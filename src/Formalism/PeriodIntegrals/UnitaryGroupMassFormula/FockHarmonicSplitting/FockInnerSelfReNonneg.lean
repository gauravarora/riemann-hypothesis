module

public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle0001

@[expose] public section

noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

lemma wt_eq_nat (α : σ →₀ ℕ) : wt α = ((α.prod fun _ k => k.factorial : ℕ) : ℂ) := by
  simp [wt, Finsupp.prod]

lemma wt_pos_nat (α : σ →₀ ℕ) : 0 < (α.prod fun _ k => k.factorial : ℕ) := by
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

lemma conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α :=
  FockRaiseLowInner.wt_conj α

lemma fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α :=
  FockRaiseLowInner.fockInner_eq_sum_left P Q S hS

lemma fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α :=
  FockRaiseLowInner.fockInner_eq_sum_right P Q S hS

lemma fockInner_add_left (P P' Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P + P') Q = FockH1Action.fockInner P Q + FockH1Action.fockInner P' Q :=
  FockRaiseLowInner.fockInner_add_left P P' Q

lemma fockInner_add_right (P Q Q' : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q + Q') = FockH1Action.fockInner P Q + FockH1Action.fockInner P Q' :=
  FockRaiseLowInner.fockInner_add_right P Q Q'

lemma fockInner_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q :=
  FockRaiseLowInner.fockInner_smul_left P Q c

lemma fockInner_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q :=
  FockRaiseLowInner.fockInner_smul_right P Q c

lemma fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = - FockH1Action.fockInner P Q :=
  FockRaiseLowInner.fockInner_neg_right P Q

lemma fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (-P) Q = - FockH1Action.fockInner P Q :=
  FockRaiseLowInner.fockInner_neg_left P Q

lemma fockInner_zero_left (Q : MvPolynomial σ ℂ) : FockH1Action.fockInner 0 Q = 0 :=
  FockRaiseLowInner.fockInner_zero_left Q

lemma fockInner_zero_right (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P 0 = 0 :=
  FockRaiseLowInner.fockInner_zero_right P

lemma fockInner_conj (P Q : MvPolynomial σ ℂ) :
    (starRingEnd ℂ) (FockH1Action.fockInner Q P) = FockH1Action.fockInner P Q :=
  (FockRaiseLowInner.fockInner_swap Q P).symm

lemma fockInner_self (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P P =
    ∑ α ∈ P.support, (((Complex.normSq (AddMonoidAlgebra.coeff P α)) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_sum_left P P P.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast, wt_eq_nat]

lemma fockInner_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (FockH1Action.fockInner P P).re := by
  rw [fockInner_self, Complex.re_sum]
  refine Finset.sum_nonneg (fun α _ => ?_)
  rw [Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

lemma fockInner_self_eq_zero {P : MvPolynomial σ ℂ} (h : FockH1Action.fockInner P P = 0) : P = 0 := by
  have hre : ∑ α ∈ P.support, Complex.normSq (AddMonoidAlgebra.coeff P α) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) = 0 := by
    have h' := congrArg Complex.re h
    rw [fockInner_self, Complex.re_sum] at h'
    simpa only [Complex.ofReal_re, Complex.zero_re] using h'
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => mul_nonneg (Complex.normSq_nonneg (AddMonoidAlgebra.coeff P α)) (Nat.cast_nonneg _))).mp hre
  by_contra hP
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
  rcases mul_eq_zero.mp (hterm α hα) with h1 | h1
  · rw [Complex.normSq_eq_zero] at h1
    exact (MvPolynomial.mem_support_iff.mp hα) h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (wt_pos_nat α).ne')

lemma wt_add_single [Fintype σ] [DecidableEq σ] (β : σ →₀ ℕ) (l : σ) :
    wt (β + Finsupp.single l 1) = ((β l + 1 : ℕ) : ℂ) * wt β := by
  rw [add_comm β (Finsupp.single l 1), Nat.cast_add, Nat.cast_one]
  exact FockRaiseLowInner.wt_single_add l β

lemma fockInner_X_mul [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q) :=
  FockRaiseLowInner.fockInner_X_mul l P Q

lemma fockInner_pderiv [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (pderiv l P) Q = FockH1Action.fockInner P (X l * Q) :=
  (FockRaiseLowInner.fockInner_mul_X l P Q).symm

lemma fockInner_hc_left {n : ℕ} (P Q : MvPolynomial σ ℂ) (hQ : Q ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner (homogeneousComponent n P) Q = FockH1Action.fockInner P Q := by
  have hQ' : Q.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hQ
  rw [fockInner_eq_sum_right (homogeneousComponent n P) Q Q.support
      (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hdeg := hQ' (MvPolynomial.mem_support_iff.mp hα)
  rw [coeff_homogeneousComponent]
  split_ifs with hc
  · rfl
  · exact absurd (by
      first
      | exact hdeg
      | (rw [Finsupp.degree_eq_weight_one]; exact hdeg)) hc

lemma fockInner_hc_right {n : ℕ} (P Q : MvPolynomial σ ℂ) (hP : P ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner P (homogeneousComponent n Q) = FockH1Action.fockInner P Q := by
  rw [← fockInner_conj P (homogeneousComponent n Q), fockInner_hc_left Q P hP, fockInner_conj]

end PI.FHS
