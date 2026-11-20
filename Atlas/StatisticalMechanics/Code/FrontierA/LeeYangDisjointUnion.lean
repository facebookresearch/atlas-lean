/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.LeeYangPolynomial
import Code.FrontierC.LeeYangSymmetry
import Code.Ising.FiniteVolumeSum

open scoped BigOperators
open Finset Polynomial

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

section DisjointUnion

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in


theorem minusSpinCount_isingSumConfigEquiv_symm
    (s : ConfigSpace V) (t : ConfigSpace W) :
    minusSpinCount (isingSumConfigEquiv.symm (s, t)) =
      minusSpinCount s + minusSpinCount t := by
  classical
  have hsum : minusSpinCount (isingSumConfigEquiv.symm (s, t)) =
      ∑ x : V ⊕ W,
        if isingSumConfigEquiv.symm (s, t) x = false then 1 else 0 := by
    simp [minusSpinCount]
  have hs : minusSpinCount s =
      ∑ x : V, if s x = false then 1 else 0 := by
    simp [minusSpinCount]
  have ht : minusSpinCount t =
      ∑ x : W, if t x = false then 1 else 0 := by
    simp [minusSpinCount]
  have hinl (x : V) : isingSumConfigEquiv.symm (s, t) (Sum.inl x) = s x := by
    simp [isingSumConfigEquiv]
  have hinr (x : W) : isingSumConfigEquiv.symm (s, t) (Sum.inr x) = t x := by
    simp [isingSumConfigEquiv]
  calc
    minusSpinCount (isingSumConfigEquiv.symm (s, t)) =
        ∑ x : V ⊕ W,
          if isingSumConfigEquiv.symm (s, t) x = false then 1 else 0 := hsum
    _ = (∑ x : V, if s x = false then 1 else 0) +
          ∑ x : W, if t x = false then 1 else 0 := by
      rw [Fintype.sum_sum_type]
      congr 1
    _ = minusSpinCount s + minusSpinCount t := by rw [← hs, ← ht]

omit [DecidableEq V] [DecidableEq W] in

theorem zeroFieldInteractionWeight_sum (beta : ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    zeroFieldInteractionWeight (G ⊕g H) beta
        (isingSumConfigEquiv.symm (s, t)) =
      zeroFieldInteractionWeight G beta s *
        zeroFieldInteractionWeight H beta t := by
  classical
  unfold zeroFieldInteractionWeight
  rw [sum_bond_isingSumConfigEquiv_symm G H, mul_add, Real.exp_add]



theorem leeYangPolynomial_sum (beta : ℝ) :
    leeYangPolynomial (G ⊕g H) beta =
      leeYangPolynomial G beta * leeYangPolynomial H beta := by
  unfold leeYangPolynomial
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [zeroFieldInteractionWeight_sum G H,
    minusSpinCount_isingSumConfigEquiv_symm]
  have hterm : ∀ (s : ConfigSpace V) (t : ConfigSpace W),
      C (zeroFieldInteractionWeight G beta s *
          zeroFieldInteractionWeight H beta t) *
          X ^ (minusSpinCount s + minusSpinCount t) =
        (C (zeroFieldInteractionWeight G beta s) *
            X ^ minusSpinCount s) *
          (C (zeroFieldInteractionWeight H beta t) *
            X ^ minusSpinCount t) := by
    intro s t
    rw [map_mul, pow_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]


theorem leeYangComplexPolynomial_sum (beta : ℝ) :
    leeYangComplexPolynomial (G ⊕g H) beta =
      leeYangComplexPolynomial G beta * leeYangComplexPolynomial H beta := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_sum G H]
  exact Polynomial.map_mul (algebraMap ℝ ℂ)

end DisjointUnion

section Edgeless

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in

@[simp] theorem zeroFieldInteractionWeight_bot (beta : ℝ) (s : ConfigSpace V) :
    zeroFieldInteractionWeight (⊥ : SimpleGraph V) beta s = 1 := by
  classical
  unfold zeroFieldInteractionWeight
  unfold SimpleGraph.edgeFinset
  simp [SimpleGraph.edgeSet_bot]


theorem sum_X_pow_minusSpinCount :
    (∑ s : ConfigSpace V, (X : ℝ[X]) ^ minusSpinCount s) =
      (1 + X) ^ Fintype.card V := by
  have hmonomial (s : ConfigSpace V) :
      (X : ℝ[X]) ^ minusSpinCount s =
        ∏ x : V, if s x then 1 else X := by
    symm
    calc
      (∏ x : V, if s x then (1 : ℝ[X]) else X) =
          ∏ x ∈ Finset.univ.filter (fun x => s x = false), X := by
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro x _
        cases s x <;> simp
      _ = (X : ℝ[X]) ^ minusSpinCount s := by
        rw [Finset.prod_const]
        rfl
  calc
    (∑ s : ConfigSpace V, (X : ℝ[X]) ^ minusSpinCount s) =
        ∑ s : ConfigSpace V, ∏ x : V, if s x then 1 else X := by
      apply Finset.sum_congr rfl
      intro s _
      exact hmonomial s
    _ = ∏ x : V, ∑ b : Bool, if b then (1 : ℝ[X]) else X := by
      exact (Fintype.prod_sum
        (fun (_x : V) (b : Bool) => if b then (1 : ℝ[X]) else X)).symm
    _ = ∏ _x : V, (1 + X : ℝ[X]) := by
      apply Finset.prod_congr rfl
      intro x _
      rw [Fintype.sum_bool]
      simp
    _ = (1 + X) ^ Fintype.card V := by
      rw [Finset.prod_const, Finset.card_univ]



theorem leeYangPolynomial_bot (beta : ℝ) :
    leeYangPolynomial (⊥ : SimpleGraph V) beta =
      (1 + X) ^ Fintype.card V := by
  unfold leeYangPolynomial
  simp only [zeroFieldInteractionWeight_bot, map_one, one_mul]
  exact sum_X_pow_minusSpinCount


theorem leeYangComplexPolynomial_bot (beta : ℝ) :
    leeYangComplexPolynomial (⊥ : SimpleGraph V) beta =
      (1 + X) ^ Fintype.card V := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_bot]
  simp


theorem leeYangComplexPolynomial_bot_root_eq_neg_one (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
    z = -1 := by
  rw [leeYangComplexPolynomial_bot] at hz
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X] at hz
  have hbase : (1 : ℂ) + z = 0 := eq_zero_of_pow_eq_zero hz
  linear_combination hbase


theorem leeYangComplexPolynomial_bot_root_norm (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
    ‖z‖ = 1 := by
  rw [leeYangComplexPolynomial_bot_root_eq_neg_one beta hz]
  norm_num

end Edgeless

end StatMech.FrontierA
