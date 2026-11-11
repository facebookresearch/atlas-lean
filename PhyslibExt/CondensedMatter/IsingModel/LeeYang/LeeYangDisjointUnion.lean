/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial
public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSymmetry
public import PhyslibExt.CondensedMatter.IsingModel.FiniteVolumeSum

/-!
# The Lee–Yang polynomial of disjoint unions and edgeless graphs

The Lee–Yang polynomial is multiplicative under disjoint union, and equals `(1 + X)^|V|` for the
edgeless graph.

## i. Overview

The configuration space of a disjoint union `G ⊕g H` is the product of the configuration spaces,
and both the interaction weight and the number of minus spins split accordingly, so the
Lee–Yang polynomial of `G ⊕g H` is the product of those of `G` and `H`. For the edgeless graph
the polynomial is `(1 + X)^|V|`, whose only root is `-1`; this is the base case of the circle
theorem for graphs without edges.

## ii. Key results

- `leeYangPolynomial_sum` : `P_{G ⊕g H} = P_G · P_H`.
- `leeYangPolynomial_bot` : `P_⊥ = (1 + X)^|V|`.
- `leeYangComplexPolynomial_bot_root_norm` : every root for the edgeless graph has modulus one.

## iii. Table of contents

- A. Disjoint unions
- B. The edgeless graph

## iv. References

- T. D. Lee and C. N. Yang, *Statistical theory of equations of state and phase transitions. II.
  Lattice gas and Ising model*, Phys. Rev. 87 (1952) 410–419.
-/

@[expose] public section

open scoped BigOperators
open Finset Polynomial

namespace StatMech.LeeYang

open StatMech.Ising StatMech.LeeYang

section DisjointUnion

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-! ## A. Disjoint unions -/

omit [DecidableEq V] [DecidableEq W] in
lemma minusSpinCount_isingSumConfigEquiv_symm
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
lemma zeroFieldInteractionWeight_sum (beta : ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    zeroFieldInteractionWeight (G ⊕g H) beta
        (isingSumConfigEquiv.symm (s, t)) =
      zeroFieldInteractionWeight G beta s *
        zeroFieldInteractionWeight H beta t := by
  classical
  unfold zeroFieldInteractionWeight
  rw [sum_bond_isingSumConfigEquiv_symm G H, mul_add, Real.exp_add]

lemma leeYangPolynomial_sum (beta : ℝ) :
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

lemma leeYangComplexPolynomial_sum (beta : ℝ) :
    leeYangComplexPolynomial (G ⊕g H) beta =
      leeYangComplexPolynomial G beta * leeYangComplexPolynomial H beta := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_sum G H]
  exact Polynomial.map_mul (algebraMap ℝ ℂ)

end DisjointUnion

section Edgeless

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## B. The edgeless graph -/

omit [DecidableEq V] in
@[simp] lemma zeroFieldInteractionWeight_bot (beta : ℝ) (s : ConfigSpace V) :
    zeroFieldInteractionWeight (⊥ : SimpleGraph V) beta s = 1 := by
  classical
  unfold zeroFieldInteractionWeight
  unfold SimpleGraph.edgeFinset
  simp [SimpleGraph.edgeSet_bot]

lemma sum_X_pow_minusSpinCount :
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

lemma leeYangPolynomial_bot (beta : ℝ) :
    leeYangPolynomial (⊥ : SimpleGraph V) beta =
      (1 + X) ^ Fintype.card V := by
  unfold leeYangPolynomial
  simp only [zeroFieldInteractionWeight_bot, map_one, one_mul]
  exact sum_X_pow_minusSpinCount

lemma leeYangComplexPolynomial_bot (beta : ℝ) :
    leeYangComplexPolynomial (⊥ : SimpleGraph V) beta =
      (1 + X) ^ Fintype.card V := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_bot]
  simp

lemma leeYangComplexPolynomial_bot_root_eq_neg_one (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
    z = -1 := by
  rw [leeYangComplexPolynomial_bot] at hz
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X] at hz
  have hbase : (1 : ℂ) + z = 0 := eq_zero_of_pow_eq_zero hz
  linear_combination hbase

lemma leeYangComplexPolynomial_bot_root_norm (beta : ℝ) {z : ℂ}
    (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
    ‖z‖ = 1 := by
  rw [leeYangComplexPolynomial_bot_root_eq_neg_one beta hz]
  norm_num

end Edgeless

end StatMech.LeeYang
