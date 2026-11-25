/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurveSupersingular
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ModularCurve Polynomial

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

-- Consumer with the original binders, at a prime characteristic `p`.
example (N p : ℕ) [Fact p.Prime] :
    eichlerMass N p = ((p : ℚ) - 1) * (ArithmeticFunction.dedekindPsi N : ℚ) / 12 :=
  rfl

example (N p : ℕ) [Fact p.Prime] :
    ssCountFormula N p = eichlerMass N p
      + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3 :=
  ssCountFormula_eq N p

-- The count formula takes a prime characteristic: the prime power `4` is rejected.
example : True := by
  fail_if_success have := ssCountFormula 1 4
  trivial

-- The Eichler mass at level one.
example (p : ℕ) [Fact p.Prime] : eichlerMass 1 p = ((p : ℚ) - 1) / 12 :=
  eichlerMass_one p

/-! At level one the count formula gives the number of supersingular `j`-invariants listed by
`ssSetTwo`, ..., `ssSetThirteen`. -/

private theorem nuTwo_one : nuTwo 1 = 1 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_one : nuThree 1 = 1 := by rw [nuThree, Nat.card_eq_fintype_card]; decide

private theorem nuTwo_two : nuTwo 2 = 1 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_two : nuThree 2 = 0 := by rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_three : nuTwo 3 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_three : nuThree 3 = 1 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_five : nuTwo 5 = 2 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_five : nuThree 5 = 0 := by rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_seven : nuTwo 7 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_seven : nuThree 7 = 2 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_eleven : nuTwo 11 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_eleven : nuThree 11 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_thirteen : nuTwo 13 = 2 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_thirteen : nuThree 13 = 2 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

example : ssCountFormula 1 2 = ssSetTwo.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_two, nuThree_two]
  norm_num [ssSetTwo]

example : ssCountFormula 1 3 = ssSetThree.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_three, nuThree_three]
  norm_num [ssSetThree]

example : ssCountFormula 1 5 = ssSetFive.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_five, nuThree_five]
  norm_num [ssSetFive]

example : ssCountFormula 1 7 = ssSetSeven.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_seven, nuThree_seven]
  norm_num [ssSetSeven]

example : ssCountFormula 1 11 = ssSetEleven.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_eleven, nuThree_eleven,
    ssSetEleven_card]
  norm_num

example : ssCountFormula 1 13 = ssSetThirteen.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_thirteen,
    nuThree_thirteen]
  norm_num [ssSetThirteen]

/-! The automorphism weight reads the characteristic of the field, not its cardinality. -/

-- The field with four elements has characteristic `2`, so `j = 0` has weight `12` there.
open Classical in
example : autWeight (0 : GaloisField 2 2) = 12 :=
  autWeight_two_zero (ringChar.eq (GaloisField 2 2) 2)

example : autWeight (0 : ZMod 3) = 6 :=
  autWeight_three_zero (ZMod.ringChar_zmod_n 3)

example : autWeight (0 : ZMod 5) = 3 := by
  simp [autWeight, ZMod.ringChar_zmod_n]

example : autWeight (1728 : ZMod 7) = 2 := by
  simp only [autWeight, ZMod.ringChar_zmod_n]
  decide

-- Boundary: the automorphism weight drops to `1` away from `0` and `1728`.
example (j : ZMod 5) (hj0 : j ≠ 0) (hj : j ≠ 1728) : autWeight j = 1 :=
  autWeight_of_ne (by rw [ZMod.ringChar_zmod_n]; norm_num)
    (by rw [ZMod.ringChar_zmod_n]; norm_num) j hj0 hj

example : ssPolyTwo = X := ssPolyTwo_eq

example : ssSetEleven.card = 2 := ssSetEleven_card

/-! The short model is an elliptic curve with `j`-invariant `j` away from characteristics `2`
and `3`, and singular in those two characteristics. -/

example {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)] [NeZero (3 : F)] (j : F) :
    (ssModel j).IsElliptic :=
  inferInstance

example {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)] [NeZero (3 : F)] (j : F) :
    (ssModel j).j = j :=
  ssModel_j j

-- Nonsingularity at every `j` in characteristic `5`.
example : ∀ j : ZMod 5, (ssModel j).Δ ≠ 0 := by decide

-- In characteristics `2` and `3` the short model is singular at every `j`.
example : ∀ j : ZMod 2, (ssModel j).Δ = 0 := by decide

example : ∀ j : ZMod 3, (ssModel j).Δ = 0 := by decide

example {F : Type*} [Field F] [DecidableEq F] (h3 : (3 : F) = 0) (j : F) : (ssModel j).Δ = 0 :=
  ssModel_Δ_eq_zero (Or.inr h3) j

-- There Mathlib's generalized Weierstrass model `WeierstrassCurve.ofJ` is nonsingular.
example : (WeierstrassCurve.ofJ (0 : ZMod 2)).Δ ≠ 0 := by decide

example : (WeierstrassCurve.ofJ (0 : ZMod 3)).Δ ≠ 0 := by decide

/-! A supersingular elliptic curve over `ZMod p`, `p ≥ 5`, has `p + 1` points, so the model at a
listed supersingular `j` has `p` affine points; at an ordinary `j` the count differs. -/

example : affinePointCount (ssModelA (0 : ZMod 5)) (ssModelB 0) = 5 := by decide

example : affinePointCount (ssModelA (1728 : ZMod 7)) (ssModelB 1728) = 7 := by decide

example : affinePointCount (ssModelA (0 : ZMod 11)) (ssModelB 0) = 11 := by decide

example : affinePointCount (ssModelA (1728 : ZMod 11)) (ssModelB 1728) = 11 := by decide

example : affinePointCount (ssModelA (5 : ZMod 13)) (ssModelB 5) = 13 := by decide

-- `j = 1728` is ordinary in characteristic `5`.
example : affinePointCount (ssModelA (1728 : ZMod 5)) (ssModelB 1728) = 3 := by decide

/-! The supersingular locus uses geometric `p`-torsion over an algebraic closure. -/

-- Consumer for the supersingular `j` set.
example (p : ℕ) [Fact p.Prime] (j : AlgebraicClosure (ZMod p)) :
    j ∈ ssJSet p ↔ ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic],
      W.j = j → W.toAffine.IsSupersingular :=
  mem_ssJSet_iff

section Locus

open Classical

-- Membership constrains an actual curve: `WeierstrassCurve.ofJ j` has `j`-invariant `j`.
example (p : ℕ) [Fact p.Prime] (j : AlgebraicClosure (ZMod p)) (hj : j ∈ ssJSet p) :
    (WeierstrassCurve.ofJ j).toAffine.IsSupersingular :=
  mem_ssJSet_iff.mp hj _ (WeierstrassCurve.ofJ_j j)

-- `j = 0` is supersingular in characteristic `2`, as `ssSetTwo` records: `j = 0` forces
-- `a₁ = 0`, so a point with `P = -P` forces `a₃ = 0`, and then the discriminant vanishes.
example : (0 : AlgebraicClosure (ZMod 2)) ∈ ssJSet 2 := by
  refine mem_ssJSet_iff.mpr fun W _ hj => ?_
  have h2 : (2 : AlgebraicClosure (ZMod 2)) = 0 := CharTwo.two_eq_zero
  have ha₁ : W.a₁ = 0 := W.j_eq_zero_iff_of_char_two.mp hj
  intro P hP
  match P, hP with
  | .zero, _ => rfl
  | .some x y h, hP =>
    exfalso
    have hneg := eq_neg_of_add_eq_zero_left (by rwa [two_nsmul] at hP)
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hneg
    have ha₃ : W.a₃ = 0 := by
      have hy := hneg.2
      rw [WeierstrassCurve.Affine.negY, ha₁] at hy
      linear_combination hy - y * h2
    have hΔ : W.Δ = 0 := by
      rw [WeierstrassCurve.Δ_of_char_two, ha₁, ha₃]
      ring
    exact (WeierstrassCurve.IsElliptic.isUnit (W := W)).ne_zero hΔ

-- `j = 1` is not supersingular in characteristic `2`: the point `(0, 1)` of
-- `y ^ 2 + x y = x ^ 3 + 1` is a nonzero point killed by `2`.
example : (1 : AlgebraicClosure (ZMod 2)) ∉ ssJSet 2 := by
  intro h
  have h2 : (2 : AlgebraicClosure (ZMod 2)) = 0 := CharTwo.two_eq_zero
  have h1728 : (1728 : AlgebraicClosure (ZMod 2)) = 0 := by linear_combination 864 * h2
  have hW : WeierstrassCurve.ofJ (1 : AlgebraicClosure (ZMod 2)) =
      WeierstrassCurve.ofJNe0Or1728 1 :=
    WeierstrassCurve.ofJ_ne_0_ne_1728 1 one_ne_zero (by rw [h1728]; exact one_ne_zero)
  have hss := mem_ssJSet_iff.mp h (WeierstrassCurve.ofJ 1) (WeierstrassCurve.ofJ_j 1)
  have heq : (WeierstrassCurve.ofJ (1 : AlgebraicClosure (ZMod 2))).toAffine.Equation 0 1 := by
    rw [WeierstrassCurve.Affine.equation_iff, hW]
    simp only [WeierstrassCurve.ofJNe0Or1728, h1728]
    linear_combination h2
  let P : (WeierstrassCurve.ofJ (1 : AlgebraicClosure (ZMod 2))).toAffine.Point :=
    .some 0 1 (WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq)
  have hneg : -P = P := by
    simp only [P, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq,
      true_and]
    rw [WeierstrassCurve.Affine.negY, hW]
    simp only [WeierstrassCurve.ofJNe0Or1728, h1728]
    linear_combination -h2
  have hP : 2 • P = 0 := by
    rw [two_nsmul]
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel P
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ (hss P hP)

end Locus
