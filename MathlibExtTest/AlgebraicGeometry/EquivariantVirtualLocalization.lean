/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AlgebraicMovingEulerModels
import MathlibExt.AlgebraicGeometry.EquivariantDualBundleSourceModels
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Nonreduced coefficient and physical dual-weight checks

The differential calculation uses a genuine nonzero nilpotent scheme
coefficient. The Euler sign check starts with cotangent weight minus
one and computes the leading class of its physical tangent dual.
-/

set_option autoImplicit false
@[expose] noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.EquivariantVirtualLocalization

open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicMovingEulerModels IntegralChowChernModels

def epsilon : TrivSqZeroExt ℂ ℂ := TrivSqZeroExt.inr 1

example : epsilon * epsilon = 0 := TrivSqZeroExt.inr_mul_inr ℂ (1 : ℂ) 1

example : epsilon ≠ 0 := by
  intro h
  have h' : (1 : ℂ) = 0 :=
    TrivSqZeroExt.inr_injective (R := ℂ) (by simpa [epsilon] using h)
  exact one_ne_zero h'

example :
    KaehlerDifferential.D (TrivSqZeroExt ℂ ℂ) (Polynomial (TrivSqZeroExt ℂ ℂ))
        (Polynomial.C (1+epsilon) * Polynomial.X) =
      (1+epsilon) • KaehlerDifferential.D (TrivSqZeroExt ℂ ℂ)
        (Polynomial (TrivSqZeroExt ℂ ℂ)) Polynomial.X :=
  weightOneCoordinateDifferential (TrivSqZeroExt ℂ ℂ) (1+epsilon)

/-- A cotangent character of weight minus one has tangent-dual Euler leading term plus t. -/
example (F : SchemeData) (E : DualMovingSummand F)
    (rank : E.rank=1) (cotangentWeight : E.integer.weight = -1) :
    leadingCoefficient F [E] = LaurentPolynomial.T 1 := by
  simp [leadingCoefficient, movingRank, rank, cotangentWeight]

/-- Moving weights are nonzero, so the leading Euler coefficient is a unit with
inverse `leadingInverse`. -/
example (F : SchemeData) (E : List (DualMovingSummand F)) :
    leadingCoefficient F E * leadingInverse F E = 1 := by
  have hp : (E.map (fun e => (-e.integer.weight : ℚ) ^ e.rank)).prod ≠ 0 := by
    apply List.prod_ne_zero
    simp only [List.mem_map, not_exists, not_and]
    intro e _ h
    exact pow_ne_zero _ (neg_ne_zero.2 (Int.cast_ne_zero.2 e.moving)) h
  simp only [leadingCoefficient, leadingInverse]
  rw [mul_mul_mul_comm, ← map_mul, mul_inv_cancel₀ hp, map_one, one_mul,
    ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The weighted Euler cap of a summand has the dual weight of the original
character: a cotangent character of weight `-1` contributes `+t`. -/
example (F : SchemeData) (E : DualMovingSummand F) :
    dualEuler F E = weightedEuler F E.chern (-E.integer.weight) := rfl

section DualBundleSections

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open MathlibExt.AlgebraicGeometry.EquivariantDualBundleSourceModels
open MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
open MathlibExt.AlgebraicGeometry.LinearizedLineBundles
open MathlibExt.AlgebraicGeometry.GlobalPOTVirtualClass
open MathlibExt.AlgebraicGeometry.AlgebraicEquivariantChowModels
open MathlibExt.AlgebraicGeometry.EquivariantCharacterLineModels
open AlgebraicGeometry.StackCycleGeometry AlgebraicGeometry.StackAffineModules
open AlgebraicGeometry.StackVectorBundles

/-- The inverse virtual Euler class is `e(E^{-1}_mov) / e(E^0_mov)`: the Euler class of the moving
part of the negative (obstruction) term times the inverse Euler class of the moving part of the
degree-zero (tangent) term, not the reverse. -/
example {X : Over base} [ModObj Gm X]
    {P : DerivedTwoTermObstructionModels.EquivariantObstructionTerms X} (F : SchemeData)
    {i : F.scheme ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint Gm X i}
    {W : DerivedTwoTermObstructionModels.FixedTerms P i hi} (N : VirtualNormalData F P W) (d : ℕ) :
    inverseVirtualEuler F N d =
      movingEuler F (decompositionSummands F N.negative) *
        inverseMovingEuler F (decompositionSummands F N.zero) d := rfl


/-- Regression for the prescribed base arrow: the section lift of a quotient dual bundle uses the
arrow `a ⟶ M.map b` given by the comparison counit and `overBase` for its base, and that arrow's
torsor map followed by the fibre comparison of `M` for its torsor isomorphism. -/
example {X : Over base} [ModObj Gm X] {E : X.left.Modules} (L : Linearization Gm X E) {r : ℕ}
    (B : DualBundleModel X E r) [ModObj Gm B.total]
    (hp : γ[Gm,B.total] ≫ B.projection = (Gm ◁ B.projection) ≫ γ[Gm,X])
    (Q : EquivariantSource X) (R : EquivariantSource B.total) (M : EquivariantMap R Q B.projection hp)
    (P : QuotientDualBundle L B hp Q R M) (a : AffinePoint Q.quotient.stack)
    (s : P.module.val.presheaf.obj (Opposite.op a)) :
    let e := Opposite.op ((sectionPresheaf P.module.val).elementsMk (Opposite.op a) s)
    let b := P.comparison.inverse.obj e
    let φ : a ⟶ (affineMap M.map).obj b :=
      ((sectionForget P.module.val).mapIso (P.comparison.counitIso.app e)).inv ≫
        (P.overBase.app b).hom
    (P.sectionNormalization a s).baseIso.hom = φ.hom.base ∧
      (P.sectionNormalization a s).torsorIso.hom =
        torsorMap Q φ ≫ ((M.fibre b.obj.base).hom.app b.obj.fiber).iso.hom :=
  P.sectionArrow a s

end DualBundleSections

end MathlibExtTest.AlgebraicGeometry.EquivariantVirtualLocalization
