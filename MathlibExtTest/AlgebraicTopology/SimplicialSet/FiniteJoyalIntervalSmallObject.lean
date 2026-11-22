/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSmallObject

/-!
# Public clients for the auxiliary small object argument

The native factorization at the explicit cardinal `ℵ₀` supplies both
orthogonality conditions and its strict factorization equation. Its right
factor solves squares against the actual endpoint corners in every
dimension, including zero, without a model-category assumption.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.joyalInterval
open scoped Simplicial

universe u

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSmallObject

/-- Use the explicit countable-cardinal construction, without a separate
factorization hypothesis. -/
noncomputable def omegaFactorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    MorphismProperty.MapFactorizationData auxiliaryGenerators.rlp.llp auxiliaryGenerators.rlp f :=
  (SmallObject.functorialFactorizationData auxiliaryGenerators Cardinal.aleph0.{u}).factorizationData f

/-- The chosen construction gives actual factors and both lifting classes. -/
theorem exists_omega_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      i ≫ p = f ∧ auxiliaryGenerators.rlp.llp i ∧ auxiliaryGenerators.rlp p := by
  let d := omegaFactorization f
  exact ⟨d.Z, d.i, d.p, d.fac, d.hi, d.hp⟩

/-- Both actual endpoint corners admit strict prescribed diagonals against
the right factor of the countable-cardinal construction. -/
theorem exists_endpointCorner_lift {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) (ε : Fin 2)
    {a : pushout (SSet.boundary.{u} n).ι
      ((productPrecylinder.{u}.app (SSet.boundary.{u} n : SSet)).endpoint ε) ⟶
      (omegaFactorization f).Z}
    {b : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ Y}
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε)
      (omegaFactorization f).p b) :
    ∃ l : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ (omegaFactorization f).Z,
      productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε ≫ l = a ∧
        l ≫ (omegaFactorization f).p = b := by
  have h : HasLiftingProperty
      (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε)
      (omegaFactorization f).p :=
    (omegaFactorization f).hp _ (auxiliaryGenerators.endpointCorner_mem n ε)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalSmallObject
