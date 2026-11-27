/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalCoefficientFamilyUnit

/-!
# Tests for the classical coefficient family unit

Identity coefficient family maps are isomorphisms by the native derived unit.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalCoefficientFamilyUnit

private theorem isIso_of_heq (C : Type*) [Category C]
    (X Y X' Y' : C) (hX : X = X') (hY : Y = Y')
    (a : X ⟶ Y) (b : X' ⟶ Y') [IsIso b] (h : HEq a b) : IsIso a := by
  subst X' Y'
  rw [eq_of_heq h]
  infer_instance

/-- Identity coefficient family maps are isomorphisms. -/
public theorem identity_isIso (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L) (D : CoefficientMapSystem Z)
    (C : EtalePushforwardCoherence L) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    IsIso (coefficientFamilyMap D (𝟙 A) E) := by
  apply isIso_of_heq (EtaleDerived O (Spec (ordinaryRing A))) _ _ _ _ _ _ _
    ((etaleDerivedId C (Spec (ordinaryRing A))).hom.app
      (vertexEtaleDerived r P A (Z.module A) (Z.etale A) E))
    (classical_coefficient_family_unit k N S R r P O L Z D C A E)
  · change (etaleDerivedPullback (L.derived
      (Spec.map (CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom)))).obj _ = _
    change (etaleDerivedPullback (L.derived (Spec.map (𝟙 (ordinaryRing A))))).obj _ = _
    rw [Spec.map_id]
    rfl
  · change vertexEtaleDerived r P A (Z.module A) (Z.etale A)
      (((underivedModuliFunctor R P).map (𝟙 A)).app (op ⦋0⦌) E) = _
    rw [(underivedModuliFunctor R P).map_id]
    rfl

end MathlibExtTest.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalCoefficientFamilyUnit
