/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import MathlibExt.HomologicalAlgebra.InjectiveSingleHom
public import MathlibExt.HomologicalAlgebra.RightDerivedCohomology
public import MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Derived-Hom and classical compact-support cohomology

The comparison is assembled from the actual represented compact-support
Hom, the injectivity of the rational coefficient module, the canonical
shift comparison, and the actual classical/Plus right-derived comparison.
There is no additional geometric hypothesis or supplied comparison map.

The two imported homological-algebra helpers retain the exact Axiom
source paths, revision, Apache 2.0 notice and modification notice for the
completed producer proofs.
-/

namespace MathlibExt.AlgebraicGeometry.CompactSupportComparison

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.VerdierBetti
open MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open MathlibExt.HomologicalAlgebra.RightDerivedCohomology
open MathlibExt.HomologicalAlgebra.InjectiveSingleHom.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- The actual rational coefficient object is injective. -/
instance rationalCoefficientInjective : Injective (ModuleCat.of ℚ ℚ) := by
  have : Module.Injective ℚ ℚ := Module.injective_of_isSemisimpleRing ℚ ℚ
  exact Module.injective_object_of_injective_module ℚ ℚ

/-- H⁰ of the shifted actual compact-support complex is classical Hⁿ_c. -/
def compactCohomologyIso (Z : TopCat.{0}) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) 0).obj
      ((derivedSections Z).obj ((unitPlus Z)⟦(n : ℤ)⟧)) ≅
      Cohomology Z n := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) 0
  let Y := (derivedSections Z).obj (unitPlus Z)
  have : (derivedSections Z).CommShift ℤ := by
    dsimp [derivedSections]
    infer_instance
  let a : H.obj ((derivedSections Z).obj ((unitPlus Z)⟦(n : ℤ)⟧)) ≅
      H.obj (Y⟦(n : ℤ)⟧) :=
    H.mapIso (((derivedSections Z).commShiftIso (n : ℤ)).app (unitPlus Z))
  let b : H.obj (Y⟦(n : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) (n : ℤ)).obj Y :=
    (H.isoShift (n : ℤ)).app Y ≪≫
      (eqToIso (DerivedCategory.shift_homologyFunctor (ModuleCat.{0} ℚ) (n : ℤ))).app Y
  let c : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) (n : ℤ)).obj Y ≅
      Cohomology Z n := derivedCohomologyIso (sections Z) (rationalConstantSheaf Z) n
  exact a ≪≫ b ≪≫ c

/-- The compact-support Hom group is the actual rational dual of its
classical cohomology group, with the scalar action retained. -/
def compactDualHomEquiv (Z : TopCat.{0}) (n : ℕ) :
    CompactDualHom Z (n : ℤ) ≃ₗ[ℚ] DualCohomology Z n := by
  let Y := (derivedSections Z).obj ((unitPlus Z)⟦(n : ℤ)⟧)
  let e := homToInjectiveSingleLinearEquiv ℚ Y (ModuleCat.of ℚ ℚ) 0
  let a := ModuleCat.homLinearEquiv (R := ℚ) (S := ℚ)
    (M := (DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) 0).obj Y)
    (N := ModuleCat.of ℚ ℚ)
  let b : Module.Dual ℚ ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) 0).obj Y) ≃ₗ[ℚ]
      DualCohomology Z n :=
    LinearEquiv.arrowCongr (compactCohomologyIso Z n).toLinearEquiv (LinearEquiv.refl ℚ ℚ)
  exact e.trans (a.trans b)

/-- The already-characterized dualizing object gives the desired
Borel--Moore/classical compact-support dual equivalence. -/
def derivedHomCompactSupportComparison (Z : TopCat.{0})
    (D : DualizingComplex Z) (n : ℕ) :
    BorelMoore Z D (n : ℤ) ≃ₗ[ℚ] DualCohomology Z n :=
  (bmDualHomEquiv Z D (n : ℤ)).trans (compactDualHomEquiv Z n)

end MathlibExt.AlgebraicGeometry.CompactSupportComparison

