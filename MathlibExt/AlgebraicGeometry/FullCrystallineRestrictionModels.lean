/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules
public import MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Explicit full-basis restriction and crystal-extension comparisons

The restriction functor precomposes by the literal nilpotent-basis
inclusion, with identity maps on all original thickening rings. Its
source and target modules are the two independently fixed local Ext
module constructions. The extension and comparison are outputs, rather
than consequences silently assumed from enlarging the site.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section3.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FullCrystallineRestrictionModels

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open PDivisibleGroupSchemes PDivisibleCartierTowerModels

variable (p : ℕ) [Fact p.Prime] (A : FullPDCrystallineTests.PDBase)
  (S : Over A.reduction)

/-- The original coefficient rings restrict by exactly the identity ring map. -/
def coefficientRestriction :
    GeometricPDCrystallineSheaves.structureRingPresheaf p A S ⋙
      forget₂ CommRingCat.{1} RingCat.{1} ⟶
    (FullPDCrystallineTests.nilpotentInclusion p A S).op ⋙
      (FullPDCrystallineSheaves.structureRingPresheaf p A S ⋙
        forget₂ CommRingCat.{1} RingCat.{1}) where
  app P := RingCat.ofHom (RingHom.id (ULift.{1} P.unop.ring))
  naturality {P Q} f := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl

/-- The actual original-basis restriction functor for full modules. -/
def restrictModules := PresheafOfModules.pushforward (coefficientRestriction p A S)

variable (R : Type) [CommRing R] (G : PDivisibleGroup (Spec (.of R)) p)
  (D : CartierDualTower p R G) (s : Spec (.of R) ⟶ A.reduction)

/-- Restrict the exact full-basis covariant Ext module. -/
def restrictedCovariantModule :=
  (restrictModules p A (Over.mk s)).obj
    (FullPDCrystallineExtModules.nativeModule p A (Over.mk s)
      (FullPDCrystallineSheaves.groupSheaf p A (Over.mk s) D.group) 1)

/-- Both crystal constructions, together with an isomorphism between the restriction of the
full-basis covariant Ext module to the nilpotent basis and the nilpotent-basis covariant Ext
module, are requested outputs. The isomorphism is not required to be a canonical restriction
map: only its existence is recorded. -/
structure ExtensionComparison where
  fullCrystal : FullPDCrystallineExtModules.CrystalRealization p A (Over.mk s)
    (FullPDCrystallineSheaves.groupSheaf p A (Over.mk s) D.group)
  nilpotentCrystal : PDivisibleCrystallineRealizations.Realization p R G D A s
  restriction : restrictedCovariantModule p A R G D s ≅
    PDivisibleCrystallineRealizations.covariantModule p R G D A s

end MathlibExt.AlgebraicGeometry.FullCrystallineRestrictionModels
