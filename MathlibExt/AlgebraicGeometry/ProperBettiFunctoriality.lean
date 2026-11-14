/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.CompactSupportBetti
public import MathlibExt.AlgebraicGeometry.VerdierBetti
public import MathlibExt.AlgebraicGeometry.BettiFunctoriality
public import Mathlib.CategoryTheory.Shift.Adjunction
/-!
# Proper Betti pushforward from normalized compact-support pullback

The support map is fixed pointwise by the ordinary inverse-image adjunction.
Its derived enhancement is characterized by equality with the actual right-
derived units on every bounded-below cochain complex. The coefficient-unit
comparison is fixed by the same adjunction and its derived unit. These
conditions determine the data rather than supply arbitrary cohomology maps.

Given these characterized inputs, Borel--Moore pushforward is constructed by
precomposition on compact-support duals and the two actual linear dualizing
representations. No proper-trace operator is assumed separately. The existence
of this input for proper maps is not claimed in this completed definition file.

Reference: Kashiwara--Schapira, *Sheaves on Manifolds*, §§2.5--3.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.BettiRealization
open MathlibExt.AlgebraicGeometry.CompactSupportBetti
open MathlibExt.AlgebraicGeometry.BettiFunctoriality
open MathlibExt.AlgebraicGeometry.VerdierBetti
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Actual derived inverse image on bounded-below rational complexes. -/
abbrev inverseImagePlus {Z W : TopCat.{0}} (f : Z ⟶ W) :=
  (pullback ℚ f).rightDerivedFunctorPlus
/-- Actual derived compact-support section functor with bounded-below target. -/
abbrev compactDerived (Z : TopCat.{0}) := (sections Z).rightDerivedFunctorPlus

/-- Compact support of the fixed section map, not a choice of map. -/
structure SectionSupport {Z W : TopCat.{0}} (f : Z ⟶ W) : Prop where
  compact : ∀ (F : RationalSheaf W) (s : compactSections F),
    IsCompact (closure (germSupport ((pullback ℚ f).obj F)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F).hom.app
        (op ⊤) s.1)))

/-- Pullback of a compact section is the actual adjunction-unit section. -/
def sectionPullback {Z W : TopCat.{0}} (f : Z ⟶ W) (P : SectionSupport f)
    (F : RationalSheaf W) : compactSections F →ₗ[ℚ] compactSections ((pullback ℚ f).obj F) where
  toFun s := ⟨((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F).hom.app
    (op ⊤) s.1, P.compact F s⟩
  map_add' s t := by ext; exact map_add _ _ _
  map_smul' r s := by ext; exact map_smul _ _ _

/-- Naturality follows from the actual sheaf inverse-image unit. -/
def sectionPullbackNat {Z W : TopCat.{0}} (f : Z ⟶ W) (P : SectionSupport f) :
    sections W ⟶ pullback ℚ f ⋙ sections Z where
  app F := ModuleCat.ofHom (sectionPullback f P F)
  naturality {F G} a := by
    ext s
    apply Subtype.ext
    have h := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality a
    exact congrArg (fun b => (b.hom.app (op ⊤)).hom s.1) h

abbrev rationalVectorUnit : DerivedCategory (ModuleCat.{0} ℚ) :=
  (DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) 0).obj (ModuleCat.of ℚ ℚ)
/-- Actual compact-support derived Hom into the rational coefficient unit. -/
abbrev CompactDualHom (Z : TopCat.{0}) (n : ℤ) : Type 1 :=
  (derivedSections Z).obj ((unitPlus Z)⟦n⟧) ⟶ rationalVectorUnit

/-- Shift adjunction from Borel--Moore degree to the dualizing representation. -/
def bmAdjoint (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℤ) :
    BorelMoore Z D n →ₗ[ℚ] (DerivedCategory.Plus.ι.obj ((unitPlus Z)⟦n⟧) ⟶ D.obj) where
  toFun a := (DerivedCategory.Plus.ι.commShiftIso n).hom.app (unitPlus Z) ≫
    (shiftFunctor (RationalDerived Z) n).map a ≫
      (shiftFunctorCompIsoId (RationalDerived Z) (-n) n (neg_add_cancel n)).hom.app D.obj
  map_add' a b := by
    simp [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r a := by
    simp [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- The shift-adjunction map is a rational linear equivalence. -/
def bmAdjointEquiv (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℤ) :
    BorelMoore Z D n ≃ₗ[ℚ] (DerivedCategory.Plus.ι.obj ((unitPlus Z)⟦n⟧) ⟶ D.obj) :=
  LinearEquiv.ofBijective (bmAdjoint Z D n) (by
    let A := (DerivedCategory.Plus.ι.commShiftIso n).app (unitPlus Z)
    let a := (shiftEquiv (RationalDerived Z) n).toAdjunction.homEquiv (rationalUnit Z) D.obj
    change Function.Bijective ((fun f => A.hom ≫ f) ∘ a.symm)
    apply Function.Bijective.comp _ a.symm.bijective
    constructor
    · intro a b h
      exact (cancel_epi A.hom).mp h
    · intro b
      exact ⟨A.inv ≫ b, by simp⟩)

/-- The actual dualizing representation gives the compact-support Hom equivalence. -/
def bmDualHomEquiv (Z : TopCat.{0}) (D : DualizingComplex Z) (n : ℤ) :
    BorelMoore Z D n ≃ₗ[ℚ] CompactDualHom Z n :=
  (bmAdjointEquiv Z D n).trans
    (D.representation.app (op ((unitPlus Z)⟦n⟧))).toLinearEquiv

def unitComplex (Z : TopCat.{0}) : CochainComplex.Plus (RationalSheaf Z) :=
  ⟨(CochainComplex.singleFunctor (RationalSheaf Z) 0).obj (rationalConstantSheaf Z),
    ⟨0, inferInstance⟩⟩

/-- The actual cochain constant complex has the fixed bounded-below coefficient image. -/
@[simp] theorem unitComplex_image (Z : TopCat.{0}) :
    DerivedCategory.Plus.Q.obj (unitComplex Z) = unitPlus Z := by rfl

def coefficientUnitMap {Z W : TopCat.{0}} (f : Z ⟶ W) :
    unitPlus Z ⟶ (inverseImagePlus f).obj (unitPlus W) := by
  let k : unitComplex Z ⟶ (pullback ℚ f).mapCochainComplexPlus.obj (unitComplex W) :=
    ObjectProperty.homMk
      ((CochainComplex.singleFunctor (RationalSheaf Z) 0).map
        ((constantPullbackIso f).app (ModuleCat.of ℚ ℚ)).inv ≫
        (HomologicalComplex.singleMapHomologicalComplex (pullback ℚ f)
          (ComplexShape.up ℤ) 0).inv.app (rationalConstantSheaf W))
  exact DerivedCategory.Plus.Q.map k ≫
    (pullback ℚ f).rightDerivedFunctorPlusUnit.app (unitComplex W)

/-- A derived compact-support pullback fixed by actual cochain maps and units. -/
structure ProperPullback {Z W : TopCat.{0}} (f : Z ⟶ W) where
  support : SectionSupport f
  unitIso : (inverseImagePlus f).obj (unitPlus W) ≅ unitPlus Z
  unit_normalization : unitIso.inv = coefficientUnitMap f
  map : compactDerived W ⟶ inverseImagePlus f ⋙ compactDerived Z
  compatibility : ∀ K : CochainComplex.Plus (RationalSheaf W),
    (sections W).rightDerivedFunctorPlusUnit.app K ≫ map.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((sectionPullbackNat f support).mapCochainComplexPlus.app K) ≫
        (sections Z).rightDerivedFunctorPlusUnit.app ((pullback ℚ f).mapCochainComplexPlus.obj K) ≫
        (compactDerived Z).map ((pullback ℚ f).rightDerivedFunctorPlusUnit.app K)

/-- The fixed compact-support pullback on shifted rational coefficient complexes. -/
def compactPullback {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback f) (n : ℤ) :
    (derivedSections W).obj ((unitPlus W)⟦n⟧) ⟶
      (derivedSections Z).obj ((unitPlus Z)⟦n⟧) :=
  DerivedCategory.Plus.ι.map (P.map.app ((unitPlus W)⟦n⟧) ≫
    (compactDerived Z).map
      (((inverseImagePlus f).commShiftIso n).hom.app (unitPlus W) ≫
        (shiftFunctor (DerivedCategory.Plus (RationalSheaf Z)) n).map P.unitIso.hom))

/-- Precomposition on the actual compact-support duals. -/
def compactDualPullback {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback f) (n : ℤ) :
    CompactDualHom Z n →ₗ[ℚ] CompactDualHom W n where
  toFun a := compactPullback P n ≫ a
  map_add' a b := by simp [Preadditive.comp_add]
  map_smul' r a := by simp [Linear.comp_smul]

/-- Proper Borel--Moore pushforward, constructed from normalized support data. -/
def borelMoorePushforward {Z W : TopCat.{0}} {f : Z ⟶ W} (P : ProperPullback f)
    (DX : DualizingComplex Z) (DY : DualizingComplex W) (n : ℤ) :
    BorelMoore Z DX n →ₗ[ℚ] BorelMoore W DY n :=
  (bmDualHomEquiv W DY n).symm.toLinearMap ∘ₗ
    compactDualPullback P n ∘ₗ (bmDualHomEquiv Z DX n).toLinearMap

end MathlibExt.AlgebraicGeometry.ProperBettiFunctoriality
