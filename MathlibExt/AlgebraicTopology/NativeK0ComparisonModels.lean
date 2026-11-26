/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSZeroFoldModels
public import MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
public import MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Actual object-sphere and object-circle maps and the K0 group comparison

The spectrum is the original native S-construction assembly. Every
object gives its actual free-zero sphere map through the native level
zero adjunction. Its circle is the original zero-fold object map followed
by the full S insertion. The sphere action relates these two maps.

The target group carrier is the literal Hom from the native free-zero
sphere in the formal localization of actual Tau Ceti spectra at the
stable weak maps fixed by the original spectrum infinity source. Its
additive structure comes from that same stable homotopy category.
The Grothendieck quotient and its actual equivalence/cofiber relations
are defined independently. Relation descent and bijectivity are separate
Wanted proofs; neither group nor K is defined by this comparison.

Sources: Waldhausen Section1.3; BGT1001.2282v4 Definition7.5 and
Sections7--9; Hovey--Shipley--Smith Sections2.2/3.1. Native free spectrum,
Hom, localization and source S operators retain their pins and licenses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeK0ComparisonModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open StableInfinityCategoryModels StableInfinityGrothendieckGroups
open StableInfinityKSpectra NativeSZeroFoldModels StableInfinityIntervalInsertion
open StableSpectraInfinitySource NativeDerivedSpectrumModels NativeSpectrumConeSources
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The actual source sphere is the native free-zero spectrum of the pointed tensor unit. -/
abbrev sourceSphere : SymmetricSpectrum := (SymmetricSpectrum.free 0).obj (𝟙_ PointedSSet.{0})

/-- The source stable weak maps are fixed in the entire original spectrum localization. -/
def stableWeak (S : SpectrumInfinitySource) : MorphismProperty SymmetricSpectrum :=
  fun _ _ f => IsStableWeak S f

/-- The actual formal stable homotopy category of the original native spectrum carrier. -/
abbrev spectrumHo (S : SpectrumInfinitySource) := (stableWeak S).Localization

abbrev spectrumQ (S : SpectrumInfinitySource) : SymmetricSpectrum ⥤ spectrumHo S := (stableWeak S).Q

/-- The actual point-set zero map retains the fixed native zero-spectrum operators. -/
def spectrumZeroMap {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (E F : SymmetricSpectrum) : E ⟶ F := toZeroSpectrum Z E ≫ initialSpectrumMap F

/-- Stable additivity is a construction of the same literal native localized category. -/
structure SpectrumGroupSource (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S) where
  preadditive : Preadditive (spectrumHo S)
  biproducts : letI := preadditive; HasFiniteBiproducts (spectrumHo S)
  zero_normalization : letI := preadditive
    ∀ E F : SymmetricSpectrum,
    (0 : (spectrumQ S).obj E ⟶ (spectrumQ S).obj F) = (spectrumQ S).map (spectrumZeroMap Z E F)

variable {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S} (G : SpectrumGroupSource S Z)

/-- Pi0 of a native spectrum is this actual stable sphere Hom carrier. -/
def spectrumPi0 (_G : SpectrumGroupSource S Z) (E : SymmetricSpectrum) : Type 1 :=
  (spectrumQ S).obj sourceSphere ⟶ (spectrumQ S).obj E

instance spectrumPi0Group (E : SymmetricSpectrum) : AddCommGroup (spectrumPi0 G E) := by
  letI := G.preadditive
  change AddCommGroup ((spectrumQ S).obj sourceSphere ⟶ (spectrumQ S).obj E)
  infer_instance

/-- Every original spectrum map induces its actual stable sphere-Hom group map. -/
def spectrumPi0Map {E F : SymmetricSpectrum} (f : E ⟶ F) : spectrumPi0 G E →+ spectrumPi0 G F := by
  letI := G.preadditive
  exact
    { toFun := fun a => a ≫ (spectrumQ S).map f
      map_zero' := by change (0 : (spectrumQ S).obj sourceSphere ⟶ (spectrumQ S).obj E) ≫ _ = 0; simp
      map_add' := by
        intro a b
        change (a + b : (spectrumQ S).obj sourceSphere ⟶ (spectrumQ S).obj E) ≫
          (spectrumQ S).map f = a ≫ (spectrumQ S).map f + b ≫ (spectrumQ S).map f
        exact Preadditive.add_comp (C := spectrumHo S) _ _ _ a b ((spectrumQ S).map f) }

variable (K : ConnectiveKConstruction) (C : StableInfinityCategory.{0})

/-- The original object is placed in K level zero by its fixed native zero-fold diagram. -/
def objectLevelZero (x : C.toSSet _⦋0⦌) : 𝟙_ PointedSSet.{0} ⟶ level (connectiveK K C) 0 :=
  pointedUnitMap (pointedDiagonal (K.insertion C).pointing 0) (zeroFoldVertex C x) ≫
    (K.assembly C).comparison 0

/-- The actual free-spectrum adjunction extends that same object generator. -/
def objectSphereMap (x : C.toSSet _⦋0⦌) : sourceSphere ⟶ connectiveK K C :=
  SymmetricSpectrum.freeDesc (connectiveK K C) (objectLevelZero K C x)

/-- Its original circle is the actual full S insertion, with the original assembly comparison. -/
def objectCircle (x : C.toSSet _⦋0⦌) : PointedSSet.circle ⟶ level (connectiveK K C) 1 :=
  objectCircleMap (K.insertion C) x ≫ (K.assembly C).comparison 1

/-- The circle obtained by the original spectrum sphere action on that exact object generator. -/
def spectrumObjectCircle (x : C.toSSet _⦋0⦌) : PointedSSet.circle ⟶ level (connectiveK K C) 1 :=
  (ρ_ PointedSSet.circle).inv ≫ PointedSSet.circle ◁ objectLevelZero K C x ≫
    (connectiveK K C).smashPowStructureMap 0

/-- The actual K0 class is the native localized object-sphere map. -/
def nativeObjectClass (x : C.toSSet _⦋0⦌) : spectrumPi0 G (connectiveK K C) :=
  (spectrumQ S).map (objectSphereMap K C x)

/-- The free group map uses precisely those independently fixed native object maps. -/
def objectCycleMap : ObjectCycles C →+ spectrumPi0 G (connectiveK K C) :=
  FreeAbelianGroup.lift (nativeObjectClass G K C)

/-- The relation-descent proof concerns this actual source map and the independently defined subgroup. -/
def K0RelationDescent : Prop := relations C ≤ (objectCycleMap G K C).ker

/-- The actual K0 comparison is native quotient descent of the original object-sphere map. -/
def k0Comparison (h : K0RelationDescent G K C) :
    GrothendieckGroup C →+ spectrumPi0 G (connectiveK K C) :=
  QuotientAddGroup.lift (relations C) (objectCycleMap G K C) h

/-- The comparison sends the class of an object to its native object class. -/
theorem k0Comparison_objectClass (h : K0RelationDescent G K C) (x : C.toSSet _⦋0⦌) :
    k0Comparison G K C h (objectClass C x) = nativeObjectClass G K C x := by
  rw [k0Comparison, objectClass, QuotientAddGroup.lift_mk, objectCycleMap,
    FreeAbelianGroup.lift_apply_of]

end MathlibExt.AlgebraicTopology.NativeK0ComparisonModels
