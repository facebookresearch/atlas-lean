/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.KLocalHomotopy
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalReplacement
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Original K local replacement and native level homotopy tests

The same original κ/B K-data is applied to the original toZeroArrow functor.
Its actual K-local outputs, all Z/i/p/Arrow maps and relative cells are retained.
Cofibrant input gives the original native Ho Hom universal property. Composing
with the SAME original I-data cofibrant replacement provides the actual
all-object homotopy comparison and detects these K-local Hom tests by level
weakness of the chosen replacement map. Native Omega identification and stable
model recognition remain separate required joins.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableK

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  generators_isCardinalForSmallObjectArgument

/-- Hom tests against exactly the actual constructed K-local objects. -/
abbrev localTestEquivalences : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.localTestEquivalences.{u, v} (B := B) StabilizationKAdapter.family

/-- The complete original local-test class is the same general family predicate. -/
theorem localTestEquivalences_eq_native : localTestEquivalences.{u, v} =
    NativeK.localTestEquivalences.{u, v} (B := B) StabilizationKAdapter.family :=
  rfl

/-- The old full K-local target tests are the shared predicate, with only K-class transport. -/
theorem localTestEquivalences_iff_liftingTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    localTestEquivalences f ↔
      ∀ Z : PointedCGWH.SequentialSpectrum.{u, v}, generators.rlp (toZero Z) →
        Function.Bijective
          (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
              (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
            (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) := by
  rw [localTestEquivalences, NativeK.localTestEquivalences,
    NativeK.omegaTests_eq_lifting_tests, StabilizationKAdapter.generators_eq]

/-- The entire class is the intersection of the original targetwise Hom isomorphism tests. -/
theorem localTestEquivalences_eq_iInf_isomorphisms :
    localTestEquivalences.{u, v} =
      ⨅ Z : {Z : PointedCGWH.SequentialSpectrum.{u, v} // generators.rlp (toZero Z)},
        ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
          ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).op ⋙
            yoneda.obj
              ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z.1))).unop :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localTestEquivalences_eq_iInf_isomorphisms.{u, v} (B := B) StabilizationKAdapter.family

/-- Identity arrows satisfy the same literal local tests. -/
theorem localTestEquivalences.containsIdentities :
    localTestEquivalences.{u, v}.ContainsIdentities :=
  NativeK.localTestEquivalences.containsIdentities.{u, v} (B := B) StabilizationKAdapter.family

/-- All three composition and cancellation directions hold for the whole local test class. -/
theorem localTestEquivalences.hasTwoOutOfThreeProperty :
    localTestEquivalences.{u, v}.HasTwoOutOfThreeProperty :=
  NativeK.localTestEquivalences.hasTwoOutOfThreeProperty.{u, v} (B := B)
    StabilizationKAdapter.family

/-- Whole Arrow retracts preserve every original local Hom test. -/
theorem localTestEquivalences.isStableUnderRetracts :
    localTestEquivalences.{u, v}.IsStableUnderRetracts :=
  NativeK.localTestEquivalences.isStableUnderRetracts.{u, v} (B := B) StabilizationKAdapter.family

/-- Original native level weak equivalences satisfy all constructed local tests. -/
theorem levelWeak_le_localTestEquivalences :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ≤ localTestEquivalences :=
  NativeK.levelWeak_le_localTestEquivalences.{u, v} (B := B) StabilizationKAdapter.family

/-- Between the actual constructed local objects the tests detect the native level weak class. -/
theorem localTestEquivalences_iff_levelWeak_of_local
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : generators.rlp (toZero X)) (hY : generators.rlp (toZero Y)) :
    localTestEquivalences f ↔ weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localTestEquivalences_iff_levelWeak_of_local.{u, v} (B := B)
      StabilizationKAdapter.family f
      (by simpa only [StabilizationKAdapter.generators_eq] using hX)
      (by simpa only [StabilizationKAdapter.generators_eq] using hY)

/-- Every original K-left arrow with genuinely cofibrant source satisfies those same Ho tests. -/
theorem left_localTestEquivalence_of_cofibrant
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : generators.rlp.llp f) [IsCofibrant X] : localTestEquivalences f :=
  NativeK.left_localTestEquivalence_of_cofibrant.{u, v} (B := B) StabilizationKAdapter.family f
    (by simpa only [StabilizationKAdapter.generators_eq] using hf)

/-- The genuine original K middle-object functor on the same original zero arrows. -/
abbrev localReplacement : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.localReplacement.{u, v} (B := B) StabilizationKAdapter.family

/-- The full original chosen sequential replacement functor is the shared family value. -/
theorem localReplacement_eq_native : localReplacement.{u, v} =
    NativeK.localReplacement.{u, v} (B := B) StabilizationKAdapter.family :=
  rfl

/-- The original K injection supplies the entire genuine native replacement unit. -/
abbrev localReplacementUnit : 𝟭 PointedCGWH.SequentialSpectrum.{u, v} ⟶ localReplacement :=
  NativeK.localReplacementUnit.{u, v} (B := B) StabilizationKAdapter.family

/-- The entire original local replacement unit keeps the same shared K injection. -/
theorem localReplacementUnit_eq_native :
    HEq localReplacementUnit.{u, v}
      (NativeK.localReplacementUnit.{u, v} (B := B) StabilizationKAdapter.family) :=
  HEq.rfl

/-- The actual original K projection gives the full chosen map to the same original zero. -/
abbrev localReplacementProjection : localReplacement.{u, v} ⟶
    (Functor.const PointedCGWH.SequentialSpectrum.{u, v}).obj (zeroDiagram (A :=
      CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v})) :=
  NativeK.localReplacementProjection.{u, v} (B := B) StabilizationKAdapter.family

/-- The whole original projection to the same zero diagram is the shared K projection. -/
theorem localReplacementProjection_eq_native :
    HEq localReplacementProjection.{u, v}
      (NativeK.localReplacementProjection.{u, v} (B := B) StabilizationKAdapter.family) :=
  HEq.rfl

/-- The whole replacement functor is the literal original κ small-object Z composition. -/
theorem localReplacement_eq_original : localReplacement.{u, v} =
    toZeroArrow ⋙ (SmallObject.functorialFactorizationData
      generators realizedGeneratorCardinal.{v}).Z :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacement_eq_original.{u, v} (B := B) StabilizationKAdapter.family

/-- Every actual object remains the original selected κ iteration. -/
theorem localReplacement_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localReplacement.obj X = SmallObject.obj generators realizedGeneratorCardinal.{v} (toZero X) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacement_obj.{u, v} (B := B) StabilizationKAdapter.family X

/-- Every whole map is the original κ map on the same full zero Arrow square. -/
theorem localReplacement_map {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    localReplacement.map f = SmallObject.objMap generators realizedGeneratorCardinal.{v}
      (toZeroArrow.map f) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacement_map.{u, v} (B := B) StabilizationKAdapter.family f

/-- The actual replacement unit is the literal original chosen K injection. -/
theorem localReplacementUnit_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localReplacementUnit.app X = SmallObject.ιObj generators realizedGeneratorCardinal.{v}
      (toZero X) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacementUnit_app.{u, v} (B := B) StabilizationKAdapter.family X

/-- The actual replacement projection is the literal original chosen K projection. -/
theorem localReplacementProjection_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localReplacementProjection.app X = SmallObject.πObj generators realizedGeneratorCardinal.{v}
      (toZero X) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacementProjection_app.{u, v} (B := B) StabilizationKAdapter.family X

/-- The complete original maps retain the same original object-to-zero factorization. -/
theorem localReplacement_fac (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localReplacementUnit.app X ≫ localReplacementProjection.app X = toZero X :=
  NativeK.localReplacement_fac.{u, v} (B := B) StabilizationKAdapter.family X

/-- Both original functorial sides occur in every actual unit naturality square. -/
theorem localReplacementUnit_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) :
    localReplacementUnit.app X ≫ localReplacement.map f = f ≫ localReplacementUnit.app Y :=
  NativeK.localReplacementUnit_naturality.{u, v} (B := B) StabilizationKAdapter.family f

/-- The original projection retains complete naturality with every replacement map. -/
theorem localReplacementProjection_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) :
    localReplacement.map f ≫ localReplacementProjection.app Y = localReplacementProjection.app X :=
  NativeK.localReplacementProjection_naturality.{u, v} (B := B) StabilizationKAdapter.family f

/-- The original selected projection is the actual unique map into the original native zero. -/
theorem localReplacementProjection_eq_toZero (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    localReplacementProjection.app X = toZero (localReplacement.obj X) :=
  NativeK.localReplacementProjection_eq_toZero.{u, v} (B := B) StabilizationKAdapter.family X

/-- The literal original replacement projection satisfies all original K lifting. -/
theorem localReplacementProjection_mem_right (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp (localReplacementProjection.app X) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacementProjection_mem_right.{u, v} (B := B) StabilizationKAdapter.family X

/-- The actual original K output has the literal original local right lifting. -/
theorem localReplacement_isLocal (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp (toZero (localReplacement.obj X)) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacement_isLocal.{u, v} (B := B) StabilizationKAdapter.family X

/-- The same output is fibrant in the actual native level model. -/
theorem localReplacement_isFibrant (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsFibrant (localReplacement.obj X) :=
  NativeK.localReplacement_isFibrant.{u, v} (B := B) StabilizationKAdapter.family X

/-- The exact same original unit is a relative K-cell complex at the same original κ/B. -/
abbrev localReplacementUnitCells (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => generators.homFamily)
      (localReplacementUnit.app X) :=
  by
  rw [← StabilizationKAdapter.generators_eq]
  exact NativeK.localReplacementUnitCells.{u, v} (B := B) StabilizationKAdapter.family X

/-- The actual original unit belongs to the full generated K-left class. -/
theorem localReplacementUnit_mem_left (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp.llp (localReplacementUnit.app X) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.localReplacementUnit_mem_left.{u, v} (B := B) StabilizationKAdapter.family X

/-- The same original unit is an actual native projective cofibration. -/
theorem localReplacementUnit_cofibration (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    cofibrations PointedCGWH.SequentialSpectrum.{u, v} (localReplacementUnit.app X) :=
  NativeK.localReplacementUnit_cofibration.{u, v} (B := B) StabilizationKAdapter.family X

/-- On genuinely cofibrant input the actual original native K-local output stays cofibrant. -/
theorem localReplacement_isCofibrant (X : PointedCGWH.SequentialSpectrum.{u, v}) [IsCofibrant X] :
    IsCofibrant (localReplacement.obj X) :=
  NativeK.localReplacement_isCofibrant.{u, v} (B := B) StabilizationKAdapter.family X

/-- The literal original local replacement unit is a Hom-test equivalence on cofibrant input. -/
theorem localReplacementUnit_localTestEquivalence
    (X : PointedCGWH.SequentialSpectrum.{u, v}) [IsCofibrant X] :
    localTestEquivalences (localReplacementUnit.app X) :=
  NativeK.localReplacementUnit_localTestEquivalence.{u, v} (B := B) StabilizationKAdapter.family X

/-- The same original I-data Q does not change any original local test. -/
theorem cofibrantReplacement_map_localTest_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    localTestEquivalences
      ((Replacement.cofibrantReplacement
        (B := B)).map f) ↔ localTestEquivalences f :=
  NativeK.cofibrantReplacement_map_localTest_iff.{u, v} (B := B) StabilizationKAdapter.family f

/-- On two cofibrant inputs the SAME original K map preserves and reflects every local test. -/
theorem localReplacement_map_localTest_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] :
    localTestEquivalences (localReplacement.map f) ↔ localTestEquivalences f :=
  NativeK.localReplacement_map_localTest_iff.{u, v} (B := B) StabilizationKAdapter.family f

/-- The all-object chosen replacement uses the SAME original I-Q followed by original K-Z. -/
abbrev cofibrantLocalReplacement : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.cofibrantLocalReplacement.{u, v} (B := B) StabilizationKAdapter.family

/-- The whole original I-Q then K-Z functor is the shared all-object replacement. -/
theorem cofibrantLocalReplacement_eq_native : cofibrantLocalReplacement.{u, v} =
    NativeK.cofibrantLocalReplacement.{u, v} (B := B) StabilizationKAdapter.family :=
  rfl

/-- Its exact output has actual K-local lifting, without an Omega or model dictionary. -/
theorem cofibrantLocalReplacement_isLocal (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    generators.rlp (toZero (cofibrantLocalReplacement.obj X)) :=
  by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.cofibrantLocalReplacement_isLocal.{u, v} (B := B) StabilizationKAdapter.family X

/-- The same original I and K cofibrations make every chosen output cofibrant. -/
theorem cofibrantLocalReplacement_isCofibrant (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsCofibrant (cofibrantLocalReplacement.obj X) :=
  NativeK.cofibrantLocalReplacement_isCofibrant.{u, v} (B := B) StabilizationKAdapter.family X

/-- Level weakness of the full original chosen replacement map detects exactly
the local Hom tests. -/
theorem cofibrantLocalReplacement_map_weak_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (cofibrantLocalReplacement.map f) ↔
      localTestEquivalences f :=
  NativeK.cofibrantLocalReplacement_map_weak_iff.{u, v} (B := B) StabilizationKAdapter.family f

/-- Consequently this actual all-object chosen functor preserves original native level weakness. -/
theorem cofibrantLocalReplacement_map_weak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (cofibrantLocalReplacement.map f) :=
  NativeK.cofibrantLocalReplacement_map_weak.{u, v} (B := B) StabilizationKAdapter.family f hf

/-- The actual all-object Ho comparison keeps original Q's projection inverse
and original K's unit. -/
abbrev cofibrantLocalComparison :
    toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v} ⟶
      cofibrantLocalReplacement ⋙ toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v} :=
  NativeK.cofibrantLocalComparison.{u, v} (B := B) StabilizationKAdapter.family

/-- Every actual comparison component retains BOTH given original chosen maps. -/
theorem cofibrantLocalComparison_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    cofibrantLocalComparison.app X =
      (Replacement.cofibrantReplacementProjectionIso
        (B := B)).inv.app X ≫
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
        (localReplacementUnit.app
          ((Replacement.cofibrantReplacement
            (B := B)).obj X)) :=
  NativeK.cofibrantLocalComparison_app.{u, v} (B := B) StabilizationKAdapter.family X

/-- Precomposition by the actual all-object comparison is bijective at every K-local target. -/
theorem cofibrantLocalComparison_precomp_bijective
    (X Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : generators.rlp (toZero Z)) :
    Function.Bijective
      (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
          (cofibrantLocalReplacement.obj X) ⟶
          (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
        cofibrantLocalComparison.app X ≫ g) :=
  NativeK.cofibrantLocalComparison_precomp_bijective.{u, v} (B := B)
    StabilizationKAdapter.family X Z
    (by simpa only [StabilizationKAdapter.generators_eq] using hZ)

/-- The entire all-object Ho comparison retains the same original Q inverse and K unit. -/
theorem cofibrantLocalComparison_eq_native :
    HEq cofibrantLocalComparison.{u, v}
      (NativeK.cofibrantLocalComparison.{u, v} (B := B) StabilizationKAdapter.family) :=
  HEq.rfl

end PointedCGWH.SequentialSpectrum.StableK
