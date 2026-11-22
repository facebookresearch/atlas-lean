/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Original K local replacement and native level homotopy tests

The same original κ/B K-data is applied to the original toZeroArrow functor.
Its actual K-local outputs, all Z/i/p/Arrow maps and relative cells are retained.
Cofibrant input gives the original native Ho Hom universal property. Composing
with the SAME original I-data cofibrant replacement provides the actual
all-object homotopy comparison and detects the canonical Omega Hom tests by
level weakness of the chosen replacement map. The retained local names use the
same Omega tests, replacement functor and unit. Stable model recognition remains
a separate required join.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev NativeCarrier := EnrichedFunctorCat PointedCGWH.{u, v} I

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  generators_isCardinalForSmallObjectArgument

/-- Hom tests against exactly the actual constructed K-local objects. -/
def localTestEquivalences : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  omegaTests s

/-- The retained local-test name denotes the whole canonical original Omega class. -/
theorem localTestEquivalences_eq_omegaTests : localTestEquivalences s = omegaTests s := rfl

/-- The entire class is the intersection of the original targetwise Hom isomorphism tests. -/
theorem localTestEquivalences_eq_iInf_isomorphisms :
    (localTestEquivalences s) =
      ⨅ Z : {Z : (EnrichedFunctorCat PointedCGWH.{u, v} I) // (generators s).rlp (toZero Z)},
        ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage
          ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).op ⋙
            yoneda.obj
              ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z.1))).unop := by
  rw [localTestEquivalences, omegaTests_eq_lifting_tests s]
  ext X Y f
  rw [MorphismProperty.iInf_iff]
  constructor
  · intro h Z
    exact (CategoryTheory.isIso_iff_bijective _).2 (h Z.1 Z.2)
  · intro h Z hZ
    exact (CategoryTheory.isIso_iff_bijective _).1 (h ⟨Z, hZ⟩)

/-- Identity arrows satisfy the same literal local tests. -/
instance localTestEquivalences.containsIdentities :
    (localTestEquivalences s).ContainsIdentities :=
  omegaTests.containsIdentities s

/-- All three composition and cancellation directions hold for the whole local test class. -/
instance localTestEquivalences.hasTwoOutOfThreeProperty :
    (localTestEquivalences s).HasTwoOutOfThreeProperty :=
  omegaTests.hasTwoOutOfThreeProperty s

/-- Whole Arrow retracts preserve every original local Hom test. -/
instance localTestEquivalences.isStableUnderRetracts :
    (localTestEquivalences s).IsStableUnderRetracts :=
  omegaTests.isStableUnderRetracts s

/-- Original native level weak equivalences satisfy all constructed local tests. -/
theorem levelWeak_le_localTestEquivalences :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤ (localTestEquivalences s) :=
  levelWeak_le_omegaTests s

/-- Between the actual constructed local objects the tests detect the native level weak class. -/
theorem localTestEquivalences_iff_levelWeak_of_local
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hX : (generators s).rlp (toZero X)) (hY : (generators s).rlp (toZero Y)) :
    (localTestEquivalences s) f ↔ weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f :=
  omegaTests_iff_levelWeak_of_isOmega s f
    ((lifting_toZero_iff_isOmega s X).mp hX) ((lifting_toZero_iff_isOmega s Y).mp hY)

/-- Every original K-left arrow with genuinely cofibrant source satisfies those same Ho tests. -/
theorem left_localTestEquivalence_of_cofibrant
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : (generators s).rlp.llp f) [IsCofibrant X] : (localTestEquivalences s) f :=
  fun Z hZ => (left_Ho_precomp_bijective_originalPath s) f hf Z
    ((lifting_toZero_iff_isOmega s Z).mpr hZ)

/-- The genuine original K middle-object functor on the same original zero arrows. -/
def localReplacement : (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  omegaReplacement s

/-- The retained local-replacement name is the whole original Omega replacement functor. -/
theorem localReplacement_eq_omegaReplacement : localReplacement s = omegaReplacement s := rfl

/-- The original K injection supplies the entire genuine native replacement unit. -/
def localReplacementUnit : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ (localReplacement s) :=
  omegaReplacementUnit s

/-- The entire retained local unit is the same original Omega replacement unit. -/
theorem localReplacementUnit_eq_omegaReplacementUnit :
    localReplacementUnit s = omegaReplacementUnit s := rfl

/-- The actual original K projection gives the full chosen map to the same original zero. -/
def localReplacementProjection : (localReplacement s) ⟶
    (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj (zeroDiagram (A := I)) where
  app X := omegaReplacementProjection s X
  naturality X Y f := by
    change (factorizationData s).Z.map (toZeroArrow.map f) ≫
        (factorizationData s).p.app (Arrow.mk (toZero Y)) =
      (factorizationData s).p.app (Arrow.mk (toZero X)) ≫ 𝟙 _
    exact (factorizationData_p_naturality s) (toZeroArrow.map f)

/-- The whole replacement functor is the literal original κ small-object Z composition. -/
theorem localReplacement_eq_original : (localReplacement s) =
    toZeroArrow ⋙ (SmallObject.functorialFactorizationData
      (generators s) realizedGeneratorCardinal.{v}).Z := rfl

/-- Every actual object remains the original selected κ iteration. -/
theorem localReplacement_obj (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacement s).obj X =
      SmallObject.obj (generators s) realizedGeneratorCardinal.{v} (toZero X) :=
  rfl

/-- Every whole map is the original κ map on the same full zero Arrow square. -/
theorem localReplacement_map {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (localReplacement s).map f = SmallObject.objMap (generators s) realizedGeneratorCardinal.{v}
      (toZeroArrow.map f) := rfl

/-- The actual replacement unit is the literal original chosen K injection. -/
theorem localReplacementUnit_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementUnit s).app X = SmallObject.ιObj (generators s) realizedGeneratorCardinal.{v}
      (toZero X) := rfl

/-- The actual replacement projection is the literal original chosen K projection. -/
theorem localReplacementProjection_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementProjection s).app X =
      SmallObject.πObj (generators s) realizedGeneratorCardinal.{v}
      (toZero X) := rfl

/-- The complete original maps retain the same original object-to-zero factorization. -/
theorem localReplacement_fac (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementUnit s).app X ≫ (localReplacementProjection s).app X = toZero X :=
  (factorizationData s).fac_app

/-- Both original functorial sides occur in every actual unit naturality square. -/
theorem localReplacementUnit_naturality {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (f : X ⟶ Y) :
    (localReplacementUnit s).app X ≫ (localReplacement s).map f =
      f ≫ (localReplacementUnit s).app Y :=
  (factorizationData_i_naturality s) (toZeroArrow.map f)

/-- The original projection retains complete naturality with every replacement map. -/
theorem localReplacementProjection_naturality {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (f : X ⟶ Y) :
    (localReplacement s).map f ≫ (localReplacementProjection s).app Y =
      (localReplacementProjection s).app X :=
  ((factorizationData_p_naturality s) (toZeroArrow.map f)).trans (Category.comp_id _)

/-- The original selected projection is the actual unique map into the original native zero. -/
theorem localReplacementProjection_eq_toZero (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (localReplacementProjection s).app X = toZero ((localReplacement s).obj X) :=
  zeroDiagram_isZero.eq_of_tgt _ _

/-- The literal original replacement projection satisfies all original K lifting. -/
theorem localReplacementProjection_mem_right (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (generators s).rlp ((localReplacementProjection s).app X) :=
  omegaReplacementProjection_mem_right s X

/-- The actual original K output has the literal original local right lifting. -/
theorem localReplacement_isLocal (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (generators s).rlp (toZero ((localReplacement s).obj X)) := by
  exact (lifting_toZero_iff_isOmega s _).mpr (omegaReplacement_isOmega s X)

/-- The same output is fibrant in the actual native level model. -/
theorem localReplacement_isFibrant (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsFibrant ((localReplacement s).obj X) :=
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant _

/-- The exact same original unit is a relative K-cell complex at the same original κ/B. -/
def localReplacementUnitCells (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators s).homFamily)
      ((localReplacementUnit s).app X) :=
  SmallObject.relativeCellComplexιObj (generators s) realizedGeneratorCardinal.{v} (toZero X)

/-- The actual original unit belongs to the full generated K-left class. -/
theorem localReplacementUnit_mem_left (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (generators s).rlp.llp ((localReplacementUnit s).app X) :=
  omegaReplacementUnit_mem_left s X

/-- The same original unit is an actual native projective cofibration. -/
theorem localReplacementUnit_cofibration (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ((localReplacementUnit s).app X) :=
  omegaReplacementUnit_cofibration s X

/-- On genuinely cofibrant input the actual original native K-local output stays cofibrant. -/
theorem localReplacement_isCofibrant (X : (EnrichedFunctorCat PointedCGWH.{u, v} I))
    [IsCofibrant X] :
    IsCofibrant ((localReplacement s).obj X) :=
  omegaReplacement_isCofibrant s X

/-- The literal original local replacement unit is a Hom-test equivalence on cofibrant input. -/
theorem localReplacementUnit_localTestEquivalence
    (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant X] :
    (localTestEquivalences s) ((localReplacementUnit s).app X) := by
  let _ : IsCofibrant ((𝟭 (NativeCarrier (I := I))).obj X) := by
    change IsCofibrant X
    infer_instance
  exact left_localTestEquivalence_of_cofibrant s
    ((localReplacementUnit s).app X) (localReplacementUnit_mem_left s X)

/-- The same original I-data Q does not change any original local test. -/
theorem cofibrantReplacement_map_localTest_iff
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    (localTestEquivalences s)
      ((Replacement.cofibrantReplacement
        (B := B)).map f) ↔ (localTestEquivalences s) f := by
  let Q : (NativeCarrier (I := I)) ⥤ (NativeCarrier (I := I)) :=
    Replacement.cofibrantReplacement (B := B)
  let π : Q ⟶ 𝟭 (NativeCarrier (I := I)) :=
    Replacement.cofibrantReplacementCounit (B := B)
  have hX : (localTestEquivalences s) (π.app X) := (levelWeak_le_localTestEquivalences s) _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)
  have hY : (localTestEquivalences s) (π.app Y) := (levelWeak_le_localTestEquivalences s) _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences Y)
  have hnat : Q.map f ≫ π.app Y = π.app X ≫ f :=
    Replacement.cofibrantReplacementCounit_naturality f
  constructor
  · intro hf
    have h := (localTestEquivalences s).comp_mem (Q.map f) (π.app Y) hf hY
    rw [hnat] at h
    exact (localTestEquivalences s).of_precomp (π.app X) f hX h
  · intro hf
    have h := (localTestEquivalences s).comp_mem (π.app X) f hX hf
    rw [← hnat] at h
    exact (localTestEquivalences s).of_postcomp (Q.map f) (π.app Y) hY h

/-- On two cofibrant inputs the SAME original K map preserves and reflects every local test. -/
theorem localReplacement_map_localTest_iff
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] :
    (localTestEquivalences s) ((localReplacement s).map f) ↔ (localTestEquivalences s) f := by
  have hX := (localReplacementUnit_localTestEquivalence s) X
  have hY := (localReplacementUnit_localTestEquivalence s) Y
  constructor
  · intro hf
    have h := (localTestEquivalences s).comp_mem ((localReplacementUnit s).app X)
      ((localReplacement s).map f) hX hf
    rw [(localReplacementUnit_naturality s)] at h
    exact (localTestEquivalences s).of_postcomp f ((localReplacementUnit s).app Y) hY h
  · intro hf
    have h := (localTestEquivalences s).comp_mem f ((localReplacementUnit s).app Y) hf hY
    rw [← (localReplacementUnit_naturality s)] at h
    exact (localTestEquivalences s).of_precomp ((localReplacementUnit s).app X)
      ((localReplacement s).map f) hX h

/-- The all-object chosen replacement uses the SAME original I-Q followed by original K-Z. -/
def cofibrantLocalReplacement : (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  Replacement.cofibrantReplacement (B := B) ⋙
    (localReplacement s)

/-- Its exact output has actual K-local lifting, without an Omega or model dictionary. -/
theorem cofibrantLocalReplacement_isLocal (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (generators s).rlp (toZero ((cofibrantLocalReplacement s).obj X)) :=
  (localReplacement_isLocal s) _

/-- The same original I and K cofibrations make every chosen output cofibrant. -/
theorem cofibrantLocalReplacement_isCofibrant (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsCofibrant ((cofibrantLocalReplacement s).obj X) := by
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement
      (A := I) X
  exact (localReplacement_isCofibrant s) _

/-- Level weakness of the full original chosen replacement map detects exactly
the local Hom tests. -/
theorem cofibrantLocalReplacement_map_weak_iff
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((cofibrantLocalReplacement s).map f) ↔
      (localTestEquivalences s) f := by
  let Q : (NativeCarrier (I := I)) ⥤ (NativeCarrier (I := I)) :=
    Replacement.cofibrantReplacement (B := B)
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement
      (A := I) X
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj Y) :=
    Replacement.isCofibrant_cofibrantReplacement
      (A := I) Y
  exact ((localTestEquivalences_iff_levelWeak_of_local s) ((localReplacement s).map (Q.map f))
    ((localReplacement_isLocal s) (Q.obj X)) ((localReplacement_isLocal s) (Q.obj Y))).symm.trans
      (((localReplacement_map_localTest_iff s) (Q.map f)).trans
        ((cofibrantReplacement_map_localTest_iff s) f))

/-- Consequently this actual all-object chosen functor preserves original native level weakness. -/
theorem cofibrantLocalReplacement_map_weak
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((cofibrantLocalReplacement s).map f) :=
  ((cofibrantLocalReplacement_map_weak_iff s) f).mpr ((levelWeak_le_localTestEquivalences s) _ hf)

/-- The actual all-object Ho comparison keeps original Q's projection inverse
and original K's unit. -/
def cofibrantLocalComparison :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶
      (cofibrantLocalReplacement s) ⋙
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
  (Replacement.cofibrantReplacementProjectionIso
    (B := B)).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (Replacement.cofibrantReplacement (B := B))
        (localReplacementUnit s))
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))

/-- Every actual comparison component retains BOTH given original chosen maps. -/
theorem cofibrantLocalComparison_app (X : (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (cofibrantLocalComparison s).app X =
      (Replacement.cofibrantReplacementProjectionIso
        (B := B)).inv.app X ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        ((localReplacementUnit s).app
          ((Replacement.cofibrantReplacement
            (B := B)).obj X)) := rfl

/-- Precomposition by the actual all-object comparison is bijective at every K-local target. -/
theorem cofibrantLocalComparison_precomp_bijective
    (X Z : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hZ : (generators s).rlp (toZero Z)) :
    Function.Bijective
      (fun g : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
          ((cofibrantLocalReplacement s).obj X) ⟶
          (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj Z =>
        (cofibrantLocalComparison s).app X ≫ g) := by
  let Q : (NativeCarrier (I := I)) ⥤ (NativeCarrier (I := I)) :=
    Replacement.cofibrantReplacement (B := B)
  let e : Q ⋙ toHomotopyCategory (NativeCarrier (I := I)) ≅
      toHomotopyCategory (NativeCarrier (I := I)) :=
    Replacement.cofibrantReplacementProjectionIso (B := B)
  let _ : IsCofibrant ((Replacement.cofibrantReplacement (B := B)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement
      (A := I) X
  have hη := (localReplacementUnit_localTestEquivalence s) (Q.obj X) Z
    ((lifting_toZero_iff_isOmega s Z).mp hZ)
  have hπ := (isIso_iff_coyoneda_map_bijective (e.inv.app X)).mp (by infer_instance)
    ((toHomotopyCategory (NativeCarrier (I := I))).obj Z)
  simpa only [(cofibrantLocalComparison_app s), cofibrantLocalReplacement, Functor.comp_obj,
    Q, e, Function.comp_def, ← Category.assoc] using hπ.comp hη

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
