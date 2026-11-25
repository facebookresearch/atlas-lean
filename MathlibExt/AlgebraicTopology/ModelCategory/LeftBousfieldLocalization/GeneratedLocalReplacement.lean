/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyMappingCalculation
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Local
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# The original generated derived locality tests

The locality predicates use the original generated right function complexes.
Their comparison with the original chosen derived mapping bifunctor retains
every input arrow and both replacement naturalities. No accessibility,
localization model, or local replacement unit law is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- Derived locality in the original generated homotopy function complexes. -/
def generatedIsDerivedLocal {K : Type wS} (S : K → Arrow C) (Z : C) : Prop :=
  ∀ k, IsIso (GeneratedRightMappingEnrichment.precomp d (S k).hom Z)

/-- Original base fibrancy together with the same generated derived locality. -/
def generatedLocalFibrant {K : Type wS} (S : K → Arrow C) (Z : C) : Prop :=
  IsFibrant Z ∧ generatedIsDerivedLocal d S Z

/-- Every original arrow is tested against every original local fibrant target. -/
def generatedLocalEquivalences {K : Type wS} (S : K → Arrow C) : MorphismProperty C :=
  fun _ _ f ↦ ∀ Z, generatedLocalFibrant d S Z →
    IsIso (GeneratedRightMappingEnrichment.precomp d f Z)

namespace GeneratedLocalReplacement

open GeneratedFunctorialReplacements GeneratedDerivedMapping HomotopyMappingSpaceCategory

section OriginalComparison

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The common mapping object uses both original chosen replacement functors. -/
abbrev comparisonSpace (X Z : C) : SSet.{v} :=
  space d ((cofibrantReplacement (C := C)).obj X)
    ((fibrantReplacement (C := C)).obj Z)

/-- The original derived mapping object maps to the common object by the same generated q/r. -/
def fromOriginal (X Z : C) :
    ((derivedMappingObject (C := C)).obj (.op X)).obj Z ⟶ comparisonSpace d X Z :=
  ((ordinaryToMixed d).app (.op ((cofibrantReplacement (C := C)).obj X))).app
    ((fibrantReplacement (C := C)).obj Z)

/-- The generated mixed object maps to the same common object by the original chosen q/r. -/
def fromGenerated (X Z : C) : space d X Z ⟶ comparisonSpace d X Z :=
  precomp d ((cofibrantReplacementCounit (C := C)).app X) Z ≫
    postcomp d ((cofibrantReplacement (C := C)).obj X)
      ((fibrantReplacementUnit (C := C)).app Z)

include a in
/-- The entire original comparison leg is weak from the source action. -/
theorem fromOriginal_weak (X Z : C) :
    SSet.realizationWeakEquivalences (fromOriginal d X Z) := by
  exact (weakEquivalence_iff _).mp (ordinaryToMixed_weak d a
    ((cofibrantReplacement (C := C)).obj X) ((fibrantReplacement (C := C)).obj Z))

include a in
/-- The entire generated comparison leg is weak from the same source action. -/
theorem fromGenerated_weak (X Z : C) :
    SSet.realizationWeakEquivalences (fromGenerated d X Z) := by
  let _ : WeakEquivalence
      (precomp d ((cofibrantReplacementCounit (C := C)).app X) Z) :=
    GeneratedDerivedMapping.precomp_weak d a _ Z
  let _ : WeakEquivalence
      (postcomp d ((cofibrantReplacement (C := C)).obj X)
        ((fibrantReplacementUnit (C := C)).app Z)) :=
    GeneratedDerivedMapping.postcomp_weak d a _ _
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (mem_weakEquivalences
      (precomp d ((cofibrantReplacementCounit (C := C)).app X) Z))
    (mem_weakEquivalences
      (postcomp d ((cofibrantReplacement (C := C)).obj X)
        ((fibrantReplacementUnit (C := C)).app Z)))

/-- All original source morphisms preserve the first whole comparison map. -/
theorem fromOriginal_source {X Y : C} (f : X ⟶ Y) (Z : C) :
    derivedMappingPrecomp (C := C) f Z ≫ fromOriginal d X Z =
      fromOriginal d Y Z ≫
        precomp d ((cofibrantReplacement (C := C)).map f)
          ((fibrantReplacement (C := C)).obj Z) :=
  ordinaryToMixed_source_naturality d ((cofibrantReplacement (C := C)).map f)
    ((fibrantReplacement (C := C)).obj Z)

/-- All original target morphisms preserve the first whole comparison map. -/
theorem fromOriginal_target (X : C) {Z Z' : C} (f : Z ⟶ Z') :
    derivedMappingPostcomp (C := C) X f ≫ fromOriginal d X Z' =
      fromOriginal d X Z ≫
        postcomp d ((cofibrantReplacement (C := C)).obj X)
          ((fibrantReplacement (C := C)).map f) :=
  ordinaryToMixed_target_naturality d ((cofibrantReplacement (C := C)).obj X)
    ((fibrantReplacement (C := C)).map f)

/-- All original source morphisms preserve the second whole comparison map. -/
theorem fromGenerated_source {X Y : C} (f : X ⟶ Y) (Z : C) :
    precomp d f Z ≫ fromGenerated d X Z =
      fromGenerated d Y Z ≫
        precomp d ((cofibrantReplacement (C := C)).map f)
          ((fibrantReplacement (C := C)).obj Z) := by
  dsimp only [fromGenerated]
  rw [← Category.assoc, ← precomp_comp]
  have h := (cofibrantReplacementCounit (C := C)).naturality f
  simp only [Functor.id_map] at h
  rw [← h, precomp_comp, Category.assoc, precomp_postcomp, ← Category.assoc]

/-- All original target morphisms preserve the second whole comparison map. -/
theorem fromGenerated_target (X : C) {Z Z' : C} (f : Z ⟶ Z') :
    postcomp d X f ≫ fromGenerated d X Z' =
      fromGenerated d X Z ≫
        postcomp d ((cofibrantReplacement (C := C)).obj X)
          ((fibrantReplacement (C := C)).map f) := by
  dsimp only [fromGenerated]
  rw [← Category.assoc, ← precomp_postcomp, Category.assoc, ← postcomp_comp]
  have h := (fibrantReplacementUnit (C := C)).naturality f
  simp only [Functor.id_map] at h
  rw [h, postcomp_comp, ← Category.assoc]

include a in
/-- Native generated precomposition is exactly the original chosen derived weak test,
at arbitrary source and target endpoints. -/
theorem precomp_isIso_iff_original_weak {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp d f Z) ↔
      SSet.realizationWeakEquivalences (derivedMappingPrecomp (C := C) f Z) := by
  have hNative : IsIso (GeneratedRightMappingEnrichment.precomp d f Z) ↔
      IsIso (localize.map (precomp d f Z)) := by
    let e := GeneratedHomotopyMappingCalculation.calculation a d d
    let eX : GeneratedRightMappingEnrichment.space d X Z ≅ localize.obj (space d X Z) :=
      (e.app (.op X)).app Z
    let eY : GeneratedRightMappingEnrichment.space d Y Z ≅ localize.obj (space d Y Z) :=
      (e.app (.op Y)).app Z
    let _ : IsIso eX.hom := eX.isIso_hom
    let _ : IsIso eY.hom := eY.isIso_hom
    have h := congrArg (fun t ↦ t.app Z) (e.hom.naturality f.op)
    change GeneratedRightMappingEnrichment.precomp d f Z ≫ eX.hom =
      eY.hom ≫ localize.map (precomp d f Z) at h
    constructor
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_left h.symm
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_right h
  have hFirst : IsIso (localize.map (derivedMappingPrecomp (C := C) f Z)) ↔
      IsIso (localize.map (precomp d ((cofibrantReplacement (C := C)).map f)
        ((fibrantReplacement (C := C)).obj Z))) := by
    let _ : IsIso (localize.map (fromOriginal d X Z)) :=
      localize_isIso _ (fromOriginal_weak d a X Z)
    let _ : IsIso (localize.map (fromOriginal d Y Z)) :=
      localize_isIso _ (fromOriginal_weak d a Y Z)
    have h := congrArg localize.map (fromOriginal_source d f Z)
    simp only [Functor.map_comp] at h
    constructor
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_left h.symm
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_right h
  have hSecond : IsIso (localize.map (precomp d f Z)) ↔
      IsIso (localize.map (precomp d ((cofibrantReplacement (C := C)).map f)
        ((fibrantReplacement (C := C)).obj Z))) := by
    let _ : IsIso (localize.map (fromGenerated d X Z)) :=
      localize_isIso _ (fromGenerated_weak d a X Z)
    let _ : IsIso (localize.map (fromGenerated d Y Z)) :=
      localize_isIso _ (fromGenerated_weak d a Y Z)
    have h := congrArg localize.map (fromGenerated_source d f Z)
    simp only [Functor.map_comp] at h
    constructor
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_left h.symm
    · intro hf
      let _ := hf
      exact IsIso.of_isIso_fac_right h
  let _ : localize.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  exact hNative.trans (hSecond.trans hFirst.symm) |>.trans
    (weakEquivalence_iff_isIso_map_of_isLocalization localize _).symm

include a in
/-- The full original local-object predicate is unchanged by generated mapping calculations. -/
theorem generatedIsDerivedLocal_iff_original {K : Type wS} (S : K → Arrow C) (Z : C) :
    generatedIsDerivedLocal d S Z ↔ isDerivedLocal S Z := by
  exact forall_congr' (fun k ↦ precomp_isIso_iff_original_weak d a (S k).hom Z)

include a in
/-- Base fibrancy and every original localizing map are both retained. -/
theorem generatedLocalFibrant_iff_original {K : Type wS} (S : K → Arrow C) (Z : C) :
    generatedLocalFibrant d S Z ↔ isLocalFibrant S Z :=
  and_congr Iff.rfl (generatedIsDerivedLocal_iff_original d a S Z)

include a in
/-- Equality is for the entire original morphism property, at every endpoint and target. -/
theorem generatedLocalEquivalences_eq_original {K : Type wS} (S : K → Arrow C) :
    generatedLocalEquivalences d S = localEquivalences S := by
  funext X Y f
  apply propext
  constructor
  · intro hf Z hZ
    exact (precomp_isIso_iff_original_weak d a f Z).mp
      (hf Z ((generatedLocalFibrant_iff_original d a S Z).mpr hZ))
  · intro hf Z hZ
    exact (precomp_isIso_iff_original_weak d a f Z).mpr
      (hf Z ((generatedLocalFibrant_iff_original d a S Z).mp hZ))

end OriginalComparison

section NativeTests

/-- The whole native source action retains every original composite. -/
theorem nativePrecomp_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (T : C) :
    GeneratedRightMappingEnrichment.precomp d (f ≫ g) T =
      GeneratedRightMappingEnrichment.precomp d g T ≫
        GeneratedRightMappingEnrichment.precomp d f T := by
  simp [GeneratedRightMappingEnrichment.precomp]

/-- Every original base weak arrow gives the same inverted native mapping arrow. -/
theorem nativePrecomp_isIso_of_weak {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) (Z : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp d f Z) := by
  rw [GeneratedRightMappingEnrichment.precomp_eq]
  exact localize_isIso _ ((weakEquivalence_iff _).mp
    (GeneratedFrameEnrichmentComparison.right_source_weak d f hf Z))

/-- Every original source test agrees with the test of its same generated Q map. -/
theorem nativePrecomp_Q_iff {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp d ((Q d).map f) Z) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d f Z) := by
  let _ : IsIso (GeneratedRightMappingEnrichment.precomp d ((counit d).app X) Z) :=
    nativePrecomp_isIso_of_weak d _ (counit_weak d X) Z
  let _ : IsIso (GeneratedRightMappingEnrichment.precomp d ((counit d).app Y) Z) :=
    nativePrecomp_isIso_of_weak d _ (counit_weak d Y) Z
  have h : GeneratedRightMappingEnrichment.precomp d ((counit d).app Y) Z ≫
      GeneratedRightMappingEnrichment.precomp d ((Q d).map f) Z =
    GeneratedRightMappingEnrichment.precomp d f Z ≫
      GeneratedRightMappingEnrichment.precomp d ((counit d).app X) Z := by
    rw [← nativePrecomp_comp, ← nativePrecomp_comp]
    exact congrArg (fun i ↦ GeneratedRightMappingEnrichment.precomp d i Z)
      ((counit d).naturality f)
  constructor
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_right h.symm
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_left h

/-- An inverted original generated precomposition map is bijective on the same original components.
-/
theorem nativePrecomp_bijective_components {X Y : C} (f : X ⟶ Y) (Z : C)
    (hf : IsIso (GeneratedRightMappingEnrichment.precomp d f Z)) :
    Function.Bijective
        (SSet.mapπ₀ (((GeneratedFrameHomComplex.rightBifunctor d).map f.op).app Z)) := by
  let _ : localize.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  have hw : SSet.realizationWeakEquivalences
      (((GeneratedFrameHomComplex.rightBifunctor d).map f.op).app Z) := by
    apply (weakEquivalence_iff_isIso_map_of_isLocalization localize _).mpr
    change IsIso (localize.map (((GeneratedFrameHomComplex.rightBifunctor d).map f.op).app Z)) at hf
    exact hf
  exact hw.bijective_mapπ₀

/-- Between original local fibrant objects, the native local class is exactly the base weak class.
Both inverse triangles are derived from the original mapping components. -/
theorem generatedLocalEquivalences_weak_iff_of_local {K : Type wS} (S : K → Arrow C)
    {X Y : C} (f : X ⟶ Y) (hX : generatedLocalFibrant d S X)
    (hY : generatedLocalFibrant d S Y) :
    generatedLocalEquivalences d S f ↔ weakEquivalences C f := by
  constructor
  · intro hf
    let H := (weakEquivalences C).Q
    let eXX := GeneratedFrameHomComplex.rightPiZeroEquiv d H X X
    let eYX := GeneratedFrameHomComplex.rightPiZeroEquiv d H Y X
    let eXY := GeneratedFrameHomComplex.rightPiZeroEquiv d H X Y
    let eYY := GeneratedFrameHomComplex.rightPiZeroEquiv d H Y Y
    have hπX := nativePrecomp_bijective_components d f X (hf X hX)
    have hπY := nativePrecomp_bijective_components d f Y (hf Y hY)
    obtain ⟨qg, hqg⟩ := hπX.surjective (eXX.symm (𝟙 (H.obj X)))
    let g : H.obj Y ⟶ H.obj X := eYX qg
    have hfg : H.map f ≫ g = 𝟙 (H.obj X) := by
      calc
        H.map f ≫ g = eXX (SSet.mapπ₀
            (((GeneratedFrameHomComplex.rightBifunctor d).map f.op).app X) qg) :=
          (GeneratedFrameHomComplex.rightPiZeroEquiv_naturality_source d H f X qg).symm
        _ = eXX (eXX.symm (𝟙 (H.obj X))) := congrArg eXX hqg
        _ = 𝟙 (H.obj X) := eXX.apply_symm_apply _
    let qgf := eYY.symm (g ≫ H.map f)
    let qid := eYY.symm (𝟙 (H.obj Y))
    have hq : qgf = qid := by
      apply hπY.injective
      apply eXY.injective
      rw [GeneratedFrameHomComplex.rightPiZeroEquiv_naturality_source d H f Y qgf,
        GeneratedFrameHomComplex.rightPiZeroEquiv_naturality_source d H f Y qid]
      dsimp only [qgf, qid]
      rw [eYY.apply_symm_apply, eYY.apply_symm_apply]
      rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
    have hgf : g ≫ H.map f = 𝟙 (H.obj Y) := by
      have h := congrArg eYY hq
      simpa only [qgf, qid, eYY.apply_symm_apply] using h
    exact (weakEquivalence_iff_isIso_map_of_isLocalization H f).mpr ⟨⟨g, hfg, hgf⟩⟩
  · intro hf Z _
    exact nativePrecomp_isIso_of_weak d f hf Z

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)

include a in
/-- Ordinary enriched precomposition computes the original generated test at cofibrant
sources and a fibrant target. -/
theorem nativePrecomp_isIso_iff_raw_weak {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (Z : C) [IsFibrant Z] :
    IsIso (GeneratedRightMappingEnrichment.precomp d f Z) ↔
      SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor C).map f.op).app Z) := by
  let eX : localize.obj (SimplicialCategory.sHom X Z) ≅
      GeneratedRightMappingEnrichment.space d X Z :=
    GeneratedHomotopyMappingCalculation.ordinaryCalculation a d d X Z
  let eY : localize.obj (SimplicialCategory.sHom Y Z) ≅
      GeneratedRightMappingEnrichment.space d Y Z :=
    GeneratedHomotopyMappingCalculation.ordinaryCalculation a d d Y Z
  have h := GeneratedHomotopyMappingCalculation.ordinaryCalculation_source a d d f Z
  change localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Z) ≫ eX.hom =
    eY.hom ≫ GeneratedRightMappingEnrichment.precomp d f Z at h
  let e : Arrow.mk (localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Z)) ≅
      Arrow.mk (GeneratedRightMappingEnrichment.precomp d f Z) := Arrow.isoMk eY eX h.symm
  have he := (isomorphisms SpaceHo.{v}).arrow_mk_iso_iff e
  change IsIso (localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Z)) ↔
    IsIso (GeneratedRightMappingEnrichment.precomp d f Z) at he
  let _ : localize.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  exact he.symm.trans (weakEquivalence_iff_isIso_map_of_isLocalization localize _).symm

end NativeTests

section BoundaryFamily

section LocalizingCofibrations

variable {K : Type wS} (S : K → Arrow C)

/-- The actual original I factor of the same generated Q image of a localizing arrow. -/
def localizingFactor (k : K) :=
  d.cofibrantFactorizationData.factorizationData ((Q d).map (S k).hom)

/-- The original cofibration factor retains the original Q source and original middle object. -/
abbrev localizingCofibration (k : K) : Arrow C := Arrow.mk (localizingFactor d S k).i

/-- The source of the cofibration factor is the same original generated Q object. -/
theorem localizingCofibration_left (k : K) :
    (localizingCofibration d S k).left = (Q d).obj (S k).left := rfl

/-- The original I factor is a cofibration. -/
theorem localizingCofibration_mem (k : K) :
    cofibrations C (localizingCofibration d S k).hom := (localizingFactor d S k).hi

/-- The original factor projection is a base weak equivalence. -/
theorem localizingProjection_weak (k : K) :
    weakEquivalences C (localizingFactor d S k).p := (localizingFactor d S k).hp.2

/-- The original localizing arrow and the cofibration factor have exactly the same native test. -/
theorem localizingCofibration_test_iff (k : K) (Z : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp d (localizingCofibration d S k).hom Z) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d (S k).hom Z) := by
  let _ : IsIso (GeneratedRightMappingEnrichment.precomp d (localizingFactor d S k).p Z) :=
    nativePrecomp_isIso_of_weak d _ (localizingProjection_weak d S k) Z
  rw [← nativePrecomp_Q_iff d (S k).hom Z, ← (localizingFactor d S k).fac,
    nativePrecomp_comp]
  exact (isIso_comp_left_iff _ _).symm

end LocalizingCofibrations

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} (S : K → Arrow C)

/-- The actual pushout-product retains the original cofibration and original simplicial boundary. -/
def boundaryPushout (k : K) (n : ℕ) :
    a.tensor.PushoutObjObj (localizingCofibration d S k).hom (SSet.boundary n).ι :=
  Functor.PushoutObjObj.ofHasPushout a.tensor (localizingCofibration d S k).hom
    (SSet.boundary n).ι

/-- The original boundary pushout-product arrow on the original carrier. -/
def boundaryArrow (k : K) (n : ℕ) : Arrow C := Arrow.mk (boundaryPushout d a S k n).ι

/-- The source action proves cofibrancy of every original boundary map. -/
theorem boundaryArrow_mem_cofibrations (k : K) (n : ℕ) :
    cofibrations C (boundaryArrow d a S k n).hom := by
  apply a.cof_cof _ _ (boundaryPushout d a S k n) (localizingCofibration_mem d S k)
  change monomorphisms SSet.{v} (SSet.boundary n).ι
  infer_instance

/-- The exact original J arrows and exact boundary arrows form one original family. -/
def generatingArrow : d.J.toSet ⊕ (K × ℕ) → Arrow C
  | .inl j => j.1
  | .inr (k, n) => boundaryArrow d a S k n

/-- The localization-generating family consists of these same original arrows. -/
def generators : MorphismProperty C :=
  MorphismProperty.ofHoms (fun x ↦ (generatingArrow d a S x).hom)

/-- Smallness is produced from original generation and the small original S index. -/
theorem generators_isSmall [Small.{w} K] : (generators d a S).IsSmall.{w} := by
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  dsimp only [generators]
  exact MorphismProperty.isSmall_ofHoms _

/-- Every original J generating arrow is retained literally. -/
theorem J_le_generators : d.J ≤ generators d a S := by
  intro X Y f hf
  exact MorphismProperty.ofHoms.mk (f := fun x ↦ (generatingArrow d a S x).hom)
    (Sum.inl ⟨Arrow.mk f, hf⟩)

/-- Every original boundary arrow is retained literally. -/
theorem boundaryArrow_mem_generators (k : K) (n : ℕ) :
    generators d a S (boundaryArrow d a S k n).hom := ⟨Sum.inr (k, n)⟩

/-- All arrows in the original small family are base cofibrations. -/
theorem generators_le_cofibrations : generators d a S ≤ cofibrations C := by
  rintro X Y f ⟨x⟩
  cases x with
  | inl j =>
    have h := d.J.le_llp_rlp j.1.hom j.2
    rw [d.J_rlp, fibrations_llp] at h
    exact h.1
  | inr x => exact boundaryArrow_mem_cofibrations d a S x.1 x.2

/-- Right lifting against the original family produces base fibrancy and exact derived S locality.
-/
theorem generators_rlp_terminal_isLocal (Z : C)
    (hZ : (generators d a S).rlp (terminal.from Z)) : generatedLocalFibrant d S Z := by
  have hJ : d.J.rlp (terminal.from Z) := (antitone_rlp (J_le_generators d a S)) _ hZ
  rw [d.J_rlp] at hJ
  let _ : IsFibrant Z := (isFibrant_iff Z).mpr ((fibration_iff _).mpr hJ)
  refine ⟨inferInstance, ?_⟩
  intro k
  let i := (localizingCofibration d S k).hom
  have hi : cofibrations C i := localizingCofibration_mem d S k
  have hRaw : SSet.modelCategoryQuillen.I.rlp
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z) := by
    intro A B j hj
    obtain ⟨n⟩ := hj
    exact (a.tensorHom.hasLiftingProperty_iff (boundaryPushout d a S k n)
      (CompatibleSimplicialMapping.terminalCorner a i Z)).mp
        (hZ _ (boundaryArrow_mem_generators d a S k n))
  have hw : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z) :=
    SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ hRaw
  let _ : IsCofibrant (localizingCofibration d S k).left := Q_isCofibrant d (S k).left
  let _ : Cofibration i := (cofibration_iff i).mpr hi
  let _ : IsCofibrant (localizingCofibration d S k).right := isCofibrant_of_cofibration i
  exact (localizingCofibration_test_iff d S k Z).mp
    ((nativePrecomp_isIso_iff_raw_weak d a i Z).mpr hw)

end BoundaryFamily

section MappingMatching

open scoped Simplicial

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)

/-- The original source Hom functor is applied to the original simplicial diagram. -/
abbrev mappingDiagram (X : C) (F : SimplicialObject C) : SimplicialObject SSet.{v} :=
  F ⋙ (SimplicialCategory.sHomFunctor C).obj (.op X)

/-- Every original source map acts on the whole original mapping diagram. -/
def mappingPrecompDiagram {A B : C} (i : A ⟶ B) (F : SimplicialObject C) :
    mappingDiagram B F ⟶ mappingDiagram A F :=
  Functor.whiskerLeft F ((SimplicialCategory.sHomFunctor C).map i.op)

/-- The caller matching cone is the original matching cone mapped by the original Hom functor. -/
def mappingMatchingCone (X : C) (F : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    Cone (SimplexCategory.reedyOp.matchingDiagram (mappingDiagram X F) n) :=
  ReedyStructure.PostcomposeCorners.matchingCone SimplexCategory.reedyOp
    ((SimplicialCategory.sHomFunctor C).obj (.op X)) n F

include a in
/-- The actual tensor/Hom adjunction preserves exactly this original matching limit. -/
def mappingMatchingIsLimit (X : C) (F : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    IsLimit (mappingMatchingCone X F n) := by
  let _ : PreservesLimitsOfSize.{0, 0} ((SimplicialCategory.sHomFunctor C).obj (.op X)) :=
    (a.tensorHom.adj X).rightAdjoint_preservesLimits
  exact ReedyStructure.PostcomposeCorners.matchingIsLimit SimplexCategory.reedyOp
    ((SimplicialCategory.sHomFunctor C).obj (.op X)) n F

/-- The entire caller matching map is the Hom image of the original matching map. -/
theorem mappingMatchingMap_eq (X : C) (F : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    SimplexCategory.reedyOp.matchingMapWith (mappingDiagram X F) n
        (mappingMatchingCone X F n) (mappingMatchingIsLimit a X F n) =
      ((SimplicialCategory.sHomFunctor C).obj (.op X)).map
        (ReedyStructure.matchingMap SimplexCategory.reedyOp F n) := by
  let _ : PreservesLimitsOfSize.{0, 0} ((SimplicialCategory.sHomFunctor C).obj (.op X)) :=
    (a.tensorHom.adj X).rightAdjoint_preservesLimits
  exact ReedyStructure.PostcomposeCorners.matchingMapWith_eq SimplexCategory.reedyOp
    ((SimplicialCategory.sHomFunctor C).obj (.op X)) n F

/-- The whole mapped matching comparison is the original precomposition at the original limit. -/
theorem mappingMatchingComparison_eq {A B : C} (i : A ⟶ B) (F : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) :
    SimplexCategory.reedyOp.matchingComparisonWith (mappingPrecompDiagram i F) n
        (mappingMatchingCone B F n) (mappingMatchingCone A F n) (mappingMatchingIsLimit a A F n) =
      ((SimplicialCategory.sHomFunctor C).map i.op).app
        (limit (SimplexCategory.reedyOp.matchingDiagram F n)) := by
  apply (mappingMatchingIsLimit a A F n).hom_ext
  intro b
  rw [ReedyStructure.matchingComparisonWith_π]
  change ((SimplicialCategory.sHomFunctor C).obj (.op B)).map
        (limit.π (SimplexCategory.reedyOp.matchingDiagram F n) b) ≫
      ((SimplicialCategory.sHomFunctor C).map i.op).app
        (F.obj (SimplexCategory.reedyOp.matchingTarget b)) =
    ((SimplicialCategory.sHomFunctor C).map i.op).app
        (limit (SimplexCategory.reedyOp.matchingDiagram F n)) ≫
      ((SimplicialCategory.sHomFunctor C).obj (.op A)).map
        (limit.π (SimplexCategory.reedyOp.matchingDiagram F n) b)
  exact (((SimplicialCategory.sHomFunctor C).map i.op).naturality
    (limit.π (SimplexCategory.reedyOp.matchingDiagram F n) b))

include a in
/-- Actual SM7 is the actual Reedy matching fibration of the whole mapping diagram. -/
theorem mappingPrecomp_matchingCorner_fibration {A B : C} (i : A ⟶ B)
    (F : SimplicialObject C) (n : SimplexCategoryᵒᵖ) (hi : cofibrations C i)
    (hF : fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp F n)) :
    fibrations SSet.{v}
      (ReedyStructure.matchingCorner SimplexCategory.reedyOp (mappingPrecompDiagram i F) n) := by
  let sq := Functor.PullbackObjObj.ofHasPullback (SimplicialCategory.sHomFunctor C) i
    (ReedyStructure.matchingMap SimplexCategory.reedyOp F n)
  let cB := mappingMatchingCone B F n
  let cA := mappingMatchingCone A F n
  let hB := mappingMatchingIsLimit a B F n
  let hA := mappingMatchingIsLimit a A F n
  let cP : PullbackCone
      (SimplexCategory.reedyOp.matchingComparisonWith (mappingPrecompDiagram i F) n cB cA hA)
      (SimplexCategory.reedyOp.matchingMapWith (mappingDiagram A F) n cA hA) :=
    PullbackCone.mk sq.snd sq.fst (by
      rw [mappingMatchingComparison_eq, mappingMatchingMap_eq]
      exact sq.isPullback.w.symm)
  have hP : IsLimit cP := by
    have hp : IsPullback sq.snd sq.fst
        (SimplexCategory.reedyOp.matchingComparisonWith (mappingPrecompDiagram i F) n cB cA hA)
        (SimplexCategory.reedyOp.matchingMapWith (mappingDiagram A F) n cA hA) := by
      rw [mappingMatchingComparison_eq, mappingMatchingMap_eq]
      exact sq.isPullback.flip
    exact hp.isLimit
  have he : SimplexCategory.reedyOp.matchingCornerWith (mappingPrecompDiagram i F) n
      cB hB cA hA cP hP = sq.π := by
    apply PullbackCone.IsLimit.hom_ext hP
    · rw [ReedyStructure.matchingCornerWith_fst, mappingMatchingMap_eq]
      exact sq.π_snd.symm
    · rw [ReedyStructure.matchingCornerWith_snd]
      exact sq.π_fst.symm
  apply (ReedyStructure.matchingCornerWith_mem_iff SimplexCategory.reedyOp
    (mappingPrecompDiagram i F) n (fibrations SSet.{v}) cB hB cA hA cP hP).mp
  rw [he]
  exact CompatibleSimplicialMapping.sm7_fibration a sq hi hF

include a in
/-- The actual fixed-target cotensor is fibrant on every original simplicial parameter. -/
theorem cotensorObject_isFibrant (Z : C) [IsFibrant Z] (T : SSet.{v}) :
    IsFibrant ((a.cotensor.obj (.op T)).obj Z) := by
  let _ : (CompatibleCotensorFraming.cotensorAdjunction a Z).IsQuillenAdjunction :=
    CompatibleCotensorFraming.cotensor_isQuillen a Z
  let _ : IsCofibrant T := HomotopyMappingSpaceCategory.all_isCofibrant T
  let _ : IsFibrant (Opposite.op T) :=
    (isFibrant_iff_of_isTerminal (initial.to T).op initialIsInitial.op).mpr (by
      apply (fibration_iff _).mpr
      rw [fibrations_op]
      exact mem_cofibrations (initial.to T))
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := CompatibleCotensorFraming.cotensorAdjunction a Z) inferInstance

include a in
/-- The original cotensor-frame degrees preserve a raw weak test at cofibrant sources. -/
theorem mappingResolutionPrecomp_component_weak {A B : C} [IsCofibrant A] [IsCofibrant B]
    (i : A ⟶ B) (Z : C) [IsFibrant Z]
    (hi : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z))
    (n : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences
      ((mappingPrecompDiagram i ((CompatibleCotensorFraming.resolution a).obj Z)).app n) := by
  let F := (CompatibleCotensorFraming.resolution a).obj Z
  let _ : IsFibrant (F.obj n) := cotensorObject_isFibrant a Z (SSet.stdSimplex.obj n.unop)
  let u : Z ⟶ F.obj n := ((CompatibleCotensorFraming.coaugmentation a).app Z).app n
  let _ : WeakEquivalence u := CompatibleCotensorFraming.coaugmentation_weak a Z n
  have hA : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).obj (.op A)).map u) :=
    (weakEquivalence_iff _).mp (CompatibleSimplicialMapping.postcomp_weak a A u)
  have hB : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).obj (.op B)).map u) :=
    (weakEquivalence_iff _).mp (CompatibleSimplicialMapping.postcomp_weak a B u)
  have h := ((SimplicialCategory.sHomFunctor C).map i.op).naturality u
  apply SSet.realizationWeakEquivalences.of_precomp
    (((SimplicialCategory.sHomFunctor C).obj (.op B)).map u) _ hB
  change SSet.realizationWeakEquivalences
    (((SimplicialCategory.sHomFunctor C).obj (.op B)).map u ≫
      ((SimplicialCategory.sHomFunctor C).map i.op).app (F.obj n))
  rw [h]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hi hA

include a in
/-- The genuine Reedy matching limit of the cotensor frame preserves the same raw weak test. -/
theorem cotensorBoundary_rawPrecomp_weak {A B : C} [IsCofibrant A] [IsCofibrant B]
    (i : A ⟶ B) (Z : C) [IsFibrant Z] (hi : cofibrations C i)
    (hw : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z)) (n : ℕ) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app
        ((a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))).obj Z)) := by
  let F := (CompatibleCotensorFraming.resolution a).obj Z
  let f := mappingPrecompDiagram i F
  have hFib (j : SimplexCategoryᵒᵖ) :
      fibrations SSet.{v} (ReedyStructure.matchingCorner SimplexCategory.reedyOp f j) :=
    mappingPrecomp_matchingCorner_fibration a i F j hi
      (CompatibleCotensorFraming.matchingMap_fibration a Z j.unop)
  have hWeak (j : SimplexCategoryᵒᵖ) : weakEquivalences SSet.{v} (f.app j) :=
    mappingResolutionPrecomp_component_weak a i Z hw j
  have hTriv (j : SimplexCategoryᵒᵖ) :
      trivialFibrations SSet.{v} (ReedyStructure.matchingCorner SimplexCategory.reedyOp f j) :=
    ReedyModel.matchingCorner_trivialFibration_of_fibration_weak
      SimplexCategory.reedyOp f hFib hWeak j
  have hLimit : trivialFibrations SSet.{v}
      (((SimplicialCategory.sHomFunctor C).map i.op).app
        (limit (SimplexCategory.reedyOp.matchingDiagram F (.op ⦋n⦌)))) := by
    have h := ReedyModel.matchingComparisonWith_trivialFibration SimplexCategory.reedyOp f (.op ⦋n⦌)
      (mappingMatchingCone B F (.op ⦋n⦌)) (mappingMatchingIsLimit a B F (.op ⦋n⦌))
      (mappingMatchingCone A F (.op ⦋n⦌)) (mappingMatchingIsLimit a A F (.op ⦋n⦌))
      (fun j _ ↦ hTriv j)
    rwa [mappingMatchingComparison_eq] at h
  let e : limit (SimplexCategory.reedyOp.matchingDiagram F (.op ⦋n⦌)) ≅
      (a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))).obj Z :=
    CompatibleCotensorFraming.matchingBoundaryIso a Z ⦋n⦌
  have h := ((SimplicialCategory.sHomFunctor C).map i.op).naturality e.hom
  apply SSet.realizationWeakEquivalences.of_precomp
    (((SimplicialCategory.sHomFunctor C).obj (.op B)).map e.hom) _
    (SSet.realizationWeakEquivalences.of_isIso _)
  rw [h]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hLimit.2
    (SSet.realizationWeakEquivalences.of_isIso _)

/-- The same original local targets remain local under every original standard cotensor. -/
theorem cotensorSimplex_isLocal {K : Type wS} (S : K → Arrow C) (Z : C)
    (hZ : generatedLocalFibrant d S Z) (n : ℕ) :
    generatedLocalFibrant d S ((a.cotensor.obj (.op (SSet.stdSimplex.obj ⦋n⦌))).obj Z) := by
  let _ : IsFibrant Z := hZ.1
  let T := (a.cotensor.obj (.op (SSet.stdSimplex.obj ⦋n⦌))).obj Z
  let _ : IsFibrant T := cotensorObject_isFibrant a Z (SSet.stdSimplex.obj ⦋n⦌)
  refine ⟨inferInstance, ?_⟩
  intro k
  let i := (localizingCofibration d S k).hom
  let _ : IsCofibrant (localizingCofibration d S k).left := Q_isCofibrant d (S k).left
  let _ : Cofibration i := (cofibration_iff i).mpr (localizingCofibration_mem d S k)
  let _ : IsCofibrant (localizingCofibration d S k).right := isCofibrant_of_cofibration i
  have hw : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z) :=
    (nativePrecomp_isIso_iff_raw_weak d a i Z).mp
      ((localizingCofibration_test_iff d S k Z).mpr (hZ.2 k))
  have h := mappingResolutionPrecomp_component_weak a i Z hw (.op ⦋n⦌)
  change SSet.realizationWeakEquivalences
    (((SimplicialCategory.sHomFunctor C).map i.op).app T) at h
  exact (localizingCofibration_test_iff d S k T).mp
    ((nativePrecomp_isIso_iff_raw_weak d a i T).mpr h)

/-- The genuine matching limit proves locality of each actual original cotensor boundary. -/
theorem cotensorBoundary_isLocal {K : Type wS} (S : K → Arrow C) (Z : C)
    (hZ : generatedLocalFibrant d S Z) (n : ℕ) :
    generatedLocalFibrant d S ((a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))).obj Z) := by
  let _ : IsFibrant Z := hZ.1
  let T := (a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))).obj Z
  let _ : IsFibrant T := cotensorObject_isFibrant a Z (SSet.boundary n : SSet.{v})
  refine ⟨inferInstance, ?_⟩
  intro k
  let i := (localizingCofibration d S k).hom
  let _ : IsCofibrant (localizingCofibration d S k).left := Q_isCofibrant d (S k).left
  let _ : Cofibration i := (cofibration_iff i).mpr (localizingCofibration_mem d S k)
  let _ : IsCofibrant (localizingCofibration d S k).right := isCofibrant_of_cofibration i
  have hw : SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map i.op).app Z) :=
    (nativePrecomp_isIso_iff_raw_weak d a i Z).mp
      ((localizingCofibration_test_iff d S k Z).mpr (hZ.2 k))
  have h := cotensorBoundary_rawPrecomp_weak a i Z (localizingCofibration_mem d S k) hw n
  exact (localizingCofibration_test_iff d S k T).mp
    ((nativePrecomp_isIso_iff_raw_weak d a i T).mpr h)

/-- Relative SM7 proves that base fibrations between original local fibrant objects lift
against the actual original localization-generating family. -/
theorem generators_rlp_of_base_fibration_of_local {K : Type wS} (S : K → Arrow C)
    {X Y : C} (p : X ⟶ Y) (hp : fibrations C p)
    (hX : generatedLocalFibrant d S X) (hY : generatedLocalFibrant d S Y) :
    (generators d a S).rlp p := by
  let _ : IsFibrant X := hX.1
  let _ : IsFibrant Y := hY.1
  have hJ : d.J.rlp p := by rwa [d.J_rlp]
  have hGen (x : d.J.toSet ⊕ (K × ℕ)) : HasLiftingProperty (generatingArrow d a S x).hom p := by
    cases x with
    | inl j => exact hJ j.1.hom j.2
    | inr x =>
      rcases x with ⟨k, n⟩
      let i := (localizingCofibration d S k).hom
      have hi : cofibrations C i := localizingCofibration_mem d S k
      let _ : IsCofibrant (localizingCofibration d S k).left := Q_isCofibrant d (S k).left
      let _ : Cofibration i := (cofibration_iff i).mpr hi
      let _ : IsCofibrant (localizingCofibration d S k).right := isCofibrant_of_cofibration i
      have hwX : SSet.realizationWeakEquivalences
          (((SimplicialCategory.sHomFunctor C).map i.op).app X) :=
        (nativePrecomp_isIso_iff_raw_weak d a i X).mp
          ((localizingCofibration_test_iff d S k X).mpr (hX.2 k))
      have hwY : SSet.realizationWeakEquivalences
          (((SimplicialCategory.sHomFunctor C).map i.op).app Y) :=
        (nativePrecomp_isIso_iff_raw_weak d a i Y).mp
          ((localizingCofibration_test_iff d S k Y).mpr (hY.2 k))
      have hTY : trivialFibrations SSet.{v}
          (((SimplicialCategory.sHomFunctor C).map i.op).app Y) :=
        ⟨CompatibleSimplicialMapping.sm7_fibration a
          (CompatibleSimplicialMapping.terminalCorner a i Y) hi
          ((fibration_iff _).mp inferInstance), hwY⟩
      let sq := Functor.PullbackObjObj.ofHasPullback (SimplicialCategory.sHomFunctor C) i p
      have hFst : trivialFibrations SSet.{v} sq.fst :=
        (trivialFibrations SSet.{v}).pullback_fst _ _ hTY
      have hπ : trivialFibrations SSet.{v} sq.π := by
        refine ⟨CompatibleSimplicialMapping.sm7_fibration a sq hi hp, ?_⟩
        apply SSet.realizationWeakEquivalences.of_postcomp
          (W' := SSet.realizationWeakEquivalences) sq.π sq.fst hFst.2
        rw [sq.π_fst]
        exact hwX
      have hBoundary : cofibrations SSet.{v} (SSet.boundary n).ι := by
        change monomorphisms SSet.{v} (SSet.boundary n).ι
        infer_instance
      exact (a.tensorHom.hasLiftingProperty_iff (boundaryPushout d a S k n) sq).mpr
        (hasLiftingProperty_of_wfs (SSet.boundary n).ι sq.π hBoundary hπ)
  rintro A B f ⟨x⟩
  exact hGen x

/-- Every actual cotensor boundary map between original local targets has the original right lifting
tests. -/
theorem cotensorBoundaryMap_generators_rlp {K : Type wS} (S : K → Arrow C) (Z : C)
    (hZ : generatedLocalFibrant d S Z) (n : ℕ) :
    (generators d a S).rlp ((a.cotensor.map (SSet.boundary n).ι.op).app Z) := by
  let _ : IsFibrant Z := hZ.1
  exact generators_rlp_of_base_fibration_of_local d a S _
    (CompatibleCotensorFraming.boundaryMap_fibration a Z ⦋n⦌)
    (cotensorSimplex_isLocal d a S Z hZ n) (cotensorBoundary_isLocal d a S Z hZ n)

/-- Both original parametrized adjunctions identify the actual boundary and cotensor lift tests. -/
theorem boundaryLifting_iff_cotensorLifting {A B : C} (i : A ⟶ B) (Z : C) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι
        (((SimplicialCategory.sHomFunctor C).map i.op).app Z) ↔
      HasLiftingProperty i ((a.cotensor.map (SSet.boundary n).ι.op).app Z) := by
  let _ : PreservesLimitsOfSize.{0, 0}
      (a.cotensor.obj (.op (SSet.boundary n : SSet.{v}))) :=
    (a.tensorCotensor.adj (SSet.boundary n : SSet.{v})).rightAdjoint_preservesLimits
  let _ : PreservesLimitsOfSize.{0, 0} (a.cotensor.obj (.op (SSet.stdSimplex.obj ⦋n⦌))) :=
    (a.tensorCotensor.adj (SSet.stdSimplex.obj ⦋n⦌)).rightAdjoint_preservesLimits
  let sq := Functor.PushoutObjObj.ofHasPushout a.tensor i (SSet.boundary n).ι
  let c := Functor.PullbackObjObj.ofIsTerminal a.cotensor (SSet.boundary n).ι
    (terminal.from Z) terminalIsTerminal
  exact (a.tensorHom.hasLiftingProperty_iff sq
    (CompatibleSimplicialMapping.terminalCorner a i Z)).symm.trans
      (a.tensorCotensor.hasLiftingProperty_iff sq.flip c)

end MappingMatching

end GeneratedLocalReplacement

end HomotopicalAlgebra
