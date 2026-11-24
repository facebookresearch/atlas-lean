/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeIKFunctorSources

/-!
# Native spectral tensors and functor images of full motive evaluation

Scalar tensors are the actual native spectrum tensor on projective raw
presheaf representatives. Evaluation uses the complete end projection
and native closed counit at every coefficient spectrum. Coherent tensor
normalizations and unit triangles retain the entire ordinary source
natural transformations, including all simplex parameters.

Colimit-preserving stable functors use their full spectral-linearity
comparison. A map to a spectrum is obtained by sending the original
evaluation diagram through that functor; an RHom or tangent endpoint is
never supplied. Construction and generic coherence proofs remain Wanted.

Sources: HSS Sections 2.2/3.1--3.4; HTT Section 5.5;
BGT arXiv:1001.2282v4 Sections 6.2/8.3/9.2. Native notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityFilteredColimits NativeDiagramFamilies
open StableInfinitySFunctorMaps
open NativeMotivePresheafSources NativeMotiveLocalizationModels NativeMotiveGenerators
open NativeSpectralPresheafModels NativeDerivedSpectrumModels StableSpectraInfinitySource
open NativeSpectrumFunctionEvaluation NativeSpectrumConeSources
open scoped Simplicial MonoidalClosed

def firstProjection (C D : Type 1) [Category.{0} C] [Category.{0} D] : C × D ⥤ C where
  obj p := p.1
  map f := f.1

def secondProjection (C D : Type 1) [Category.{0} C] [Category.{0} D] : C × D ⥤ D where
  obj p := p.2
  map f := f.2

def pairAtFirst (C D : Type 1) [Category.{0} C] [Category.{0} D] (c : C) : D ⥤ C × D where
  obj d := (c, d)
  map f := (𝟙 c, f)
  map_comp f g := by simp

/-- The native nerve cylinder is fixed on every object and every original ordinary arrow.
These equations determine all its simplices, not only the endpoint functors. -/
structure NerveNaturalTransformation {C D : Type 1} [Category.{0} C] [Category.{0} D]
    (F G : C ⥤ D) (a : F ⟶ G) where
  map : nerve C ⊗ (Δ[1] : SSet.{1}) ⟶ nerve D
  objects : ∀ (n : ℕ) (x : (nerve C) _⦋n⦌) (t : (Δ[1] : SSet.{1}) _⦋n⦌) (i : Fin (n + 1)),
    (map.app (op ⦋n⦌) (x, t)).obj i = if t i = 0 then F.obj (x.obj i) else G.obj (x.obj i)
  zero_zero : ∀ (n : ℕ) (x : (nerve C) _⦋n⦌) (t : (Δ[1] : SSet.{1}) _⦋n⦌)
    (i j : Fin (n + 1)) (h : i ≤ j), t i = 0 → t j = 0 →
    HEq ((map.app (op ⦋n⦌) (x, t)).map (homOfLE h)) (F.map (x.map (homOfLE h)))
  zero_one : ∀ (n : ℕ) (x : (nerve C) _⦋n⦌) (t : (Δ[1] : SSet.{1}) _⦋n⦌)
    (i j : Fin (n + 1)) (h : i ≤ j), t i = 0 → t j = 1 →
    HEq ((map.app (op ⦋n⦌) (x, t)).map (homOfLE h)) (a.app (x.obj i) ≫ G.map (x.map (homOfLE h)))
  one_one : ∀ (n : ℕ) (x : (nerve C) _⦋n⦌) (t : (Δ[1] : SSet.{1}) _⦋n⦌)
    (i j : Fin (n + 1)) (h : i ≤ j), t i = 1 → t j = 1 →
    HEq ((map.app (op ⦋n⦌) (x, t)).map (homOfLE h)) (G.map (x.map (homOfLE h)))
  source : (mapping (nerve C) (nerve D)).δ 1 (SSet.yonedaEquiv (MonoidalClosed.curry map)) =
    mappingZero _ _ (nerveMap F)
  target : (mapping (nerve C) (nerve D)).δ 0 (SSet.yonedaEquiv (MonoidalClosed.curry map)) =
    mappingZero _ _ (nerveMap G)

def NerveNaturalTransformation.edge {C D : Type 1} [Category.{0} C] [Category.{0} D]
    {F G : C ⥤ D} {a : F ⟶ G} (N : NerveNaturalTransformation F G a) :
    (mapping (nerve C) (nerve D)) _⦋1⦌ := SSet.yonedaEquiv (MonoidalClosed.curry N.map)

def nativeTensorFunctor {S : SpectrumInfinitySource} (R : SpectrumReplacements S) :
    SymmetricSpectrum × SymmetricSpectrum ⥤ SymmetricSpectrum where
  obj p := R.cofibrant.obj p.1 ⊗ R.cofibrant.obj p.2
  map f := R.cofibrant.map f.1 ⊗ₘ R.cofibrant.map f.2
  map_id p := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]

def spectrumUnitFunctor {S : SpectrumInfinitySource} (R : SpectrumReplacements S) :
    SymmetricSpectrum ⥤ SymmetricSpectrum := pairAtFirst _ _ sphereSpectrum ⋙ nativeTensorFunctor R

def spectrumUnitMap {S : SpectrumInfinitySource} (R : SpectrumReplacements S) :
    spectrumUnitFunctor R ⟶ 𝟭 SymmetricSpectrum where
  app E := (R.cofibrant_augmentation.app sphereSpectrum ⊗ₘ R.cofibrant_augmentation.app E) ≫ (λ_ E).hom
  naturality E F f := by
    dsimp [spectrumUnitFunctor, nativeTensorFunctor, pairAtFirst]
    rw [tensorHom_comp_tensorHom_assoc, R.cofibrant.map_id, Category.id_comp,
      R.cofibrant_augmentation.naturality]
    simp only [Functor.id_map]
    have h : R.cofibrant_augmentation.app sphereSpectrum ⊗ₘ
        (R.cofibrant_augmentation.app E ≫ f) =
        (R.cofibrant_augmentation.app sphereSpectrum ⊗ₘ R.cofibrant_augmentation.app E) ≫
          (𝟙 sphereSpectrum ⊗ₘ f) := by
      symm
      rw [tensorHom_comp_tensorHom]
      simp
    rw [h, Category.assoc]
    have hu : (𝟙 sphereSpectrum ⊗ₘ f) ≫ (λ_ F).hom = (λ_ E).hom ≫ f := by
      rw [_root_.CategoryTheory.MonoidalCategory.id_tensorHom sphereSpectrum f]
      exact _root_.CategoryTheory.MonoidalCategory.leftUnitor_naturality f
    rw [hu, Category.assoc]

def spectrumPairSource (S : SpectrumInfinitySource) :
    nerve (SymmetricSpectrum × SymmetricSpectrum) ⟶ S.category.toSSet ⊗ S.category.toSSet :=
  CartesianMonoidalCategory.lift (nerveMap (firstProjection _ _) ≫ S.source)
    (nerveMap (secondProjection _ _) ≫ S.source)

/-- The target tensor and unit are the full coherent images of the actual native cofibrant tensor and unitor. -/
structure SpectrumTensorSource (S : SpectrumInfinitySource) (R : SpectrumReplacements S) where
  tensor : S.category.toSSet ⊗ S.category.toSSet ⟶ S.category.toSSet
  left_colimits : ∀ x : S.category.toSSet _⦋0⦌,
    PreservesSmallColimits (CartesianMonoidalCategory.lift (SSet.const x) (𝟙 _) ≫ tensor)
  right_colimits : ∀ y : S.category.toSSet _⦋0⦌,
    PreservesSmallColimits (CartesianMonoidalCategory.lift (𝟙 _) (SSet.const y) ≫ tensor)
  normalization : (mapping (nerve (SymmetricSpectrum × SymmetricSpectrum)) S.category.toSSet) _⦋1⦌
  normalization_equivalence : IsEquivalenceEdge _ normalization
  normalization_source : (mapping _ _).δ 1 normalization = mappingZero _ _ (spectrumPairSource S ≫ tensor)
  normalization_target : (mapping _ _).δ 0 normalization = mappingZero _ _ (nerveMap (nativeTensorFunctor R) ≫ S.source)
  rawUnit : NerveNaturalTransformation (spectrumUnitFunctor R) (𝟭 _) (spectrumUnitMap R)
  unit : (mapping S.category.toSSet S.category.toSSet) _⦋1⦌
  unit_equivalence : IsEquivalenceEdge _ unit
  unit_source : (mapping _ _).δ 1 unit =
    mappingZero _ _ (CartesianMonoidalCategory.lift (SSet.const (sphereVertex S)) (𝟙 _) ≫ tensor)
  unit_target : (mapping _ _).δ 0 unit = mappingZero _ _ (𝟙 _)
  unit_triangle : (mapping (nerve SymmetricSpectrum) S.category.toSSet) _⦋2⦌
  unit_first : (mapping _ _).δ 2 unit_triangle =
    (precomposition (nerveMap (pairAtFirst _ _ sphereSpectrum)) S.category.toSSet).app (op ⦋1⦌) normalization
  unit_second : (mapping _ _).δ 0 unit_triangle =
    (postcomposition (nerve SymmetricSpectrum) S.source).app (op ⦋1⦌) rawUnit.edge
  unit_composite : (mapping _ _).δ 1 unit_triangle =
    (precomposition S.source S.category.toSSet).app (op ⦋1⦌) unit

variable {A : NativeKParametrizedSource.StableCategoryEnrichment} {k : Cardinal.{0}}
  {T : SpectralCompactSource A k} {S : SpectrumInfinitySource} (V : MotivePresheafSetup T S)
  (R : SpectrumReplacements S)

/-- The actual derived scalar presheaf tensor retains complete coefficient actions and all component maps. -/
structure RawScalarTensor where
  functor : letI := T.enrichment; SymmetricSpectrum × RawPresheaf T.index ⥤ RawPresheaf T.index
  values : letI := T.enrichment; letI := V.colimits
    ∀ (E : SymmetricSpectrum) (F : RawPresheaf T.index) (c : T.index),
    value T.index (functor.obj (E, F)) c = R.cofibrant.obj E ⊗ value T.index (V.replacements.cofibrant.obj F) c
  action : letI := T.enrichment; letI := V.colimits
    ∀ (E : SymmetricSpectrum) (F : RawPresheaf T.index) (c d : T.index),
    NativeSpectralPresheafModels.action T.index (functor.obj (E, F)) c d ≫ eqToHom (values E F c) =
      eqToHom (values E F d) ▷ (c ⟶[SymmetricSpectrum] d) ≫
      (α_ (R.cofibrant.obj E) (value T.index (V.replacements.cofibrant.obj F) d)
        (c ⟶[SymmetricSpectrum] d)).hom ≫
      R.cofibrant.obj E ◁ NativeSpectralPresheafModels.action T.index (V.replacements.cofibrant.obj F) c d
  maps : letI := T.enrichment; letI := V.colimits
    ∀ (E E' : SymmetricSpectrum) (F F' : RawPresheaf T.index) (a : E ⟶ E') (b : F ⟶ F') (c : T.index),
    mapComponent T.index (functor.map (a, b)) c ≫ eqToHom (values E' F' c) =
      eqToHom (values E F c) ≫
        (R.cofibrant.map a ⊗ₘ mapComponent T.index (V.replacements.cofibrant.map b) c)
  unit : letI := T.enrichment; letI := V.colimits
    pairAtFirst SymmetricSpectrum (RawPresheaf T.index) sphereSpectrum ⋙ functor ⟶ 𝟭 (RawPresheaf T.index)
  unit_components : letI := T.enrichment; letI := V.colimits
    ∀ (F : RawPresheaf T.index) (c : T.index),
    mapComponent T.index (unit.app F) c =
      eqToHom (values sphereSpectrum F c) ≫
      (R.cofibrant_augmentation.app sphereSpectrum ⊗ₘ
        mapComponent T.index (V.replacements.cofibrant_augmentation.app F) c) ≫ (λ_ (value T.index F c)).hom

variable {V R}

def motivePairSource (V : MotivePresheafSetup T S)
    {G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index))}
    (M : letI := T.enrichment; letI := V.colimits; MotiveLocalization V.presheaves V.ends V.replacements G) :
    letI := T.enrichment; letI := V.colimits
    nerve (SymmetricSpectrum × RawPresheaf T.index) ⟶ S.category.toSSet ⊗ M.category.toSSet :=
  letI := T.enrichment
  letI := V.colimits
  CartesianMonoidalCategory.lift (nerveMap (firstProjection _ _) ≫ S.source)
    (nerveMap (secondProjection _ _) ≫ V.presheaves.source ≫ M.reflector)

structure MotiveTensorSource (V : MotivePresheafSetup T S) (R : SpectrumReplacements S)
    {G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index))}
    (M : letI := T.enrichment; letI := V.colimits; MotiveLocalization V.presheaves V.ends V.replacements G) where
  raw : RawScalarTensor V R
  tensor : letI := T.enrichment; letI := V.colimits
    S.category.toSSet ⊗ M.category.toSSet ⟶ M.category.toSSet
  left_colimits : letI := T.enrichment; letI := V.colimits
    ∀ x : S.category.toSSet _⦋0⦌,
    PreservesSmallColimits (CartesianMonoidalCategory.lift (SSet.const x) (𝟙 _) ≫ tensor)
  right_colimits : letI := T.enrichment; letI := V.colimits
    ∀ y : M.category.toSSet _⦋0⦌,
    PreservesSmallColimits (CartesianMonoidalCategory.lift (𝟙 _) (SSet.const y) ≫ tensor)
  normalization : letI := T.enrichment; letI := V.colimits
    (mapping (nerve (SymmetricSpectrum × RawPresheaf T.index)) M.category.toSSet) _⦋1⦌
  normalization_equivalence : letI := T.enrichment; letI := V.colimits
    IsEquivalenceEdge _ normalization
  normalization_source : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 normalization = mappingZero _ _ (motivePairSource V M ≫ tensor)
  normalization_target : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 0 normalization = mappingZero _ _ (nerveMap raw.functor ≫ V.presheaves.source ≫ M.reflector)
  rawUnit : letI := T.enrichment; letI := V.colimits
    NerveNaturalTransformation (pairAtFirst _ _ sphereSpectrum ⋙ raw.functor) (𝟭 _) raw.unit
  unit : letI := T.enrichment; letI := V.colimits
    (mapping M.category.toSSet M.category.toSSet) _⦋1⦌
  unit_equivalence : letI := T.enrichment; letI := V.colimits
    IsEquivalenceEdge _ unit
  unit_source : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 unit = mappingZero _ _
      (CartesianMonoidalCategory.lift (SSet.const (sphereVertex S)) (𝟙 _) ≫ tensor)
  unit_target : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 0 unit = mappingZero _ _ (𝟙 _)
  unit_triangle : letI := T.enrichment; letI := V.colimits
    (mapping (nerve (RawPresheaf T.index)) M.category.toSSet) _⦋2⦌
  unit_first : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 2 unit_triangle =
      (precomposition (nerveMap (pairAtFirst _ _ sphereSpectrum)) M.category.toSSet).app (op ⦋1⦌) normalization
  unit_second : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 0 unit_triangle =
      (postcomposition (nerve (RawPresheaf T.index)) (V.presheaves.source ≫ M.reflector)).app (op ⦋1⦌) rawUnit.edge
  unit_composite : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 unit_triangle =
      (precomposition (V.presheaves.source ≫ M.reflector) M.category.toSSet).app (op ⦋1⦌) unit

structure InverseEdgeSource (C : SSet.{1}) (e : C _⦋1⦌) where
  edge : C _⦋1⦌
  first : C _⦋2⦌
  second : C _⦋2⦌
  first_source : C.δ 2 first = e
  first_target : C.δ 0 first = edge
  first_identity : C.δ 1 first = C.σ 0 (C.δ 1 e)
  second_source : C.δ 2 second = edge
  second_target : C.δ 0 second = e
  second_identity : C.δ 1 second = C.σ 0 (C.δ 0 e)

/-- An equivalence edge carries its displayed inverse-edge data. -/
noncomputable def inverseEdgeSource (C : SSet.{1}) (e : C _⦋1⦌) (h : IsEquivalenceEdge C e) :
    InverseEdgeSource C e :=
  let g := h.choose
  let a := h.choose_spec.choose
  let b := h.choose_spec.choose_spec.choose
  have hab := h.choose_spec.choose_spec.choose_spec
  { edge := g
    first := a
    second := b
    first_source := hab.1
    first_target := hab.2.1
    first_identity := hab.2.2.1
    second_source := hab.2.2.2.1
    second_target := hab.2.2.2.2.1
    second_identity := hab.2.2.2.2.2 }

def chainValue {n : ℕ} {C : SSet.{1}} (d : indexNerve.{1} (Fin (n + 1)) ⟶ C)
    (i : Fin (n + 1)) : C _⦋0⦌ := d.app (op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ i))

def chainEdge {n : ℕ} {C : SSet.{1}} (d : indexNerve.{1} (Fin (n + 1)) ⟶ C)
    (i j : Fin (n + 1)) (h : i ≤ j) : C _⦋1⦌ :=
  d.app (op ⦋1⦌) (ULift.up (nerve.edgeMk (homOfLE h)).edge)

variable (V) {G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index))}
  (M : letI := T.enrichment; letI := V.colimits; MotiveLocalization V.presheaves V.ends V.replacements G)

/-- The full stable functor has actual native point-set representatives of all its object values. -/
structure MotiveFunctorModels where
  functor : letI := T.enrichment; letI := V.colimits; M.category.toSSet ⟶ S.category.toSSet
  colimits : letI := T.enrichment; letI := V.colimits; PreservesSmallColimits functor
  model : letI := T.enrichment; RawPresheaf T.index → SymmetricSpectrum
  normalization : letI := T.enrichment; letI := V.colimits
    ∀ E : RawPresheaf T.index, functor.app (op ⦋0⦌) (M.object E) = S.vertex (model E)

variable {V M}

/-- Spectral linearity is a full natural equivalence on the whole product category.
The unit triangle fixes the canonical comparison on every motive and every higher parameter. -/
structure MotiveFunctorLinearity (F : MotiveFunctorModels V M)
    (D : SpectrumTensorSource S R) (P : MotiveTensorSource V R M) where
  comparison : letI := T.enrichment; letI := V.colimits
    (mapping (S.category.toSSet ⊗ M.category.toSSet) S.category.toSSet) _⦋1⦌
  equivalence : letI := T.enrichment; letI := V.colimits; IsEquivalenceEdge _ comparison
  source : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 comparison = mappingZero _ _ ((𝟙 _ ⊗ₘ F.functor) ≫ D.tensor)
  target : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 0 comparison = mappingZero _ _ (P.tensor ≫ F.functor)
  unit_triangle : letI := T.enrichment; letI := V.colimits
    (mapping M.category.toSSet S.category.toSSet) _⦋2⦌
  unit_first : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 2 unit_triangle =
      (precomposition (CartesianMonoidalCategory.lift (SSet.const (sphereVertex S)) (𝟙 _)) S.category.toSSet).app
        (op ⦋1⦌) comparison
  unit_second : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 0 unit_triangle = (postcomposition M.category.toSSet F.functor).app (op ⦋1⦌) P.unit
  unit_composite : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 unit_triangle = (precomposition F.functor S.category.toSSet).app (op ⦋1⦌) D.unit

/-- Every coefficient evaluation is the literal complete end projection and native closed counit. -/
structure RawMotiveEvaluation (P : RawScalarTensor V R)
    (E F : letI := T.enrichment; RawPresheaf T.index) where
  map : letI := T.enrichment; letI := V.colimits
    P.functor.obj (M.mappingSpectrum E F, M.rawReflector.obj E) ⟶
      V.replacements.fibrant.obj (M.rawReflector.obj F)
  components : letI := T.enrichment; letI := V.colimits
    ∀ c : T.index, mapComponent T.index map c =
      eqToHom (P.values (M.mappingSpectrum E F) (M.rawReflector.obj E) c) ≫
      (β_ (R.cofibrant.obj (M.mappingSpectrum E F))
        (value T.index (V.replacements.cofibrant.obj (M.rawReflector.obj E)) c)).hom ≫
      value T.index (V.replacements.cofibrant.obj (M.rawReflector.obj E)) c ◁
        (R.cofibrant_augmentation.app (M.mappingSpectrum E F) ≫
          homComponent T.index (V.replacements.cofibrant.obj (M.rawReflector.obj E))
            (V.replacements.fibrant.obj (M.rawReflector.obj F)) c) ≫
      (ihom.ev (value T.index (V.replacements.cofibrant.obj (M.rawReflector.obj E)) c)).app
        (value T.index (V.replacements.fibrant.obj (M.rawReflector.obj F)) c)

/-- The whole motive evaluation is the native scalar/end evaluation, followed by the
same raw replacement and reflector units. The inverse edges retain both native triangles. -/
structure MotiveEvaluationSource (P : MotiveTensorSource V R M)
    (E F : letI := T.enrichment; RawPresheaf T.index) where
  raw : RawMotiveEvaluation (M := M) P.raw E F
  inverse_fibrant : letI := T.enrichment; letI := V.colimits
    InverseEdgeSource M.category.toSSet
      (M.reflector.app (op ⦋1⦌) (presheafEdge V.presheaves
        (V.replacements.fibrant_augmentation.app (M.rawReflector.obj F))))
  inverse_unit : letI := T.enrichment; letI := V.colimits
    InverseEdgeSource M.category.toSSet
      (M.reflector.app (op ⦋1⦌) (presheafEdge V.presheaves (M.rawUnit.app F)))
  diagram : letI := T.enrichment; letI := V.colimits; indexNerve.{1} (Fin 6) ⟶ M.category.toSSet
  vertices : letI := T.enrichment; letI := V.colimits
    ∀ i : Fin 6, chainValue diagram i = match i.val with
      | 0 => P.tensor.app (op ⦋0⦌) (S.vertex (M.mappingSpectrum E F), M.object E)
      | 1 => P.tensor.app (op ⦋0⦌) (S.vertex (M.mappingSpectrum E F), M.object (M.rawReflector.obj E))
      | 2 => M.object (P.raw.functor.obj (M.mappingSpectrum E F, M.rawReflector.obj E))
      | 3 => M.object (V.replacements.fibrant.obj (M.rawReflector.obj F))
      | 4 => M.object (M.rawReflector.obj F)
      | _ => M.object F
  first : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 0 1 (by decide) = P.tensor.app (op ⦋1⦌)
      (S.category.toSSet.σ 0 (S.vertex (M.mappingSpectrum E F)),
        M.reflector.app (op ⦋1⦌) (presheafEdge V.presheaves (M.rawUnit.app E)))
  tensor_normalization : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 1 2 (by decide) =
      (evaluateAt (nerve (SymmetricSpectrum × RawPresheaf T.index)) M.category.toSSet
        (ComposableArrows.mk₀ (M.mappingSpectrum E F, M.rawReflector.obj E))).app (op ⦋1⦌) P.normalization
  evaluation : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 2 3 (by decide) = M.reflector.app (op ⦋1⦌) (presheafEdge V.presheaves raw.map)
  fibrant_normalization : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 3 4 (by decide) = inverse_fibrant.edge
  unit_normalization : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 4 5 (by decide) = inverse_unit.edge

def MotiveEvaluationSource.edge {P : MotiveTensorSource V R M}
    {E F : letI := T.enrichment; RawPresheaf T.index} (D : MotiveEvaluationSource P E F) :
    letI := T.enrichment; letI := V.colimits; M.category.toSSet _⦋1⦌ :=
  letI := T.enrichment
  letI := V.colimits
  chainEdge D.diagram 0 5 (by decide)

/-- The point-set tensor-to-value map is the image of that exact full evaluation
diagram under the same functor and unital spectral-linearity comparison. -/
structure FunctorEvaluationSource (F : MotiveFunctorModels V M)
    (D : SpectrumTensorSource S R) (P : MotiveTensorSource V R M) (L : MotiveFunctorLinearity F D P)
    (E E' : letI := T.enrichment; RawPresheaf T.index) (Q : MotiveEvaluationSource P E E') where
  inverse_tensor : letI := T.enrichment; letI := V.colimits
    InverseEdgeSource S.category.toSSet
      ((evaluateAt (nerve (SymmetricSpectrum × SymmetricSpectrum)) S.category.toSSet
        (ComposableArrows.mk₀ (M.mappingSpectrum E E', F.model E))).app (op ⦋1⦌) D.normalization)
  map : letI := T.enrichment; letI := V.colimits
    R.cofibrant.obj (M.mappingSpectrum E E') ⊗ R.cofibrant.obj (F.model E) ⟶ R.fibrant.obj (F.model E')
  diagram : indexNerve.{1} (Fin 5) ⟶ S.category.toSSet
  vertices : letI := T.enrichment; letI := V.colimits
    ∀ i : Fin 5, chainValue diagram i = match i.val with
      | 0 => S.vertex ((nativeTensorFunctor R).obj (M.mappingSpectrum E E', F.model E))
      | 1 => D.tensor.app (op ⦋0⦌) (S.vertex (M.mappingSpectrum E E'), S.vertex (F.model E))
      | 2 => F.functor.app (op ⦋0⦌) (P.tensor.app (op ⦋0⦌) (S.vertex (M.mappingSpectrum E E'), M.object E))
      | 3 => S.vertex (F.model E')
      | _ => S.vertex (R.fibrant.obj (F.model E'))
  first : chainEdge diagram 0 1 (by decide) = inverse_tensor.edge
  linearity : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 1 2 (by decide) =
      (evaluateAt (S.category.toSSet ⊗ M.category.toSSet) S.category.toSSet
        (S.vertex (M.mappingSpectrum E E'), M.object E)).app (op ⦋1⦌) L.comparison
  evaluation : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 2 3 (by decide) = F.functor.app (op ⦋1⦌) Q.edge
  target_augmentation : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 3 4 (by decide) = S.edge (R.fibrant_augmentation.app (F.model E'))
  native_map : letI := T.enrichment; letI := V.colimits
    chainEdge diagram 0 4 (by decide) = S.edge map

end MathlibExt.AlgebraicTopology.NativeMotiveTensorModels
