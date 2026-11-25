/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels
public import MathlibExt.AlgebraicTopology.NativeCompactSourceModels
public import MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares

/-!
# Native complete presheaf end maps and compact-source spectral Yoneda

The source is the actual compact stable-category skeleton. Spectralization
is the original disjoint-basepoint/free-zero functor. Its tensorator is
normalized on the native free generators, including every parameter simplex.

Precomposition and postcomposition of complete presheaf ends are literal
equalizer lifts of the original native internal-Hom maps. Only their action
relation proofs are deferred. The presheaf coherent source uses those same
ends and retains the whole localization at pointwise stable weaknesses.
Restricted Yoneda is normalized by full source composition as a spectrum
map, rather than by an object or a pi0 comparison.

Sources: BGT arXiv:1001.2282v4, Sections 6.1--6.2 and 7.3;
HSS Sections 2.2 and 3.1; enriched Yoneda and HTT Sections 2.2/5.5.
Native Tau Ceti/Mathlib source revisions and licenses remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotivePresheafSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableSpectraInfinitySource NativeDerivedSpectrumModels NativeSpectrumFunctionEvaluation
open NativeSpectraSimplicialSource NativeKParametrizedSource NativeCompactSourceModels
open NativeSpectralPresheafModels
open scoped Simplicial MonoidalClosed

variable (C : Type) [EnrichedCategory SymmetricSpectrum C]

/-- The original internal-Hom precomposition on every component of the full end. -/
def precompositionComponents {E F : RawPresheaf C} (f : E ⟶ F) (G : RawPresheaf C) :
    rawHom C F G ⟶ piObj (componentFunctions C E G) :=
  Pi.lift (fun c => homComponent C F G c ≫
    (MonoidalClosed.pre (mapComponent C f c)).app (value C G c))

/-- Exactly the native action relation needed to lift that fixed map to the end. -/
def PrecompositionCompatible {E F : RawPresheaf C} (f : E ⟶ F) (G : RawPresheaf C) : Prop :=
  precompositionComponents C f G ≫ leftRelations C E G =
    precompositionComponents C f G ≫ rightRelations C E G

/-- This operation is the actual equalizer lift, with no mapping-spectrum callback. -/
def rawPrecomposition {E F : RawPresheaf C} (f : E ⟶ F) (G : RawPresheaf C)
    (h : PrecompositionCompatible C f G) : rawHom C F G ⟶ rawHom C E G :=
  equalizer.lift (precompositionComponents C f G) h

/-- The original internal-Hom postcomposition on every component of the full end. -/
def postcompositionComponents (E : RawPresheaf C) {F G : RawPresheaf C} (g : F ⟶ G) :
    rawHom C E F ⟶ piObj (componentFunctions C E G) :=
  Pi.lift (fun c => homComponent C E F c ≫ (ihom (value C E c)).map (mapComponent C g c))

def PostcompositionCompatible (E : RawPresheaf C) {F G : RawPresheaf C} (g : F ⟶ G) : Prop :=
  postcompositionComponents C E g ≫ leftRelations C E G =
    postcompositionComponents C E g ≫ rightRelations C E G

def rawPostcomposition (E : RawPresheaf C) {F G : RawPresheaf C} (g : F ⟶ G)
    (h : PostcompositionCompatible C E g) : rawHom C E F ⟶ rawHom C E G :=
  equalizer.lift (postcompositionComponents C E g) h

/-- A proof-only convenience bundle for these already fixed native end operations. -/
structure EndFunctoriality : Prop where
  pre : ∀ (E F G : RawPresheaf C) (f : E ⟶ F), PrecompositionCompatible C f G
  post : ∀ (E F G : RawPresheaf C) (g : F ⟶ G), PostcompositionCompatible C E g

variable (S : SpectrumInfinitySource) [HasInitial (RawPresheaf C)]

/-- The derived end map is precomposition by the original cofibrant functor image. -/
def derivedPrecomposition (H : EndFunctoriality C) (R : PresheafReplacements C S)
    {E F : RawPresheaf C} (f : E ⟶ F) (G : RawPresheaf C) :
    derivedHom C S R F G ⟶ derivedHom C S R E G :=
  rawPrecomposition C (R.cofibrant.map f) (R.fibrant.obj G)
    (H.pre _ _ _ (R.cofibrant.map f))

/-- The derived end map is postcomposition by the original fibrant functor image. -/
def derivedPostcomposition (H : EndFunctoriality C) (R : PresheafReplacements C S)
    (E : RawPresheaf C) {F G : RawPresheaf C} (g : F ⟶ G) :
    derivedHom C S R E F ⟶ derivedHom C S R E G :=
  rawPostcomposition C (R.cofibrant.obj E) (R.fibrant.map g)
    (H.post _ _ _ (R.fibrant.map g))

omit [HasInitial (RawPresheaf C)] in
/-- The simplicial Hom uses level zero of the actual complete spectral end. -/
structure PresheafSimplicialEnrichment where
  ordinary : EnrichedOrdinaryCategory SSet.{0} (RawPresheaf C)
  hom_normalization : ∀ E F : RawPresheaf C,
    ordinary.toEnrichedCategory.Hom E F = (level (rawHom C E F) 0).right
  ordinary_normalization : letI := ordinary
    ∀ (E F : RawPresheaf C) (f : E ⟶ F) (c : C) (q : ℕ) (n : SimplexCategoryᵒᵖ)
      (z : (𝟙_ SSet.{0}).obj n) (x : (level (value C E c) q).right.obj n),
    evaluatedSimplex (value C E c) (value C F c) q n
      ((((SymmetricSpectrum.evaluation 0).map (homComponent C E F c)).right).app n
        ((eqToHom (hom_normalization E F)).app n ((eHomEquiv SSet.{0} f).app n z))) x =
      ((SymmetricSpectrum.evaluation q).map (mapComponent C f c)).right.app n x
  composition_normalization : letI := ordinary
    ∀ (E F G : RawPresheaf C) (c : C) (q : ℕ) (n : SimplexCategoryᵒᵖ)
      (f : (E ⟶[SSet.{0}] F).obj n) (g : (F ⟶[SSet.{0}] G).obj n)
      (x : (level (value C E c) q).right.obj n),
    evaluatedSimplex (value C E c) (value C G c) q n
      ((((SymmetricSpectrum.evaluation 0).map (homComponent C E G c)).right).app n
        ((eqToHom (hom_normalization E G)).app n ((eComp SSet.{0} E F G).app n (f, g)))) x =
    evaluatedSimplex (value C F c) (value C G c) q n
      ((((SymmetricSpectrum.evaluation 0).map (homComponent C F G c)).right).app n
        ((eqToHom (hom_normalization F G)).app n g))
      (evaluatedSimplex (value C E c) (value C F c) q n
        ((((SymmetricSpectrum.evaluation 0).map (homComponent C E F c)).right).app n
          ((eqToHom (hom_normalization E F)).app n f)) x)

omit [HasInitial (RawPresheaf C)] in
def presheafCoherentNerve (H : PresheafSimplicialEnrichment C) : SSet.{1} :=
  letI := H.ordinary
  SimplicialNerve (RawPresheaf C)

omit [HasInitial (RawPresheaf C)] in
def presheafOrdinaryToCoherent (H : PresheafSimplicialEnrichment C) :
    nerve (RawPresheaf C) ⟶ presheafCoherentNerve C H :=
  letI := H.ordinary
  SimplicialNerve.fromNerve (RawPresheaf C)

omit [HasInitial (RawPresheaf C)] in
def InvertsCoherentPresheafWeak (H : PresheafSimplicialEnrichment C) (Z : SSet.{1})
    (a : (mapping (presheafCoherentNerve C H) Z) _⦋0⦌) : Prop :=
  ∀ (E F : RawPresheaf C) (f : E ⟶ F), IsPresheafWeak C S f →
    IsEquivalenceEdge Z (((mappingZero _ _).symm a).app (op ⦋1⦌)
      ((presheafOrdinaryToCoherent C H).app (op ⦋1⦌) (nerve.edgeMk f).edge))

omit [HasInitial (RawPresheaf C)] in
/-- The full coherent localization extends the very same ordinary source. -/
structure PresheafCoherentSource (H : PresheafSimplicialEnrichment C)
    (P : NativeSpectralPresheafModels.PresheafInfinitySource C S) where
  map : presheafCoherentNerve C H ⟶ P.category.toSSet
  normalization : presheafOrdinaryToCoherent C H ≫ map = P.source
  universal : ∀ (Z : SSet.{1}) [SSet.Quasicategory Z],
    ∃ f : mapping P.category.toSSet Z ⟶
      ((mapping (presheafCoherentNerve C H) Z).fullEnhancedSubcategory
        (InvertsCoherentPresheafWeak C S H Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition map Z ∧ CategoricalWeakEquivalence f

/-- The native functor used to spectralize the compact stable-category Hom spaces. -/
def suspensionPlus : SSet.{0} ⥤ SymmetricSpectrum :=
  PointedSSet.addBasepoint ⋙ SymmetricSpectrum.free 0

/-- Every original simplex has its actual universal free-zero generator. -/
def suspensionGenerator (X : SSet.{0}) : X ⟶ (level (suspensionPlus.obj X) 0).right :=
  (SymmetricSpectrum.freeAddBasepointAdjunction 0).unit.app X

/-- The lax structure is fixed on actual free-zero tensor generators, rather than left opaque. -/
structure SuspensionPlusSource where
  lax : suspensionPlus.LaxMonoidal
  tensor_generators : letI := lax
    ∀ (X Y : SSet.{0}) (n : SimplexCategoryᵒᵖ) (x : X.obj n) (y : Y.obj n),
    ((levelTensorInsertion (suspensionPlus.obj X) (suspensionPlus.obj Y) 0 0 ≫
      leftLevelUnit (suspensionPlus.obj X ⊗ suspensionPlus.obj Y) 0 ≫
      (SymmetricSpectrum.evaluation 0).map (Functor.LaxMonoidal.μ suspensionPlus X Y)).right).app n
      (PointedSSet.smashMk ((suspensionGenerator X).app n x)
        ((suspensionGenerator Y).app n y)) = (suspensionGenerator (X ⊗ Y)).app n (x, y)

/-- This selected source retains actual omega/kappa compactness and the entire native Hom. -/
structure SpectralCompactSource (A : StableCategoryEnrichment) (k : Cardinal.{0}) where
  skeleton : CompactStableSkeleton A k
  spectralization : SuspensionPlusSource

def SpectralCompactSource.index {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) : Type :=
  letI := T.spectralization.lax
  TransportEnrichment suspensionPlus T.skeleton.carrier

@[instance_reducible]
def SpectralCompactSource.enrichment {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) : EnrichedCategory SymmetricSpectrum T.index :=
  letI := T.spectralization.lax
  letI := T.skeleton.enrichment
  inferInstanceAs (EnrichedCategory SymmetricSpectrum
    (TransportEnrichment suspensionPlus T.skeleton.carrier))

def SpectralCompactSource.represented {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (c : T.index) : StableInfinityCategory.{0} :=
  letI := A.enrichment
  letI := T.skeleton.enrichment
  T.skeleton.representation.obj c

section RestrictedYoneda

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} (T : SpectralCompactSource A k)

/-- The original skeleton representation maps the entire source Hom spectrum. -/
def SpectralCompactSource.representationMap (c d : T.index) :
    letI := T.enrichment
    (c ⟶[SymmetricSpectrum] d) ⟶
      suspensionPlus.obj (A.enrichment.Hom (T.represented c) (T.represented d)) :=
  letI := T.enrichment
  letI := T.spectralization.lax
  letI := A.enrichment
  letI := T.skeleton.enrichment
  suspensionPlus.map (T.skeleton.representation.map c d)

variable (H : letI := T.enrichment; PresheafSimplicialEnrichment T.index)

/-- Restricted spectral Yoneda is normalized on the full source coefficient actions
and on its entire native spectrum-valued enriched Hom maps. -/
structure RestrictedYonedaSource where
  enriched : letI := T.enrichment; letI := A.enrichment; letI := H.ordinary
    EnrichedFunctor SSet.{0}
    (ForgetEnrichment SSet.{0} StableInfinityCategory.{0}) (RawPresheaf T.index)
  object : letI := T.enrichment; letI := A.enrichment; letI := H.ordinary
    ∀ (B : StableInfinityCategory.{0}) (c : T.index),
    value T.index (enriched.obj (ForgetEnrichment.of SSet.{0} B)) c =
      suspensionPlus.obj (A.enrichment.Hom (T.represented c) B)
  action : letI := T.enrichment; letI := A.enrichment; letI := H.ordinary
    letI := T.spectralization.lax
    ∀ (B : StableInfinityCategory.{0}) (c d : T.index),
    NativeSpectralPresheafModels.action T.index (enriched.obj (ForgetEnrichment.of SSet.{0} B)) c d ≫
      eqToHom (object B c) =
    (eqToHom (object B d) ⊗ₘ T.representationMap c d) ≫
      (β_ (suspensionPlus.obj (A.enrichment.Hom (T.represented d) B))
        (suspensionPlus.obj (A.enrichment.Hom (T.represented c) (T.represented d)))).hom ≫
      Functor.LaxMonoidal.μ suspensionPlus _ _ ≫
      suspensionPlus.map (eComp SSet.{0} (T.represented c) (T.represented d) B)
  hom : letI := T.enrichment; letI := A.enrichment; letI := H.ordinary
    letI := T.spectralization.lax
    ∀ (B D : StableInfinityCategory.{0}) (c : T.index),
    ((SymmetricSpectrum.freeAddBasepointAdjunction 0).homEquiv
      (A.enrichment.Hom B D)
      (rawHom T.index (enriched.obj (ForgetEnrichment.of SSet.{0} B))
        (enriched.obj (ForgetEnrichment.of SSet.{0} D)))).symm
      (enriched.map (ForgetEnrichment.of SSet.{0} B) (ForgetEnrichment.of SSet.{0} D) ≫
        eqToHom (H.hom_normalization _ _)) ≫
      homComponent T.index (enriched.obj (ForgetEnrichment.of SSet.{0} B))
        (enriched.obj (ForgetEnrichment.of SSet.{0} D)) c =
    MonoidalClosed.curry
      ((eqToHom (object B c) ⊗ₘ 𝟙 (suspensionPlus.obj (A.enrichment.Hom B D))) ≫
        Functor.LaxMonoidal.μ suspensionPlus _ _ ≫
        suspensionPlus.map (eComp SSet.{0} (T.represented c) B D) ≫
        eqToHom (object D c).symm)

variable {T H}

def RestrictedYonedaSource.presheaf (Y : RestrictedYonedaSource T H)
    (B : StableInfinityCategory.{0}) : letI := T.enrichment; RawPresheaf T.index :=
  letI := T.enrichment
  letI := A.enrichment
  letI := H.ordinary
  Y.enriched.obj (ForgetEnrichment.of SSet.{0} B)

/-- The actual exact-functor Yoneda map is the original full Hom vertex under the same enriched functor. -/
def RestrictedYonedaSource.map (Y : RestrictedYonedaSource T H)
    {B D : StableInfinityCategory.{0}} (f : ExactFunctor B D) :
    letI := T.enrichment; letI := A.enrichment; letI := H.ordinary
    Y.presheaf B ⟶ Y.presheaf D :=
  letI := T.enrichment
  letI := A.enrichment
  letI := H.ordinary
  (eHomEquiv SSet.{0}).symm
    (exactHomPoint A f ≫ Y.enriched.map (ForgetEnrichment.of SSet.{0} B)
      (ForgetEnrichment.of SSet.{0} D))

/-- This whole infinity functor is the native coherent nerve of that same enriched Yoneda functor. -/
def RestrictedYonedaSource.infinityMap (Y : RestrictedYonedaSource T H)
    {S : SpectrumInfinitySource}
    {P : letI := T.enrichment; NativeSpectralPresheafModels.PresheafInfinitySource T.index S}
    (L : letI := T.enrichment; PresheafCoherentSource T.index S H P) :
    letI := T.enrichment
    stableCategories A ⟶ P.category.toSSet :=
  letI := T.enrichment
  letI := A.enrichment
  letI := H.ordinary
  simplicialNerveMap Y.enriched ≫ L.map

/-- The compact representing source is fixed to the entire restricted native Yoneda presheaf. -/
structure RestrictedRepresentable (Y : RestrictedYonedaSource T H) (c : T.index) where
  source : letI := T.enrichment; RepresentableSource T.index c
  normalized : letI := T.enrichment; source.presheaf = Y.presheaf (T.represented c)

end RestrictedYoneda

end MathlibExt.AlgebraicTopology.NativeMotivePresheafSources
