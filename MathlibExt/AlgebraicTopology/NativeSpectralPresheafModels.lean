/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumFunctionEvaluation
public import MathlibExt.CategoryTheory.Monoidal.ModLimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Actual spectral presheaves and their complete native Hom spectrum

A raw presheaf is an actual spectrum-enriched functor from the opposite
source spectral category to Tau Ceti's native symmetric spectra. Its
arrows are the original enriched natural transformations.

The Hom spectrum is the literal equalizer of the two full-action maps
from the product of all component function spectra. The second product
tests every source Hom spectrum, not only its zero-simplex objects.
Derived Hom uses replacements in that entire presheaf category.
The infinity source is the full localization at pointwise native stable
weak maps, independent of K and of motive corepresentability.

Sources: enriched Yoneda; HTT Sections2.2/5.5; BGT1001.2282v4
Sections7.2/8/9.1; HSS Sections2.2/3.1. The native closed spectrum
and full function-evaluation ports retain source pins and license notices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableSpectraInfinitySource NativeDerivedSpectrumModels NativeSpectrumFunctionEvaluation
open scoped Simplicial MonoidalClosed

variable (C : Type) [EnrichedCategory SymmetricSpectrum C]

/-- The entire raw spectral presheaf, including all source coefficient actions. -/
abbrev RawPresheaf := EnrichedFunctor SymmetricSpectrum Cᵒᵖ SymmetricSpectrum

/-- Actual component evaluation preserves the native point-set spectrum. -/
def value (E : RawPresheaf C) (c : C) : SymmetricSpectrum := E.obj (op c)

/-- The original enriched module action uses the complete native closed counit. -/
def action (E : RawPresheaf C) (c d : C) : value C E d ⊗ (c ⟶[SymmetricSpectrum] d) ⟶ value C E c :=
  value C E d ◁ E.map (op d) (op c) ≫ (ihom.ev (value C E d)).app (value C E c)

/-- Every original enriched transformation has its actual native spectrum component. -/
def mapComponent {E F : RawPresheaf C} (f : E ⟶ F) (c : C) : value C E c ⟶ value C F c :=
  MonoidalClosed.uncurry'
    (ForgetEnrichment.homTo SymmetricSpectrum (f.out.app (ForgetEnrichment.of SymmetricSpectrum (op c))))

/-- All component function spectra are retained, in every native spectrum level. -/
def componentFunctions (E F : RawPresheaf C) : C → SymmetricSpectrum :=
  fun c => (Mod.internalHom (value C E c)).obj (value C F c)

/-- Each source Hom spectrum imposes its full homogeneous action relation. -/
def actionFunctions (E F : RawPresheaf C) : C × C → SymmetricSpectrum :=
  fun cd => (Mod.internalHom (value C E cd.2 ⊗ (cd.1 ⟶[SymmetricSpectrum] cd.2))).obj (value C F cd.1)

/-- The first relation precomposes a component function by the original source-module action. -/
def relationLeft (E F : RawPresheaf C) (c d : C) :
    componentFunctions C E F c ⟶ actionFunctions C E F (c, d) :=
  MonoidalClosed.curry
    (action C E c d ▷ componentFunctions C E F c ≫ (ihom.ev (value C E c)).app (value C F c))

/-- The second relation applies the target-module action after the same whole component function. -/
def relationRight (E F : RawPresheaf C) (c d : C) :
    componentFunctions C E F d ⟶ actionFunctions C E F (c, d) :=
  MonoidalClosed.curry
    ((α_ (value C E d) (c ⟶[SymmetricSpectrum] d) (componentFunctions C E F d)).hom ≫
      value C E d ◁ (β_ (c ⟶[SymmetricSpectrum] d) (componentFunctions C E F d)).hom ≫
      (α_ (value C E d) (componentFunctions C E F d) (c ⟶[SymmetricSpectrum] d)).inv ≫
      (ihom.ev (value C E d)).app (value C F d) ▷ (c ⟶[SymmetricSpectrum] d) ≫ action C F c d)


def leftRelations (E F : RawPresheaf C) : piObj (componentFunctions C E F) ⟶ piObj (actionFunctions C E F) :=
  Pi.lift (fun cd => Pi.π (componentFunctions C E F) cd.1 ≫ relationLeft C E F cd.1 cd.2)

def rightRelations (E F : RawPresheaf C) : piObj (componentFunctions C E F) ⟶ piObj (actionFunctions C E F) :=
  Pi.lift (fun cd => Pi.π (componentFunctions C E F) cd.2 ≫ relationRight C E F cd.1 cd.2)

/-- The literal full spectral enriched natural-transformation carrier. -/
def rawHom (E F : RawPresheaf C) : SymmetricSpectrum := equalizer (leftRelations C E F) (rightRelations C E F)

/-- Each native component is the original equalizer inclusion and product projection. -/
def homComponent (E F : RawPresheaf C) (c : C) : rawHom C E F ⟶ componentFunctions C E F c :=
  equalizer.ι _ _ ≫ Pi.π (componentFunctions C E F) c

theorem hom_relations (E F : RawPresheaf C) :
    equalizer.ι (leftRelations C E F) (rightRelations C E F) ≫ leftRelations C E F =
      equalizer.ι (leftRelations C E F) (rightRelations C E F) ≫ rightRelations C E F := equalizer.condition _ _

/-- Spectral representability fixes every original component and all of its module actions. -/
structure RepresentableSource (c : C) where
  presheaf : RawPresheaf C
  object : ∀ d : C, value C presheaf d = (d ⟶[SymmetricSpectrum] c)
  action : ∀ d e : C,
    action C presheaf d e ≫ eqToHom (object d) =
      (eqToHom (object e) ⊗ₘ 𝟙 (d ⟶[SymmetricSpectrum] e)) ≫
        (β_ (e ⟶[SymmetricSpectrum] c) (d ⟶[SymmetricSpectrum] e)).hom ≫ eComp SymmetricSpectrum d e c

/-- Full spectral Yoneda evaluation is the native component at c, its identity, and the complete closed counit. -/
def yonedaEvaluation {c : C} (Y : RepresentableSource C c) (E : RawPresheaf C) :
    rawHom C Y.presheaf E ⟶ value C E c :=
  (λ_ (rawHom C Y.presheaf E)).inv ≫
    ((eId SymmetricSpectrum c ≫ eqToHom (Y.object c).symm) ⊗ₘ homComponent C Y.presheaf E c) ≫
      (ihom.ev (value C Y.presheaf c)).app (value C E c)

variable (S : SpectrumInfinitySource)

/-- Actual presheaf weakness tests every native spectrum component. -/
def IsPresheafWeak {E F : RawPresheaf C} (f : E ⟶ F) : Prop := ∀ c : C, IsStableWeak S (mapComponent C f c)

/-- The whole raw presheaf projective trivial-fibration test. -/
def IsPresheafTrivialFibration {E F : RawPresheaf C} (f : E ⟶ F) : Prop :=
  ∀ c : C, IsLevelTrivialFibration (mapComponent C f c)

def IsProjectivelyCofibrant [HasInitial (RawPresheaf C)] (E : RawPresheaf C) : Prop :=
  ∀ (A B : RawPresheaf C) (p : A ⟶ B), IsPresheafTrivialFibration C p →
    HasLiftingProperty (initial.to E) p

/-- The two replacements are actual whole presheaf functors with their native augmentations. -/
structure PresheafReplacements [HasInitial (RawPresheaf C)] where
  cofibrant : RawPresheaf C ⥤ RawPresheaf C
  cofibrant_augmentation : cofibrant ⟶ 𝟭 (RawPresheaf C)
  cofibrant_source : ∀ E : RawPresheaf C, IsProjectivelyCofibrant C (cofibrant.obj E)
  cofibrant_weak : ∀ E : RawPresheaf C, IsPresheafWeak C S (cofibrant_augmentation.app E)
  fibrant : RawPresheaf C ⥤ RawPresheaf C
  fibrant_augmentation : 𝟭 (RawPresheaf C) ⟶ fibrant
  fibrant_source : ∀ (E : RawPresheaf C) (c : C), IsOmegaFibrant (value C (fibrant.obj E) c)
  fibrant_weak : ∀ E : RawPresheaf C, IsPresheafWeak C S (fibrant_augmentation.app E)

/-- The full derived mapping spectrum is the actual native end of these two specified replacements. -/
def derivedHom [HasInitial (RawPresheaf C)] (R : PresheafReplacements C S) (E F : RawPresheaf C) : SymmetricSpectrum :=
  rawHom C (R.cofibrant.obj E) (R.fibrant.obj F)

def InvertsPresheafWeak (Z : SSet.{1}) (a : (mapping (nerve (RawPresheaf C)) Z) _⦋0⦌) : Prop :=
  ∀ (E F : RawPresheaf C) (f : E ⟶ F), IsPresheafWeak C S f →
    IsEquivalenceEdge Z (((mappingZero _ _).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- The independent full categorical localization of the actual spectral presheaves. -/
structure PresheafInfinitySource where
  category : StableInfinityCategory.{1}
  source : nerve (RawPresheaf C) ⟶ category.toSSet
  source_objects : Function.Bijective (source.app (op ⦋0⦌))
  invert : ∀ (E F : RawPresheaf C) (f : E ⟶ F), IsPresheafWeak C S f →
    IsEquivalenceEdge category.toSSet (source.app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (Z : SSet.{1}) [SSet.Quasicategory Z],
    ∃ f : mapping category.toSSet Z ⟶
      ((mapping (nerve (RawPresheaf C)) Z).fullEnhancedSubcategory (InvertsPresheafWeak C S Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition source Z ∧ CategoricalWeakEquivalence f

end MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels
