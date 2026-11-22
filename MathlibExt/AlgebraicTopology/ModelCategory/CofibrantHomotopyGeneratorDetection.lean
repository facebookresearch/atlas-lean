/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRightMappingEnrichment
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Original right-frame mapping tests on cofibrant sources

The raw right-frame bifunctor keeps the original simplicial frame and every
original input map. Its strict source continuity and original Q comparison
relate cofibrant-source tests to the generated homotopy-function complex.
The component calculation proves full weak detection by all cofibrant sources
using the original model localization; no detector certificate is an input.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w u v t s uH vH

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingModels
open GeneratedFrameHomComplex HomotopyMappingSpaceCategory

/-- The original right frame with the actual source object left unreplaced. -/
def rawBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  ResolutionHomComplex.ofFunctors (CosimplicialObject.const C) (rightFrame d)

/-- The raw complex uses every original coefficient Hom into the original right frame. -/
abbrev rawSpace (A Y : C) : SSet.{v} := ((rawBifunctor d).obj (op A)).obj Y

/-- The entire source action is precomposition by the original source map. -/
abbrev rawPrecomp {A B : C} (i : A ⟶ B) (Y : C) : rawSpace d B Y ⟶ rawSpace d A Y :=
  ((rawBifunctor d).map i.op).app Y

/-- The entire target action is postcomposition by the original right-frame map. -/
abbrev rawPostcomp (A : C) {X Y : C} (f : X ⟶ Y) : rawSpace d A X ⟶ rawSpace d A Y :=
  ((rawBifunctor d).obj (op A)).map f

/-- Every raw vertex is the original map into the corresponding actual frame coefficient. -/
theorem rawSpace_obj (A Y : C) (n : SimplexCategoryᵒᵖ) :
    (rawSpace d A Y).obj n = (A ⟶ ((rightFrame d).obj Y).obj n) := rfl

/-- Every original source map acts by its original precomposition in every degree. -/
theorem rawPrecomp_app {A B : C} (i : A ⟶ B) (Y : C) (n : SimplexCategoryᵒᵖ)
    (g : (rawSpace d B Y).obj n) : (rawPrecomp d i Y).app n g = i ≫ g := rfl

/-- Every original target map acts by its original frame component in every degree. -/
theorem rawPostcomp_app (A : C) {X Y : C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (g : (rawSpace d A X).obj n) :
    (rawPostcomp d A f).app n g = g ≫ ((rightFrame d).map f).app n := rfl

/-- The two complete original source and target actions commute. -/
theorem raw_naturality {A B X Y : C} (i : A ⟶ B) (f : X ⟶ Y) :
    rawPrecomp d i X ≫ rawPostcomp d A f = rawPostcomp d B f ≫ rawPrecomp d i Y :=
  ResolutionHomComplex.ofFunctors_naturality (CosimplicialObject.const C) (rightFrame d) i f

/-- The source functor preserves every existing original limit, at independent diagram universes. -/
theorem rawSource_preservesLimits (Y : C) :
    PreservesLimitsOfSize.{t, s} ((rawBifunctor d).flip.obj Y) := by
  apply preservesLimits_of_evaluation
  intro n
  let e : (rawBifunctor d).flip.obj Y ⋙ (evaluation SimplexCategoryᵒᵖ (Type v)).obj n ≅
      yoneda.obj (((rightFrame d).obj Y).obj n) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro A B i
      ext g
      rfl)
  exact preservesLimits_of_natIso e.symm

/-- The raw complex at the original QA is exactly the original generated right complex. -/
theorem rawSpace_Q (A Y : C) : rawSpace d ((Q d).obj A) Y = rightSpace d A Y := rfl

/-- The whole raw target function at QA is the same original generated right function. -/
theorem rawPostcomp_Q (A : C) {X Y : C} (f : X ⟶ Y) :
    rawPostcomp d ((Q d).obj A) f = ((rightBifunctor d).obj (op A)).map f := rfl

/-- Every raw source map between actual cofibrant objects gives a weak map into the original frame. -/
theorem rawPrecomp_weak {A B : C} (i : A ⟶ B) [IsCofibrant A] [IsCofibrant B]
    (hi : weakEquivalences C i) (Y : C) : WeakEquivalence (rawPrecomp d i Y) := by
  let _ := simplicialModel d
  exact QuillenFrameHomComplex.rightPrecomp_weak d i ((rightFrame d).obj Y)
    ((weakEquivalence_iff _).mpr hi) inferInstance inferInstance (rightFrame_isFibrant d d Y)

/-- Every original cofibration induces a fibration on the same actual raw right-frame map. -/
theorem rawPrecomp_fibration {A B : C} (i : A ⟶ B) [Cofibration i] (Y : C) :
    Fibration (rawPrecomp d i Y) :=
  QuillenFrameHomComplex.rightPrecomp_originalFrame_fibration d i Y

/-- Cofibrant original sources have actual Kan right-frame mapping spaces. -/
theorem rawSpace_kanComplex (A : C) [IsCofibrant A] (Y : C) : SSet.KanComplex (rawSpace d A Y) :=
  RightFrameHornGeometry.right_kanComplex A ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y)

/-- The generated native target test is exactly weakness of its original raw map at QA. -/
theorem nativePostcomp_iff_raw_Q (A : C) {X Y : C} (f : X ⟶ Y) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A f) ↔
      WeakEquivalence (rawPostcomp d ((Q d).obj A) f) := by
  let _ : localize.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  change IsIso (localize.map (rawPostcomp d ((Q d).obj A) f)) ↔ WeakEquivalence _
  rw [weakEquivalence_iff]
  exact (weakEquivalence_iff_isIso_map_of_isLocalization localize _).symm

/-- For an actual cofibrant source, the original counit compares the raw and generated tests. -/
theorem nativePostcomp_iff_raw (A : C) [IsCofibrant A] {X Y : C} (f : X ⟶ Y) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A f) ↔ WeakEquivalence (rawPostcomp d A f) := by
  let _ : IsCofibrant ((Q d).obj A) := Q_isCofibrant d A
  let q : (Q d).obj A ⟶ A := (counit d).app A
  let _ : WeakEquivalence (rawPrecomp d q X) := rawPrecomp_weak d q (counit_weak d A) X
  let _ : WeakEquivalence (rawPrecomp d q Y) := rawPrecomp_weak d q (counit_weak d A) Y
  rw [nativePostcomp_iff_raw_Q]
  constructor
  · intro hf
    let _ : WeakEquivalence (rawPostcomp d ((Q d).obj A) f) := hf
    exact weakEquivalence_of_postcomp_of_fac (raw_naturality d q f).symm
  · intro hf
    let _ : WeakEquivalence (rawPostcomp d A f) := hf
    exact weakEquivalence_of_precomp_of_fac (raw_naturality d q f)

/-- The original native target tests are invariant under every original weak source map. -/
theorem nativePostcomp_weak_source_iff {A B : C} (i : A ⟶ B)
    (hi : weakEquivalences C i) {X Y : C} (f : X ⟶ Y) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A f) ↔
      IsIso (GeneratedRightMappingEnrichment.postcomp d B f) := by
  have hX := GeneratedFrameEnrichmentComparison.right_source_weak d i hi X
  have hY := GeneratedFrameEnrichmentComparison.right_source_weak d i hi Y
  let pX := ((rightBifunctor d).map i.op).app X
  let pY := ((rightBifunctor d).map i.op).app Y
  have hX' : SSet.realizationWeakEquivalences pX := (weakEquivalence_iff _).mp hX
  have hY' : SSet.realizationWeakEquivalences pY := (weakEquivalence_iff _).mp hY
  have hn : pX ≫ ((rightBifunctor d).obj (op A)).map f =
      ((rightBifunctor d).obj (op B)).map f ≫ pY :=
    (((rightBifunctor d).map i.op).naturality f).symm
  rw [nativePostcomp_iff_raw_Q, nativePostcomp_iff_raw_Q]
  constructor
  · intro hf
    change WeakEquivalence (((rightBifunctor d).obj (op B)).map f)
    apply (weakEquivalence_iff _).mpr
    apply SSet.realizationWeakEquivalences.of_postcomp _ pY hY'
    rw [← hn]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hX' ((weakEquivalence_iff _).mp hf)
  · intro hf
    change WeakEquivalence (((rightBifunctor d).obj (op A)).map f)
    apply (weakEquivalence_iff _).mpr
    apply SSet.realizationWeakEquivalences.of_precomp pX _ hX'
    rw [hn]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ ((weakEquivalence_iff _).mp hf) hY'

/-- The native target test gives a bijection on the original homotopy-category
Hom sets through the original component correspondence and target naturality. -/
theorem nativePostcomp_hom_bijective
    {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]
    (A : C) {X Y : C} (f : X ⟶ Y)
    (hf : IsIso (GeneratedRightMappingEnrichment.postcomp d A f)) :
    Function.Bijective (fun g : L.obj A ⟶ L.obj X => g ≫ L.map f) := by
  have hw := (nativePostcomp_iff_raw_Q d A f).mp hf
  have hp := SSet.realizationWeakEquivalences.bijective_mapπ₀ ((weakEquivalence_iff _).mp hw)
  let eX := rightPiZeroEquiv d L A X
  let eY := rightPiZeroEquiv d L A Y
  have he : (fun g : L.obj A ⟶ L.obj X => g ≫ L.map f) =
      eY ∘ SSet.mapπ₀ (rawPostcomp d ((Q d).obj A) f) ∘ eX.symm := by
    funext g
    dsimp only [Function.comp_def]
    simpa only [eX, eY, rawPostcomp_Q, Equiv.apply_symm_apply] using
      (rightPiZeroEquiv_naturality_target d L A f (eX.symm g)).symm
  rw [he]
  exact eY.bijective.comp (hp.comp eX.symm.bijective)

/-- Tests on all original source objects detect weak equivalences at completely
arbitrary arrow endpoints, through the original model localization. -/
theorem weak_iff_native_postcomp_all {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ A : C, IsIso (GeneratedRightMappingEnrichment.postcomp d A f) := by
  constructor
  · intro hf A
    have h := GeneratedFrameEnrichmentComparison.right_target_weak d A f hf
    change IsIso (localize.map (((rightBifunctor d).obj (op A)).map f))
    exact localize_isIso _ ((weakEquivalence_iff _).mp h)
  · intro h
    let L := toHomotopyCategory C
    have hHom (A : C) : Function.Bijective (fun g : L.obj A ⟶ L.obj X => g ≫ L.map f) :=
      nativePostcomp_hom_bijective d L A f (h A)
    obtain ⟨g, hg⟩ := (hHom Y).surjective (𝟙 (L.obj Y))
    change g ≫ L.map f = 𝟙 (L.obj Y) at hg
    have hfg : L.map f ≫ g = 𝟙 (L.obj X) := by
      apply (hHom X).injective
      dsimp only
      rw [Category.assoc, hg, Category.comp_id, Category.id_comp]
    let e : L.obj X ≅ L.obj Y := ⟨L.map f, g, hfg, hg⟩
    exact (weakEquivalence_iff_isIso_map_of_isLocalization L f).mpr e.isIso_hom

/-- The same original native tests on actual cofibrant sources suffice, with
the original generated QA and its whole weak counit comparison retained. -/
theorem weak_iff_native_postcomp_cofibrant {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔
      ∀ A : C, IsCofibrant A → IsIso (GeneratedRightMappingEnrichment.postcomp d A f) := by
  constructor
  · intro hf A _
    exact (weak_iff_native_postcomp_all d f).mp hf A
  · intro h
    apply (weak_iff_native_postcomp_all d f).mpr
    intro A
    exact (nativePostcomp_weak_source_iff d ((counit d).app A) (counit_weak d A) f).mp
      (h ((Q d).obj A) (Q_isCofibrant d A))

end HomotopicalAlgebra.CofibrantHomotopyGeneratorDetection
