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
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
import MathlibExt.CategoryTheory.Presentable.SmallFamily
import MathlibExt.CategoryTheory.SmallObject.FactorizationAccessibility
import MathlibExt.AlgebraicTopology.ModelCategory.CellularGeneratingEndpointDetection
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyMappingCalculation

/-!
# The original small cofibrant source family

The labels retain both endpoints of both original generating families. Their
cofibrant approximations use the original generated Q, with its original weak
counit and all original generating-map squares. A common rank bounds both the
original endpoints and these actual approximations. No detection property is
part of the source data.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w u v

open CategoryTheory CategoryTheory.Limits
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CombinatorialHomotopyGenerators

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The original I/J arrow labels, with a Boolean selecting their original endpoint. -/
abbrev Index := (d.I.toSet × Bool) ⊕ (d.J.toSet × Bool)

/-- The label type is small in the original small-object working universe. -/
theorem index_small : Small.{w} (Index d) := by
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.J.IsSmall.{w} := d.J_smallObject.isSmall
  infer_instance

/-- Every source is exactly an endpoint of its labelled original generating arrow. -/
def source : Index d → C
  | .inl (i, false) => i.1.left
  | .inl (i, true) => i.1.right
  | .inr (j, false) => j.1.left
  | .inr (j, true) => j.1.right

/-- The actual generator is the original generated cofibrant approximation of that source. -/
abbrev generator (k : Index d) : C := (Q d).obj (source d k)

/-- The original generated counit is retained at each original endpoint. -/
abbrev approximation (k : Index d) : generator d k ⟶ source d k :=
  (counit d).app (source d k)

/-- Every labelled generator is cofibrant in the original model. -/
theorem generator_isCofibrant (k : Index d) : IsCofibrant (generator d k) :=
  Q_isCofibrant d (source d k)

/-- Every original approximation is a trivial fibration, including noncofibrant sources. -/
theorem approximation_trivialFibration (k : Index d) :
    trivialFibrations C (approximation d k) :=
  counit_trivialFibration d (source d k)

/-- The complete original I-map acts through the original generated Q functor. -/
abbrev iMap (i : d.I.toSet) : generator d (.inl (i, false)) ⟶ generator d (.inl (i, true)) :=
  (Q d).map i.1.hom

/-- The complete original J-map acts through the same generated Q functor. -/
abbrev jMap (j : d.J.toSet) : generator d (.inr (j, false)) ⟶ generator d (.inr (j, true)) :=
  (Q d).map j.1.hom

/-- The actual I-map comparison retains the whole original counit naturality square. -/
theorem iMap_approximation (i : d.I.toSet) :
    iMap d i ≫ approximation d (.inl (i, true)) =
      approximation d (.inl (i, false)) ≫ i.1.hom :=
  (counit d).naturality i.1.hom

/-- The actual J-map comparison retains the whole original counit naturality square. -/
theorem jMap_approximation (j : d.J.toSet) :
    jMap d j ≫ approximation d (.inr (j, true)) =
      approximation d (.inr (j, false)) ≫ j.1.hom :=
  (counit d).naturality j.1.hom

/-- Local presentability and the original generation produce a common rank for all
original sources and their actual chosen cofibrant approximations. -/
theorem exists_source_rank
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP] :
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular),
      let _ : Fact χ.IsRegular := hχ
      κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        ∀ k : Index d,
          IsCardinalPresentable (source d k) χ ∧ IsCardinalPresentable (generator d k) χ := by
  obtain ⟨χ₀, hχ₀, _hω, hLP, hκ, hC, hI, hJ, _hIZ, _hJZ, _hIL, _hIR, _hJL, _hJR⟩ :=
    d.exists_common_factor_accessibility_cardinal κLP
  let _ : Fact χ₀.IsRegular := hχ₀
  let _ : IsCardinalLocallyPresentable C χ₀ := hC
  let _ : IsLocallyPresentable.{w} C := ⟨χ₀, hχ₀, hC⟩
  let _ : Small.{w} (Index d) := index_small d
  obtain ⟨χ₁, hχ₁, hG⟩ := exists_cardinalPresentable_small_family (generator d)
  let _ : Fact χ₁.IsRegular := hχ₁
  let χ := χ₀ ⊔ χ₁
  have hχ : Fact χ.IsRegular := ⟨iteInduction (fun _ => hχ₁.out) (fun _ => hχ₀.out)⟩
  let _ : Fact χ.IsRegular := hχ
  have hχ₀le : χ₀ ≤ χ := le_sup_left
  have hχ₁le : χ₁ ≤ χ := le_sup_right
  refine ⟨χ, hχ, hLP.trans hχ₀le, hκ.trans hχ₀le,
    IsCardinalLocallyPresentable.of_le C hχ₀le, fun k => ?_⟩
  have hS : IsCardinalPresentable (source d k) χ₀ := by
    rcases k with ⟨i, b⟩ | ⟨j, b⟩
    · cases b
      · exact (hI i).1
      · exact (hI i).2
    · cases b
      · exact (hJ j).1
      · exact (hJ j).2
  let _ : IsCardinalPresentable (source d k) χ₀ := hS
  let _ : IsCardinalPresentable (generator d k) χ₁ := hG k
  exact ⟨isCardinalPresentable_of_le _ hχ₀le, isCardinalPresentable_of_le _ hχ₁le⟩

/-- The actual small cofibrant family detects the original weak arrows at
arbitrary endpoints. The original approximation counits compare the tests
with the original I/J endpoints used by the proved generic detector. -/
theorem weak_iff_generator_tests [IsLeftProper C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔
      ∀ k : Index d, IsIso (GeneratedRightMappingEnrichment.postcomp d (generator d k) f) := by
  constructor
  · intro hf k
    exact (CofibrantHomotopyGeneratorDetection.weak_iff_native_postcomp_all d f).mp hf (generator d k)
  · intro h
    have hSource (k : Index d) : IsIso (GeneratedRightMappingEnrichment.postcomp d (source d k) f) :=
      (CofibrantHomotopyGeneratorDetection.nativePostcomp_weak_source_iff d
        (approximation d k) (approximation_trivialFibration d k).2 f).mp (h k)
    apply (CellularGeneratingEndpointDetection.weak_iff_original_IJ_endpoint_tests d f).mpr
    exact ⟨fun i => ⟨hSource (.inl (i, false)), hSource (.inl (i, true))⟩,
      fun j => ⟨hSource (.inr (j, false)), hSource (.inr (j, true))⟩⟩

section OriginalCompatibleCalculation

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)
include a

open HomotopyMappingSpaceCategory

/-- The original full compatible calculation is retained at every actual
cofibrant generator and every original target. -/
def generatorCalculation (k : Index d) (Y : C) :
    GeneratedRightMappingEnrichment.space d (generator d k) Y ≅
      localize.obj (GeneratedDerivedMapping.space d (generator d k) Y) :=
  ((GeneratedHomotopyMappingCalculation.originalCalculation a d).app (Opposite.op (generator d k))).app Y

/-- Every original target morphism keeps the whole original comparison square. -/
theorem generatorCalculation_target (k : Index d) {X Y : C} (f : X ⟶ Y) :
    GeneratedRightMappingEnrichment.postcomp d (generator d k) f ≫ (generatorCalculation d a k Y).hom =
      (generatorCalculation d a k X).hom ≫
        localize.map (GeneratedDerivedMapping.postcomp d (generator d k) f) :=
  (((GeneratedHomotopyMappingCalculation.originalCalculation a d).hom.app
    (Opposite.op (generator d k))).naturality f)

/-- Every actual original source map keeps the whole original comparison
square, including the Q images of all original I/J generating arrows. -/
theorem generatorCalculation_source {k k' : Index d} (u : generator d k ⟶ generator d k') (Y : C) :
    GeneratedRightMappingEnrichment.precomp d u Y ≫ (generatorCalculation d a k Y).hom =
      (generatorCalculation d a k' Y).hom ≫ localize.map (GeneratedDerivedMapping.precomp d u Y) :=
  congrArg (fun t => t.app Y) ((GeneratedHomotopyMappingCalculation.originalCalculation a d).hom.naturality u.op)

/-- The exact original comparison maps form an Arrow isomorphism between
the native test and the original Q/R enriched mapping test. -/
def generatorPostcompArrowIso (k : Index d) {X Y : C} (f : X ⟶ Y) :
    Arrow.mk (GeneratedRightMappingEnrichment.postcomp d (generator d k) f) ≅
      Arrow.mk (localize.map (GeneratedDerivedMapping.postcomp d (generator d k) f)) :=
  Arrow.isoMk (generatorCalculation d a k X) (generatorCalculation d a k Y)
    (generatorCalculation_target d a k f).symm

/-- The original compatible Q/R mapping tests and native function-complex
tests agree at arbitrary original arrow endpoints. -/
theorem generator_native_iff_derived (k : Index d) {X Y : C} (f : X ⟶ Y) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d (generator d k) f) ↔
      SSet.realizationWeakEquivalences (GeneratedDerivedMapping.postcomp d (generator d k) f) := by
  let _ : localize.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  have h := (CategoryTheory.MorphismProperty.isomorphisms SpaceHo.{v}).arrow_mk_iso_iff
    (generatorPostcompArrowIso d a k f)
  exact h.trans
    (weakEquivalence_iff_isIso_map_of_isLocalization localize
      (GeneratedDerivedMapping.postcomp d (generator d k) f)).symm

/-- Derived mapping out of the actual small cofibrant family detects the
original base weak equivalences at completely arbitrary arrow endpoints. -/
theorem weak_iff_derived_generator_tests [IsLeftProper C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ k : Index d,
      SSet.realizationWeakEquivalences (GeneratedDerivedMapping.postcomp d (generator d k) f) := by
  rw [weak_iff_generator_tests d f]
  exact forall_congr' (fun k => generator_native_iff_derived d a k f)

/-- The original combinatorial simplicial source constructs a source-sized
cofibrant homotopy-generator family, a common original-source/QA rank and
full arbitrary-endpoint derived weak detection. All original Q/I/J arrows
and compatible function-complex comparison maps remain the ones above. -/
theorem constructs [IsLeftProper C]
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP] :
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular),
      let _ : Fact χ.IsRegular := hχ
      Small.{w} (Index d) ∧ κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        (∀ k : Index d,
          IsCofibrant (generator d k) ∧ trivialFibrations C (approximation d k) ∧
            IsCardinalPresentable (source d k) χ ∧ IsCardinalPresentable (generator d k) χ) ∧
        ∀ (X Y : C) (f : X ⟶ Y),
          weakEquivalences C f ↔ ∀ k : Index d,
            SSet.realizationWeakEquivalences (GeneratedDerivedMapping.postcomp d (generator d k) f) := by
  obtain ⟨χ, hχ, hLP, hκ, hC, hSource⟩ := exists_source_rank d κLP
  let _ : Fact χ.IsRegular := hχ
  refine ⟨χ, hχ, index_small d, hLP, hκ, hC, ?_, ?_⟩
  · exact fun k => ⟨generator_isCofibrant d k, approximation_trivialFibration d k,
      (hSource k).1, (hSource k).2⟩
  · exact fun _ _ f => weak_iff_derived_generator_tests d a f

end OriginalCompatibleCalculation

end HomotopicalAlgebra.CombinatorialHomotopyGenerators
