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
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalSolutionSet
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.LocalTrivialCofibrationClosure
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.CombinatorialHomotopyGenerators

/-!
# Original combinatorial sources construct Smith recognition inputs

The original generated replacements and compatible model action prove local
weak-equivalence accessibility and all generator solution squares. Their actual
mapping tests prove the cobase and transfinite closure fields. The target model
and its weak factorization system are not inputs to this construction.
-/

set_option autoImplicit false
noncomputable section

universe w wS u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CombinatorialSourceRecognition

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} (S : K → Arrow C) [Small.{w} K]
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]

include a κLP in
/-- All Smith fields are outputs of the original model, generated mapping
calculus and source presentability. Every incoming solution square is retained. -/
theorem originalSmithRecognitionInput :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    SmithRecognitionInput.{w} d.I (localEquivalences S) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  refine
    { weak_two_out_of_three := localEquivalences_hasTwoOutOfThreeProperty S
      weak_retracts := localEquivalences_isStableUnderRetracts S
      trivial_fibrations_weak := ?_
      trivial_cofibrations_cobase :=
        LocalTrivialCofibrationClosure.originalSmith_cobase d a S
      trivial_cofibrations_transfinite :=
        LocalTrivialCofibrationClosure.originalSmith_transfinite d a S
      solution_set := ?_ }
  · intro X Y f hf
    have htf : trivialFibrations C f := d.I_rlp ▸ hf
    have hw : weakEquivalences C f := htf.2
    rw [← GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
    exact LocalTrivialCofibrationClosure.nativeBaseWeak_le d S f hw
  · intro X Y i _hi
    exact GeneratedLocalReplacement.originalLocalEquivalences_solutionSets d a S κLP (Arrow.mk i)

include a κLP in
/-- The actual source hypotheses construct Smith's localized factorization
classes and both weak factorization systems on the original arrows. -/
theorem originalSmithModelStructureData :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    Nonempty (SmithModelStructureData.{w} d.I (localEquivalences S)) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let : IsLocallyPresentable.{w} C := ⟨κLP, inferInstance, inferInstance⟩
  let : d.I.HasSmallObjectArgument.{w} := ⟨κ, inferInstance, inferInstance, d.I_smallObject⟩
  exact smithRecognition d.I (localEquivalences S) (originalSmithRecognitionInput d a S κLP)

omit [IsLeftProper C] in
include a κLP in
/-- The complete original local arrow class and its inclusion have a
constructed regular accessibility rank; no rank certificate is supplied. -/
theorem originalLocalArrowAccessibility :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular), (localEquivalences S).IsCardinalAccessible ν := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact GeneratedLocalReplacement.originalLocalEquivalences_accessible d a S κLP

include a κLP in
/-- The selected Smith output is chosen from the actual proved source
existence theorem, retaining its generated family and class witnesses. -/
def smithData :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    SmithModelStructureData.{w} d.I (localEquivalences S) :=
  Classical.choice (originalSmithModelStructureData d a S κLP)

/-- The source I factor factory is reclassified by its proved original
right-class identity; its middle objects and both factor maps are unchanged. -/
def cofibrantFactors : FunctorialFactorizationData d.I.rlp.llp d.I.rlp :=
  d.cofibrantFactorizationData.ofLE
    (by rw [d.I_rlp, trivialFibrations_llp]) (by rw [d.I_rlp])

include a κLP in
/-- The generated J small-object factory factors every original arrow,
using the family produced by the selected source Smith construction. -/
def fibrantFactors :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    FunctorialFactorizationData (smithData d a S κLP).J.rlp.llp
      (smithData d a S κLP).J.rlp := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  letI : M.J.HasSmallObjectArgument.{w} := M.J_smallObject
  letI : IsWeakFactorizationSystem M.J.rlp.llp M.J.rlp := M.trivialCofibration_wfs
  exact functorialFactorizationData M.J.rlp.llp M.J.rlp

include a κLP in
/-- A named model on the original category is constructed from Smith's
actual source-derived classes and complete original small-object factors. -/
@[instance_reducible]
def modelCategory : ModelCategory C := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  letI : M.J.HasSmallObjectArgument.{w} := M.J_smallObject
  letI : IsWeakFactorizationSystem M.J.rlp.llp M.J.rlp := M.trivialCofibration_wfs
  letI : (localEquivalences S).HasTwoOutOfThreeProperty :=
    localEquivalences_hasTwoOutOfThreeProperty S
  let Idata := cofibrantFactors d
  let Jdata := fibrantFactors d a S κLP
  have hRight : d.I.rlp = M.J.rlp ⊓ localEquivalences S := M.trivialFibrations_eq.symm
  have hAcyclic : M.J.rlp.llp ≤ localEquivalences S := by
    rw [M.trivialCofibrations_eq]
    exact inf_le_right
  exact OriginalGeneratedModel.modelCategory d.I M.J (localEquivalences S)
    (localEquivalences_hasTwoOutOfThreeProperty S) hRight hAcyclic Idata Jdata

include a κLP in
/-- The produced Smith data identifies the original cofibrations and full
local weak class with both actual left/right lifting classes. -/
theorem originalLocalizedClasses :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∃ M : SmithModelStructureData.{w} d.I (localEquivalences S),
      d.I.rlp.llp = cofibrations C ∧
      M.J.rlp.llp = cofibrations C ⊓ localEquivalences S ∧
      M.J.rlp = localizedFibrations S ∧
      M.J.rlp ⊓ localEquivalences S = trivialFibrations C := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  obtain ⟨M⟩ := originalSmithModelStructureData d a S κLP
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  refine ⟨M, hI, ?_, ?_, ?_⟩
  · exact M.trivialCofibrations_eq.trans (congrArg (fun P => P ⊓ localEquivalences S) hI)
  · rw [M.fibrations_eq, hI]
    rfl
  · exact M.trivialFibrations_eq.trans d.I_rlp

include a κLP in
/-- The constructed model's weak maps are exactly the original full
derived local-equivalence class on the unchanged category. -/
theorem modelWeakEquivalences :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let W := localEquivalences S
    letI : ModelCategory C := modelCategory d a S κLP
    weakEquivalences C = W := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  rfl

include a κLP in
/-- The constructed model keeps the original source cofibrations. -/
theorem modelCofibrations :
    let originalCof := cofibrations C
    letI : ModelCategory C := modelCategory d a S κLP
    cofibrations C = originalCof := by
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  exact hI

omit [Small.{w} K] [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP] in
include a in
/-- Every original terminal lifting test is exactly base fibrancy and all
original derived local tests, using the actual generated frame comparison. -/
theorem originalLocalFibrant_iff (Z : C) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    localizedFibrations S (terminal.from Z) ↔ isLocalFibrant S Z := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  rw [← GeneratedLocalReplacement.generatedLocalFibrant_iff_original d a S Z]
  rw [CellularLocalizationRecognition.localFibrant_iff_terminal_localFibration d S Z]
  change (cofibrations C ⊓ localEquivalences S).rlp (terminal.from Z) ↔
    (cofibrations C ⊓ generatedLocalEquivalences d S).rlp (terminal.from Z)
  rw [GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]

omit [IsLeftProper C] [Small.{w} K] [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] in
include a in
/-- The full original derived local class between the two individual
original local-fibrant objects is exactly the source weak class. -/
theorem originalLocalWhitehead {X Y : C} (f : X ⟶ Y)
    (hX :
      letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
        ⟨⟨d.cofibrantFactorizationData⟩⟩
      letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
        ⟨⟨d.fibrantFactorizationData⟩⟩
      isLocalFibrant S X)
    (hY :
      letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
        ⟨⟨d.cofibrantFactorizationData⟩⟩
      letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
        ⟨⟨d.fibrantFactorizationData⟩⟩
      isLocalFibrant S Y) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    localEquivalences S f ↔ weakEquivalences C f := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  rw [← GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
  exact CellularLocalizationFactorizations.weak_iff_of_local d S f
    ((GeneratedLocalReplacement.generatedLocalFibrant_iff_original d a S X).mpr hX)
    ((GeneratedLocalReplacement.generatedLocalFibrant_iff_original d a S Y).mpr hY)

include a κLP in
/-- All selected-localization recognition fields are constructed from the
original combinatorial source. No localized model or dictionary is supplied. -/
theorem localizationData :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    LeftBousfieldLocalizationData S := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  have hJ : M.J.rlp.llp = cofibrations C ⊓ localEquivalences S := by
    rw [M.trivialCofibrations_eq, hI]
  have hF : M.J.rlp = localizedFibrations S := by
    rw [M.fibrations_eq, hI]
    rfl
  refine
    { localizingMaps := ?_
      baseWeak_le := ?_
      two_out_of_three := localEquivalences_hasTwoOutOfThreeProperty S
      retracts := localEquivalences_isStableUnderRetracts S
      localized_wfs := ?_
      trivialFibrations_eq := ?_
      fibrant_iff := originalLocalFibrant_iff d a S
      weakEquivalence_iff_of_local := fun f hX hY => originalLocalWhitehead d a S f hX hY }
  · intro k
    rw [← GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
    exact CellularLocalizationFactorizations.localizingMaps d S k
  · rw [← GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
    exact CellularLocalizationFactorizations.baseWeak_le d S
  · rw [← hJ, ← hF]
    exact M.trivialCofibration_wfs
  · rw [← hF, M.trivialFibrations_eq, d.I_rlp]

include a κLP in
/-- All original source, generated, and local arrow data have one constructed
regular rank. Both original factor functors and the full local inclusion
remain the actual original functors. -/
theorem existsCommonSourceRank :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular) (_ : OrderBot χ.ord.ToType),
      letI : Fact χ.IsRegular := hχ
      κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        (localEquivalences S).IsCardinalAccessible χ ∧
        d.cofibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        (∀ i : d.I.toSet,
          IsCardinalPresentable i.1.left χ ∧ IsCardinalPresentable i.1.right χ) ∧
        (∀ j : (smithData d a S κLP).J.toSet,
          IsCardinalPresentable j.1.left χ ∧ IsCardinalPresentable j.1.right χ) ∧
        Small.{w} (CombinatorialHomotopyGenerators.Index d) ∧
        (∀ k : CombinatorialHomotopyGenerators.Index d,
          IsCofibrant (CombinatorialHomotopyGenerators.generator d k) ∧
            trivialFibrations C (CombinatorialHomotopyGenerators.approximation d k) ∧
            IsCardinalPresentable (CombinatorialHomotopyGenerators.source d k) χ ∧
            IsCardinalPresentable (CombinatorialHomotopyGenerators.generator d k) χ) ∧
        ∀ (X Y : C) (f : X ⟶ Y), weakEquivalences C f ↔
          ∀ k : CombinatorialHomotopyGenerators.Index d,
            SSet.realizationWeakEquivalences
              (GeneratedDerivedMapping.postcomp d (CombinatorialHomotopyGenerators.generator d k) f) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  obtain ⟨χ₀, hχ₀, _hω, hLP, hκ, hC, hI, _hJ, hIZ, hJZ, _hIL, _hIR, _hJL, _hJR⟩ :=
    d.exists_common_factor_accessibility_cardinal κLP
  let _ : Fact χ₀.IsRegular := hχ₀
  let _ : IsCardinalLocallyPresentable C χ₀ := hC
  let _ : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ₀ := hIZ
  let _ : d.fibrantFactorizationData.Z.IsCardinalAccessible χ₀ := hJZ
  obtain ⟨χG, hχG, hSmall, _hLPG, _hκG, _hCG, hGenerators, hDetection⟩ :=
    CombinatorialHomotopyGenerators.constructs d a κLP
  let _ : Fact χG.IsRegular := hχG
  let M := smithData d a S κLP
  let _ : M.J.HasSmallObjectArgument.{w} := M.J_smallObject
  obtain ⟨κJ, hκJ, hbotJ, hJEligible⟩ := M.J_smallObject.exists_cardinal
  let _ : Fact κJ.IsRegular := hκJ
  let _ : OrderBot κJ.ord.ToType := hbotJ
  let _ : M.J.IsSmall.{w} := hJEligible.isSmall
  let E := M.J.toSet ⊕ M.J.toSet
  let endpoint : E → C := fun e => match e with
    | .inl j => j.1.left
    | .inr j => j.1.right
  let P : ObjectProperty C := ObjectProperty.ofObj endpoint
  let _ : ObjectProperty.Small.{w} P := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{w} P := inferInstance
  let _ : IsAccessibleCategory.{w} C := ⟨χ₀, hχ₀, inferInstance⟩
  obtain ⟨μJ, hμJ, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let _ : Fact μJ.IsRegular := hμJ
  obtain ⟨ν, hν, hW⟩ := originalLocalArrowAccessibility d a S κLP
  let _ : Fact ν.IsRegular := hν
  let _ : (localEquivalences S).IsCardinalAccessible ν := hW
  let _ : IsAccessibleCategory.{w} (Arrow C) := ⟨χ₀, hχ₀, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (localEquivalences S).arrowObjectProperty.FullSubcategory :=
    ⟨ν, hν, inferInstance⟩
  let _ : Functor.IsAccessible.{w} (localEquivalences S).arrowObjectProperty.ι :=
    Functor.isAccessible_of_isCardinalAccessible _ ν
  let Upper := (χ₀.ord.ToType ⊕ χG.ord.ToType) ⊕ μJ.ord.ToType
  obtain ⟨μ, χ, hμ, hχ, hSharp, hUpper, _hArrow, hWμ, _hArrow', _hId, hι, _hIdP, _hιP⟩ :=
    CategoryTheory.Presentable.exists_inverseImage_comparison_rank
      (𝟭 (Arrow C)) (localEquivalences S).arrowObjectProperty.ι Upper
  let _ : Fact μ.IsRegular := hμ
  let _ : Fact χ.IsRegular := hχ
  let _ : IsCardinalAccessibleCategory (localEquivalences S).arrowObjectProperty.FullSubcategory μ := hWμ
  let _ : (localEquivalences S).arrowObjectProperty.ι.IsCardinalAccessible μ := hι
  have hχ₀ : χ₀ ≤ χ := by
    have h := hUpper.of_injective
      (fun x : χ₀.ord.ToType => (Sum.inl (Sum.inl x) : Upper))
      (Sum.inl_injective.comp Sum.inl_injective)
    exact (show χ₀ < χ from by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h).le
  have hχG : χG ≤ χ := by
    have h := hUpper.of_injective
      (fun x : χG.ord.ToType => (Sum.inl (Sum.inr x) : Upper))
      (Sum.inl_injective.comp Sum.inr_injective)
    exact (show χG < χ from by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h).le
  have hμJχ : μJ ≤ χ := by
    have h := hUpper.of_injective (Sum.inr : μJ.ord.ToType → Upper) Sum.inr_injective
    exact (show μJ < χ from by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h).le
  let _ : Nonempty χ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : χ.IsRegular).ne_zero
  let bottom : OrderBot χ.ord.ToType := WellFoundedLT.toOrderBot χ.ord.ToType
  refine ⟨χ, hχ, bottom, hLP.trans hχ₀, hκ.trans hχ₀,
    IsCardinalLocallyPresentable.of_le C hχ₀, ?_,
    Functor.isCardinalAccessible_of_le _ hχ₀,
    Functor.isCardinalAccessible_of_le _ hχ₀, ?_, ?_, hSmall, ?_, hDetection⟩
  · exact ⟨hSharp.isCardinalAccessibleCategory _, Functor.isCardinalAccessible_of_le _ hSharp.le⟩
  · intro i
    let _ : IsCardinalPresentable i.1.left χ₀ := (hI i).1
    let _ : IsCardinalPresentable i.1.right χ₀ := (hI i).2
    exact ⟨isCardinalPresentable_of_le _ hχ₀, isCardinalPresentable_of_le _ hχ₀⟩
  · intro j
    let _ : IsCardinalPresentable j.1.left μJ := hP _ (ObjectProperty.ofObj_apply endpoint (.inl j))
    let _ : IsCardinalPresentable j.1.right μJ := hP _ (ObjectProperty.ofObj_apply endpoint (.inr j))
    exact ⟨isCardinalPresentable_of_le _ hμJχ, isCardinalPresentable_of_le _ hμJχ⟩
  · intro k
    obtain ⟨hCof, hTF, hSource, hGenerator⟩ := hGenerators k
    let _ : IsCardinalPresentable (CombinatorialHomotopyGenerators.source d k) χG := hSource
    let _ : IsCardinalPresentable (CombinatorialHomotopyGenerators.generator d k) χG := hGenerator
    exact ⟨hCof, hTF, isCardinalPresentable_of_le _ hχG, isCardinalPresentable_of_le _ hχG⟩

include a κLP in
/-- The produced model's entire right class is the original local lifting
class, including arrows with arbitrary original endpoints. -/
theorem modelFibrations :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let F := localizedFibrations S
    letI : ModelCategory C := modelCategory d a S κLP
    fibrations C = F := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  change M.J.rlp = localizedFibrations S
  rw [M.fibrations_eq, hI]
  rfl

include a κLP in
/-- Localized trivial cofibrations are exactly original cofibrations that
satisfy all original derived local-equivalence tests. -/
theorem modelTrivialCofibrations :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let T := cofibrations C ⊓ localEquivalences S
    letI : ModelCategory C := modelCategory d a S κLP
    trivialCofibrations C = T := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  change d.I.rlp.llp ⊓ localEquivalences S = cofibrations C ⊓ localEquivalences S
  rw [hI]

include a κLP in
/-- The constructed model has precisely the original source trivial
fibrations, with the same complete raw arrow membership. -/
theorem modelTrivialFibrations :
    let originalTF := trivialFibrations C
    letI : ModelCategory C := modelCategory d a S κLP
    trivialFibrations C = originalTF := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  change M.J.rlp ⊓ localEquivalences S = trivialFibrations C
  rw [M.trivialFibrations_eq, d.I_rlp]

include a κLP in
/-- The full original I factory is installed in the produced model by
class identities alone; its middle functor and both maps are unchanged. -/
def localizedCofibrantFactors :
    letI : ModelCategory C := modelCategory d a S κLP
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  change FunctorialFactorizationData d.I.rlp.llp (M.J.rlp ⊓ localEquivalences S)
  exact (cofibrantFactors d).ofLE le_rfl (by rw [M.trivialFibrations_eq])

include a κLP in
/-- The actual Smith J factory supplies the second full factor record on
the produced model, preserving every original middle and square map. -/
def localizedFibrantFactors :
    letI : ModelCategory C := modelCategory d a S κLP
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let M := smithData d a S κLP
  change FunctorialFactorizationData (d.I.rlp.llp ⊓ localEquivalences S) M.J.rlp
  exact (fibrantFactors d a S κLP).ofLE (by rw [M.trivialCofibrations_eq]) le_rfl

include a κLP in
/-- The entire original first middle functor survives model construction. -/
theorem localizedCofibrantFactors_middle :
    (localizedCofibrantFactors d a S κLP).Z = d.cofibrantFactorizationData.Z := rfl

include a κLP in
/-- Both full original first-factor natural transformations survive. -/
theorem localizedCofibrantFactors_arrows :
    (localizedCofibrantFactors d a S κLP).i = d.cofibrantFactorizationData.i ∧
      (localizedCofibrantFactors d a S κLP).p = d.cofibrantFactorizationData.p := ⟨rfl, rfl⟩

include a κLP in
/-- The whole localized second middle functor remains its actual Smith
small-object functor at every original arrow. -/
theorem localizedFibrantFactors_middle :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let Z := (fibrantFactors d a S κLP).Z
    (localizedFibrantFactors d a S κLP).Z = Z := rfl

include a κLP in
/-- Both full localized second maps remain the actual original Smith
factor natural transformations. -/
theorem localizedFibrantFactors_arrows :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let i := (fibrantFactors d a S κLP).i
    let p := (fibrantFactors d a S κLP).p
    (localizedFibrantFactors d a S κLP).i = i ∧
      (localizedFibrantFactors d a S κLP).p = p := ⟨rfl, rfl⟩

include a κLP in
/-- The same common accessible rank supports both exact original generating
families on the constructed model, with all six small-object fields proved. -/
theorem generationAtCommonRank :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let I := d.I
    let J := (smithData d a S κLP).J
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular) (hbot : OrderBot χ.ord.ToType),
      letI : Fact χ.IsRegular := hχ
      letI : OrderBot χ.ord.ToType := hbot
      κLP ≤ χ ∧ κ ≤ χ ∧ (localEquivalences S).IsCardinalAccessible χ ∧
        letI : ModelCategory C := modelCategory d a S κLP
        ∃ g : CofibrantGenerationData C χ, g.I = I ∧ g.J = J := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  obtain ⟨χ, hχ, hbot, hLP, hκ, hC, hW, _hIZ, _hJZ, hI, hJ, _hSmall, _hGenerators, _hDetection⟩ :=
    existsCommonSourceRank d a S κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : OrderBot χ.ord.ToType := hbot
  let _ : IsCardinalLocallyPresentable C χ := hC
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let M := smithData d a S κLP
  obtain ⟨κJ, hκJ, hbotJ, hEligibleJ⟩ := M.J_smallObject.exists_cardinal
  let _ : Fact κJ.IsRegular := hκJ
  let _ : OrderBot κJ.ord.ToType := hbotJ
  let _ : M.J.IsSmall.{w} := hEligibleJ.isSmall
  have hIχ : d.I.IsCardinalForSmallObjectArgument χ := by
    refine { preservesColimit := ?_ }
    intro A B X Y i hi f hf
    let _ : IsCardinalPresentable A χ := (hI ⟨Arrow.mk i, hi⟩).1
    let _ : PreservesColimitsOfShape χ.ord.ToType (coyoneda.obj (.op A)) :=
      preservesColimitsOfShape_of_isCardinalPresentable A χ χ.ord.ToType
    infer_instance
  have hJχ : M.J.IsCardinalForSmallObjectArgument χ := by
    refine { preservesColimit := ?_ }
    intro A B X Y i hi f hf
    let _ : IsCardinalPresentable A χ := (hJ ⟨Arrow.mk i, hi⟩).1
    let _ : PreservesColimitsOfShape χ.ord.ToType (coyoneda.obj (.op A)) :=
      preservesColimitsOfShape_of_isCardinalPresentable A χ χ.ord.ToType
    infer_instance
  have hRight : d.I.rlp = M.J.rlp ⊓ localEquivalences S := M.trivialFibrations_eq.symm
  let originalI := d.I
  let originalJ := M.J
  let constructedModel := modelCategory d a S κLP
  refine ⟨χ, hχ, hbot, hLP, hκ, hW, ?_⟩
  let : ModelCategory C := constructedModel
  refine ⟨
    { I := originalI
      J := originalJ
      I_smallObject := hIχ
      J_smallObject := hJχ
      I_rlp := ?_
      J_rlp := ?_ }, rfl, rfl⟩
  · exact hRight
  · rfl

include a κLP in
/-- The original identity on the underlying category gives the actual
base-to-constructed adjunction, with both complete unchanged map functions. -/
def identityAdjunction :
    ExplicitModelIdentity.comparison (inferInstance : ModelCategory C) (modelCategory d a S κLP) ⊣
      ExplicitModelIdentity.comparison (modelCategory d a S κLP) (inferInstance : ModelCategory C) :=
  ExplicitModelIdentity.identityAdjunction _ _

include a κLP in
/-- Original cofibration preservation and derived local weak inclusion
prove that this actual identity adjunction is Quillen. -/
theorem identityAdjunction_isQuillen : (identityAdjunction d a S κLP).IsQuillenAdjunction := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  apply ExplicitModelIdentity.identityAdjunction_isQuillen
  · change cofibrations C = d.I.rlp.llp
    rw [d.I_rlp, trivialFibrations_llp]
  · change weakEquivalences C ≤ localEquivalences S
    rw [← GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
    exact CellularLocalizationFactorizations.baseWeak_le d S

include a κLP in
/-- Every whole original square acts by the same first middle map. -/
theorem localizedCofibrantFactors_map {F G : Arrow C} (φ : F ⟶ G) :
    (localizedCofibrantFactors d a S κLP).Z.map φ = d.cofibrantFactorizationData.Z.map φ := rfl

include a κLP in
/-- Every whole original square acts by the actual selected second middle map. -/
theorem localizedFibrantFactors_map {F G : Arrow C} (φ : F ⟶ G) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    (localizedFibrantFactors d a S κLP).Z.map φ = (fibrantFactors d a S κLP).Z.map φ := rfl

include a κLP in
/-- Both complete first-factor naturality squares retain their original maps. -/
theorem localizedCofibrantFactors_naturality {F G : Arrow C} (φ : F ⟶ G) :
    let out := localizedCofibrantFactors d a S κLP
    φ.left ≫ out.i.app G = out.i.app F ≫ out.Z.map φ ∧
      out.Z.map φ ≫ out.p.app G = out.p.app F ≫ φ.right := by
  exact ⟨(localizedCofibrantFactors d a S κLP).i.naturality φ,
    (localizedCofibrantFactors d a S κLP).p.naturality φ⟩

include a κLP in
/-- Both complete second-factor naturality squares retain the actual Smith maps. -/
theorem localizedFibrantFactors_naturality {F G : Arrow C} (φ : F ⟶ G) :
    let out := localizedFibrantFactors d a S κLP
    φ.left ≫ out.i.app G = out.i.app F ≫ out.Z.map φ ∧
      out.Z.map φ ≫ out.p.app G = out.p.app F ≫ φ.right := by
  exact ⟨(localizedFibrantFactors d a S κLP).i.naturality φ,
    (localizedFibrantFactors d a S κLP).p.naturality φ⟩

include a κLP in
/-- Both actual first factors compose to the full original arrow. -/
theorem localizedCofibrantFactors_fac (F : Arrow C) :
    (localizedCofibrantFactors d a S κLP).i.app F ≫
      (localizedCofibrantFactors d a S κLP).p.app F = F.hom :=
  (localizedCofibrantFactors d a S κLP).fac_app

include a κLP in
/-- Both actual second factors compose to the same full original arrow. -/
theorem localizedFibrantFactors_fac (F : Arrow C) :
    (localizedFibrantFactors d a S κLP).i.app F ≫
      (localizedFibrantFactors d a S κLP).p.app F = F.hom :=
  (localizedFibrantFactors d a S κLP).fac_app

include a κLP in
/-- A full source-derived model has all five exact original classes. The
chosen dictionary is the same one used by every generation and factor output. -/
theorem constructs :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let originalCof := cofibrations C
    let originalTF := trivialFibrations C
    let originalW := localEquivalences S
    let originalF := localizedFibrations S
    let originalTC := originalCof ⊓ originalW
    let constructed := modelCategory d a S κLP
    ∃ m : ModelCategory C, m = constructed ∧
      letI : ModelCategory C := m
      weakEquivalences C = originalW ∧ cofibrations C = originalCof ∧
        fibrations C = originalF ∧ trivialCofibrations C = originalTC ∧
        trivialFibrations C = originalTF := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact ⟨modelCategory d a S κLP, rfl, modelWeakEquivalences d a S κLP,
    modelCofibrations d a S κLP, modelFibrations d a S κLP,
    modelTrivialCofibrations d a S κLP, modelTrivialFibrations d a S κLP⟩

end HomotopicalAlgebra.CombinatorialSourceRecognition
