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
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalReplacement
import MathlibExt.AlgebraicTopology.ModelCategory.WeakArrowAccessibility
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation

/-!
# Accessible factors for the original localization-generating family

The original small boundary family has a produced source rank. The existing
fixed-cardinal small-object accessibility theorems are applied to this family.
Its terminal factors, after the original generated Q, land in the original
derived-local fibrant objects. Accessibility of the full local-equivalence
class additionally requires the local weakness of these unit maps.
-/

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty Cardinal
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedLocalReplacement

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C) {K : Type wS}
  (S : K → Arrow C)

open GeneratedFunctorialReplacements

/-- Only source presentability and accessibility of the existing original I middle are recorded. -/
structure SourceRank (χ : Cardinal.{w}) [Fact χ.IsRegular] : Prop where
  locallyPresentable : IsCardinalLocallyPresentable C χ
  originalMiddle : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ
  endpoints : ∀ g : (generators d a S).toSet,
    IsCardinalPresentable g.1.left χ ∧ IsCardinalPresentable g.1.right χ

variable [Small.{w} K]

/-- Original generation and presentability produce a rank for the actual new boundary family.
The original κ factorizations and their middle functor are unchanged. -/
theorem exists_sourceRank (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular) (_ : OrderBot χ.ord.ToType),
      letI : Fact χ.IsRegular := hχ
      κLP ≤ χ ∧ κ ≤ χ ∧ SourceRank d a S χ := by
  obtain ⟨χ₀, hχ₀, _hω, hLP, hκ, hC, _hI, _hJ, hMiddle,
    _hJMiddle, _hIL, _hIR, _hJL, _hJR⟩ :=
    d.exists_common_factor_accessibility_cardinal κLP
  let _ : Fact χ₀.IsRegular := hχ₀
  let _ : IsCardinalLocallyPresentable C χ₀ := hC
  let _ : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ₀ := hMiddle
  let _ : IsAccessibleCategory.{w} C := ⟨χ₀, hχ₀, inferInstance⟩
  let _ : (generators d a S).IsSmall.{w} := generators_isSmall d a S
  let E := (generators d a S).toSet ⊕ (generators d a S).toSet
  let endpoint : E → C := fun e ↦ match e with
    | .inl g => g.1.left
    | .inr g => g.1.right
  let P : ObjectProperty C := ObjectProperty.ofObj endpoint
  let _ : ObjectProperty.Small.{w} P := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{w} P := inferInstance
  obtain ⟨μ, hμ, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let _ : Fact μ.IsRegular := hμ
  let Upper := χ₀.ord.ToType ⊕ μ.ord.ToType
  obtain ⟨χ, hχ, hUpper⟩ := HasCardinalLT.exists_regular_cardinal.{w} Upper
  let _ : Fact χ.IsRegular := ⟨hχ⟩
  have hχ₀ : χ₀ ≤ χ := by
    have h := hUpper.of_injective (Sum.inl : χ₀.ord.ToType → Upper) Sum.inl_injective
    exact (show χ₀ < χ from by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h).le
  have hμχ : μ ≤ χ := by
    have h := hUpper.of_injective (Sum.inr : μ.ord.ToType → Upper) Sum.inr_injective
    exact (show μ < χ from by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h).le
  have hEndpoint (e : E) : IsCardinalPresentable (endpoint e) χ := by
    let _ : IsCardinalPresentable (endpoint e) μ :=
      hP _ (ObjectProperty.ofObj_apply endpoint e)
    exact isCardinalPresentable_of_le _ hμχ
  have hne : Nonempty χ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero Fact.out
  let _ : Nonempty χ.ord.ToType := hne
  let bot : OrderBot χ.ord.ToType := WellFoundedLT.toOrderBot _
  refine ⟨χ, inferInstance, bot, hLP.trans hχ₀, hκ.trans hχ₀, ?_⟩
  exact {
    locallyPresentable := IsCardinalLocallyPresentable.of_le C hχ₀
    originalMiddle := Functor.isCardinalAccessible_of_le _ hχ₀
    endpoints := fun g ↦ ⟨hEndpoint (.inl g), hEndpoint (.inr g)⟩ }

section AtRank

variable (χ : Cardinal.{w}) [Fact χ.IsRegular] [OrderBot χ.ord.ToType]
  (rank : SourceRank d a S χ)

include rank in
/-- The actual source endpoints verify the small-object hypotheses at the produced rank. -/
theorem generators_smallObject_atRank : (generators d a S).IsCardinalForSmallObjectArgument χ := by
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let _ : (generators d a S).IsSmall.{w} := generators_isSmall d a S
  refine { preservesColimit := ?_ }
  intro A B X Y i hi f hf
  let _ : IsCardinalPresentable A χ := (rank.endpoints ⟨Arrow.mk i, hi⟩).1
  let _ : PreservesColimitsOfShape χ.ord.ToType (coyoneda.obj (.op A)) :=
    preservesColimitsOfShape_of_isCardinalPresentable A χ χ.ord.ToType
  infer_instance

/-- The full factor record is the same actual χ-length small-object construction. -/
def factorAtRank :
    FunctorialFactorizationData (generators d a S).rlp.llp (generators d a S).rlp := by
  let _ : (generators d a S).IsCardinalForSmallObjectArgument χ :=
    generators_smallObject_atRank d a S χ rank
  exact SmallObject.functorialFactorizationData (generators d a S) χ

/-- Accessibility of the original χ middle follows from the existing iteration theorem. -/
theorem factorAtRank_middle_accessible : (factorAtRank d a S χ rank).Z.IsCardinalAccessible χ := by
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let _ : (generators d a S).IsCardinalForSmallObjectArgument χ :=
    generators_smallObject_atRank d a S χ rank
  let _ : ∀ g : (generators d a S).toSet, IsCardinalPresentable g.1.left χ :=
    fun g ↦ (rank.endpoints g).1
  let _ : ∀ g : (generators d a S).toSet, IsCardinalPresentable g.1.right χ :=
    fun g ↦ (rank.endpoints g).2
  exact SmallObject.functorialFactorizationData_Z_isCardinalAccessible (generators d a S) χ χ

/-- The entire first-factor Arrow functor retains its original objects and square maps. -/
theorem factorAtRank_left_accessible :
    (factorAtRank d a S χ rank).originalLeftFactorFunctor.IsCardinalAccessible χ := by
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let _ : (factorAtRank d a S χ rank).Z.IsCardinalAccessible χ :=
    factorAtRank_middle_accessible d a S χ rank
  exact (factorAtRank d a S χ rank).originalLeftFactorFunctor_isCardinalAccessible χ

/-- The entire second-factor Arrow functor retains its original objects and square maps. -/
theorem factorAtRank_right_accessible :
    (factorAtRank d a S χ rank).originalRightFactorFunctor.IsCardinalAccessible χ := by
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let _ : (factorAtRank d a S χ rank).Z.IsCardinalAccessible χ :=
    factorAtRank_middle_accessible d a S χ rank
  exact (factorAtRank d a S χ rank).originalRightFactorFunctor_isCardinalAccessible χ

/-- Factor the same original terminal arrows using the same original small-object middle. -/
def replacementAtRank : C ⥤ C := terminal.arrowFunctor C ⋙ (factorAtRank d a S χ rank).Z

/-- The original first factor is the entire natural replacement unit. -/
def replacementUnitAtRank : 𝟭 C ⟶ replacementAtRank d a S χ rank where
  app X := (factorAtRank d a S χ rank).i.app (Arrow.mk (terminal.from X))
  naturality X Y f := by
    exact (factorAtRank d a S χ rank).i.naturality
      (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y))
        f (𝟙 (⊤_ C)) (by simp))

/-- The same original generated Q is followed by the actual terminal replacement. -/
def localReplacementAtRank : C ⥤ C := Q d ⋙ replacementAtRank d a S χ rank

/-- The complete unit retains the original Q and actual first-factor natural transformation. -/
def localUnitAtRank : Q d ⟶ localReplacementAtRank d a S χ rank :=
  (Q d).rightUnitor.inv ≫ Functor.whiskerLeft (Q d) (replacementUnitAtRank d a S χ rank)

/-- Every original input has the same actual terminal small-object middle after its original Q. -/
theorem localReplacementAtRank_obj (X : C) :
    (localReplacementAtRank d a S χ rank).obj X =
      (factorAtRank d a S χ rank).Z.obj (Arrow.mk (terminal.from ((Q d).obj X))) := rfl

/-- Every original input map retains the whole original square and generated middle map. -/
theorem localReplacementAtRank_map {X Y : C} (f : X ⟶ Y) :
    (localReplacementAtRank d a S χ rank).map f =
      (factorAtRank d a S χ rank).Z.map
        (Arrow.homMk (f := Arrow.mk (terminal.from ((Q d).obj X)))
          (g := Arrow.mk (terminal.from ((Q d).obj Y)))
          ((Q d).map f) (𝟙 (⊤_ C)) (by simp)) := rfl

/-- Every unit component is the original first factor at the original Q terminal arrow. -/
theorem localUnitAtRank_app (X : C) :
    (localUnitAtRank d a S χ rank).app X =
      (factorAtRank d a S χ rank).i.app (Arrow.mk (terminal.from ((Q d).obj X))) := by
  change (𝟙 ((Q d).obj X)) ≫
      (factorAtRank d a S χ rank).i.app (Arrow.mk (terminal.from ((Q d).obj X))) = _
  exact Category.id_comp _

/-- Every original localization replacement value is genuinely base-fibrant and derived-local. -/
theorem localReplacementAtRank_isLocal (X : C) :
    generatedLocalFibrant d S ((localReplacementAtRank d a S χ rank).obj X) := by
  apply generators_rlp_terminal_isLocal d a S
  have hp := (factorAtRank d a S χ rank).hp
    (Arrow.mk (terminal.from ((Q d).obj X)))
  have h : (factorAtRank d a S χ rank).p.app (Arrow.mk (terminal.from ((Q d).obj X))) =
      terminal.from ((localReplacementAtRank d a S χ rank).obj X) :=
    terminalIsTerminal.hom_ext _ _
  rwa [h] at hp

/-- The same original replacement functor is accessible at the produced source rank. -/
theorem replacementAtRank_accessible :
    (replacementAtRank d a S χ rank).IsCardinalAccessible χ := by
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let _ : (terminal.arrowFunctor C).IsCardinalAccessible χ :=
    terminal.arrowFunctor_isCardinalAccessible C χ
  let _ : (factorAtRank d a S χ rank).Z.IsCardinalAccessible χ :=
    factorAtRank_middle_accessible d a S χ rank
  change (terminal.arrowFunctor C ⋙ (factorAtRank d a S χ rank).Z).IsCardinalAccessible χ
  exact inferInstance

omit [Small.{w} K] [OrderBot χ.ord.ToType] in
/-- The original Q functor is accessible through the same original I middle. -/
theorem originalQ_atRank_accessible (rank : SourceRank d a S χ) : (Q d).IsCardinalAccessible χ := by
  let _ : d.cofibrantFactorizationData.Z.IsCardinalAccessible χ := rank.originalMiddle
  let _ : (initial.arrowFunctor C).IsCardinalAccessible χ :=
    initial.arrowFunctor_isCardinalAccessible C χ
  change (initial.arrowFunctor C ⋙ d.cofibrantFactorizationData.Z).IsCardinalAccessible χ
  exact inferInstance

/-- The actual Q-followed localization replacement is accessible at the same produced rank. -/
theorem localReplacementAtRank_accessible :
    (localReplacementAtRank d a S χ rank).IsCardinalAccessible χ := by
  let _ : (Q d).IsCardinalAccessible χ := originalQ_atRank_accessible d a S χ rank
  let _ : (replacementAtRank d a S χ rank).IsCardinalAccessible χ :=
    replacementAtRank_accessible d a S χ rank
  change (Q d ⋙ replacementAtRank d a S χ rank).IsCardinalAccessible χ
  exact inferInstance

/-- Every actual unit is a base cofibration by the original generated family. -/
theorem localUnitAtRank_cofibration (X : C) :
    cofibrations C ((localUnitAtRank d a S χ rank).app X) := by
  rw [localUnitAtRank_app]
  have hi := (factorAtRank d a S χ rank).hi
    (Arrow.mk (terminal.from ((Q d).obj X)))
  have h := (antitone_llp (antitone_rlp (generators_le_cofibrations d a S))) _ hi
  rw [cofibrations_rlp, trivialFibrations_llp] at h
  exact h

/-- Every actual replacement value remains cofibrant, with its original unit map. -/
theorem localReplacementAtRank_isCofibrant (X : C) :
    IsCofibrant ((localReplacementAtRank d a S χ rank).obj X) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : Cofibration ((localUnitAtRank d a S χ rank).app X) :=
    (cofibration_iff _).mpr (localUnitAtRank_cofibration d a S χ rank X)
  exact isCofibrant_of_cofibration ((localUnitAtRank d a S χ rank).app X)

/-- The actual χ unit on the original QX is a derived S-local equivalence.
Local cotensor-boundary lifting supplies every raw mapping-space boundary lift. -/
theorem localUnitAtRank_isLocalEquivalence (X : C) :
    generatedLocalEquivalences d S ((localUnitAtRank d a S χ rank).app X) := by
  intro Z hZ
  let _ : IsFibrant Z := hZ.1
  have hu : (generators d a S).rlp.llp ((localUnitAtRank d a S χ rank).app X) := by
    rw [localUnitAtRank_app]
    exact (factorAtRank d a S χ rank).hi (Arrow.mk (terminal.from ((Q d).obj X)))
  have hLift (n : ℕ) : HasLiftingProperty (SSet.boundary n).ι
      (((SimplicialCategory.sHomFunctor C).map
        ((localUnitAtRank d a S χ rank).app X).op).app Z) :=
    (boundaryLifting_iff_cotensorLifting a _ Z n).mpr
      (hu _ (cotensorBoundaryMap_generators_rlp d a S Z hZ n))
  have hRaw : trivialFibrations SSet.{v}
      (((SimplicialCategory.sHomFunctor C).map
        ((localUnitAtRank d a S χ rank).app X).op).app Z) :=
    (SSet.modelCategoryQuillen.boundaryLifting_iff_trivialFibration _).mp hLift
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsCofibrant ((localReplacementAtRank d a S χ rank).obj X) :=
    localReplacementAtRank_isCofibrant d a S χ rank X
  exact (nativePrecomp_isIso_iff_raw_weak d a _ Z).mpr hRaw.2

/-- The full native local-equivalence class is the inverse image of original base weak arrows
under the actual χ replacement. All original source endpoints are retained. -/
theorem generatedLocalEquivalences_eq_inverseImage :
    generatedLocalEquivalences d S =
      (weakEquivalences C).inverseImage (localReplacementAtRank d a S χ rank) := by
  let _ : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    d.hasFunctorialFactorizationCofibrationsTrivialFibrations
  let _ : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    d.hasFunctorialFactorizationTrivialCofibrationsFibrations
  let W := generatedLocalEquivalences d S
  let _ : W.HasTwoOutOfThreeProperty := by
    change (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty
    rw [generatedLocalEquivalences_eq_original d a S]
    exact localEquivalences_hasTwoOutOfThreeProperty S
  funext X Y f
  apply propext
  change W f ↔ weakEquivalences C ((localReplacementAtRank d a S χ rank).map f)
  have hQ : W ((Q d).map f) ↔ W f := by
    constructor
    · intro hf Z hZ
      exact (nativePrecomp_Q_iff d f Z).mp (hf Z hZ)
    · intro hf Z hZ
      exact (nativePrecomp_Q_iff d f Z).mpr (hf Z hZ)
  have hUnitX : W ((localUnitAtRank d a S χ rank).app X) :=
    localUnitAtRank_isLocalEquivalence d a S χ rank X
  have hUnitY : W ((localUnitAtRank d a S χ rank).app Y) :=
    localUnitAtRank_isLocalEquivalence d a S χ rank Y
  have hNat := (localUnitAtRank d a S χ rank).naturality f
  have hL : W ((Q d).map f) ↔ W ((localReplacementAtRank d a S χ rank).map f) := by
    constructor
    · intro hf
      apply W.of_precomp _ _ hUnitX
      rw [← hNat]
      exact W.comp_mem _ _ hf hUnitY
    · intro hf
      apply W.of_postcomp _ _ hUnitY
      rw [hNat]
      exact W.comp_mem _ _ hUnitX hf
  exact (hQ.symm.trans hL).trans
    (generatedLocalEquivalences_weak_iff_of_local d S
      ((localReplacementAtRank d a S χ rank).map f)
      (localReplacementAtRank_isLocal d a S χ rank X)
      (localReplacementAtRank_isLocal d a S χ rank Y))

section OriginalClass

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The original chosen derived S-local class is exactly the inverse image under the actual
source-constructed replacement, for all original arrows and commuting squares. -/
theorem originalLocalEquivalences_eq_inverseImage :
    localEquivalences S =
      (weakEquivalences C).inverseImage (localReplacementAtRank d a S χ rank) :=
  (generatedLocalEquivalences_eq_original d a S).symm.trans
    (generatedLocalEquivalences_eq_inverseImage d a S χ rank)

/-- The membership equality is on the original full Arrow category. -/
theorem originalLocalArrowProperty_eq_inverseImage :
    (localEquivalences S).arrowObjectProperty =
      (weakEquivalences C).arrowObjectProperty.inverseImage
        (localReplacementAtRank d a S χ rank).mapArrow := by
  rw [originalLocalEquivalences_eq_inverseImage d a S χ rank]
  rfl

/-- The full-subcategory comparison changes only membership proofs of the original arrows. -/
def originalLocalArrowInverseImageEquivalence :
    (localEquivalences S).arrowObjectProperty.FullSubcategory ≌
      ((weakEquivalences C).arrowObjectProperty.inverseImage
        (localReplacementAtRank d a S χ rank).mapArrow).FullSubcategory :=
  (CategoryTheory.Equivalence.refl : Arrow C ≌ Arrow C).congrFullSubcategory
    (originalLocalArrowProperty_eq_inverseImage d a S χ rank).symm

/-- Every whole original Arrow object is retained by the comparison. -/
theorem originalLocalArrowInverseImageEquivalence_obj_function :
    (fun A : (localEquivalences S).arrowObjectProperty.FullSubcategory ↦
      ((originalLocalArrowInverseImageEquivalence d a S χ rank).functor.obj A).obj) =
      (fun A ↦ A.obj) := rfl

/-- Every whole original commuting square is retained by the comparison. -/
theorem originalLocalArrowInverseImageEquivalence_map_function :
    (fun (A B : (localEquivalences S).arrowObjectProperty.FullSubcategory) (f : A ⟶ B) ↦
      ((originalLocalArrowInverseImageEquivalence d a S χ rank).functor.map f).hom) =
      (fun (A B : (localEquivalences S).arrowObjectProperty.FullSubcategory) (f : A ⟶ B) ↦ f.hom) := rfl

/-- The comparison followed by the original inverse-image inclusion is the original inclusion. -/
def originalLocalArrowInverseImageEquivalenceCompInclusion :
    (originalLocalArrowInverseImageEquivalence d a S χ rank).functor ⋙
      ((weakEquivalences C).arrowObjectProperty.inverseImage
        (localReplacementAtRank d a S χ rank).mapArrow).ι ≅
      (localEquivalences S).arrowObjectProperty.ι := Iso.refl _

end OriginalClass

end AtRank

section FullArrowAccessibility

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

include d a in
/-- The full original derived-local-equivalence category and its original inclusion have
a genuinely produced regular accessibility rank. No desired accessibility is supplied. -/
theorem originalLocalEquivalences_accessible (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular), (localEquivalences S).IsCardinalAccessible ν := by
  obtain ⟨χ, hχ, hbot, _hLP, _hκ, rank⟩ := exists_sourceRank d a S κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : OrderBot χ.ord.ToType := hbot
  let _ : IsCardinalLocallyPresentable C χ := rank.locallyPresentable
  let L := localReplacementAtRank d a S χ rank
  let _ : L.IsCardinalAccessible χ := localReplacementAtRank_accessible d a S χ rank
  let _ : (L.mapArrow ⋙ Arrow.leftFunc).IsCardinalAccessible χ := by
    change (Arrow.leftFunc ⋙ L).IsCardinalAccessible χ
    infer_instance
  let _ : (L.mapArrow ⋙ Arrow.rightFunc).IsCardinalAccessible χ := by
    change (Arrow.rightFunc ⋙ L).IsCardinalAccessible χ
    infer_instance
  let _ : L.mapArrow.IsCardinalAccessible χ := Functor.isCardinalAccessible_toArrow _ χ
  let _ : Functor.IsAccessible.{w} L.mapArrow := Functor.isAccessible_of_isCardinalAccessible _ χ
  let _ : IsAccessibleCategory.{w} C := ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow C) := ⟨κLP, inferInstance, inferInstance⟩
  obtain ⟨νW, hνW, hW⟩ := d.weakEquivalences_accessible κLP
  let _ : Fact νW.IsRegular := hνW
  let _ : (weakEquivalences C).IsCardinalAccessible νW := hW
  let _ : IsAccessibleCategory.{w} (weakEquivalences C).arrowObjectProperty.FullSubcategory :=
    ⟨νW, inferInstance, inferInstance⟩
  let _ : Functor.IsAccessible.{w} (weakEquivalences C).arrowObjectProperty.ι :=
    Functor.isAccessible_of_isCardinalAccessible _ νW
  obtain ⟨ν, hν, hCategory, hInclusion⟩ :=
    CategoryTheory.Presentable.inverseImage_accessible L.mapArrow
      (weakEquivalences C).arrowObjectProperty
  let _ : Fact ν.IsRegular := hν
  have hEq := originalLocalArrowProperty_eq_inverseImage d a S χ rank
  refine ⟨ν, hν, ?_⟩
  constructor
  · rw [hEq]
    exact hCategory
  · rw [hEq]
    exact hInclusion

include d a in
/-- Accessibility of the desired original local class is an output of the original source construction. -/
theorem originalLocalEquivalences_isAccessible (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] : (localEquivalences S).IsAccessible.{w} :=
  ⟨originalLocalEquivalences_accessible d a S κLP⟩

include d a in
/-- Both the entire original full subcategory and the entire original inclusion share the produced rank. -/
theorem originalLocalArrowCategory_accessible (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      IsCardinalAccessibleCategory (localEquivalences S).arrowObjectProperty.FullSubcategory ν ∧
        (localEquivalences S).arrowObjectProperty.ι.IsCardinalAccessible ν := by
  obtain ⟨ν, hν, hW⟩ := originalLocalEquivalences_accessible d a S κLP
  let _ : Fact ν.IsRegular := hν
  let _ : (localEquivalences S).IsCardinalAccessible ν := hW
  exact ⟨ν, hν, inferInstance, inferInstance⟩

end FullArrowAccessibility

end HomotopicalAlgebra.GeneratedLocalReplacement
