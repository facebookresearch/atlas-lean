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

import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalEquivalenceClosure
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.OriginalLocalMappingTests
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalReplacement
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith
import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing
import MathlibExt.AlgebraicTopology.ModelCategory.ContinuousCofibrationColimit

/-!
# Actual local trivial cofibrations and original cell attachments

The source mapping tests have an actual left lifting class, obtained from
the original tensor and cotensor adjunctions. Cofibrant source calculations
and the original left proper weak comparisons transfer these tests to the
derived local-equivalence class on every supplied original diagram.
The attachment and weak-class compatibility APIs reuse the generic cellular
results. Their historical action and cofibrancy inputs retain the same types
and positions; unused compatibility inputs are explicitly named as such.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe w wS v u

open CategoryTheory Limits
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.LocalTrivialCofibrationClosure

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)

/-- The original fixed-target precomposition map is a trivial fibration.
The opposite variance retains its exact original map. -/
def rawTests (Z : C) : MorphismProperty C :=
  (trivialCofibrations SSet.{v}ᵒᵖ).inverseImage
    (CompatibleCotensorFraming.mappingToOpposite (C := C) Z)

omit [ModelCategory C] in
/-- The test is the original simplicial precomposition trivial fibration,
at arbitrary original source and target endpoints. -/
theorem rawTests_iff {X Y : C} (f : X ⟶ Y) (Z : C) :
    rawTests Z f ↔ trivialFibrations SSet.{v}
      (((SimplicialCategory.sHomFunctor C).map f.op).app Z) := by
  dsimp only [rawTests, MorphismProperty.inverseImage]
  rw [trivialCofibrations_op]
  rfl

/-- Both complete original adjunctions identify the entire test class
with the left lifting class of the original cotensor-image arrows.
This constructs a class equality, without a localized WFS or model input. -/
theorem rawTests_eq_llp (Z : C) :
    rawTests Z = ((fibrations SSet.{v}ᵒᵖ).map
      (CompatibleCotensorFraming.cotensorAt a Z)).llp := by
  rw [rawTests, ← fibrations_llp SSet.{v}ᵒᵖ]
  let adj := CompatibleCotensorFraming.cotensorAdjunction a Z
  apply le_antisymm
  · intro X Y f hf A B p hp
    rcases hp with ⟨A', B', p', hp', ⟨e⟩⟩
    exact (HasLiftingProperty.iff_of_arrow_iso_right f e).mp
      ((adj.hasLiftingProperty_iff f p').mp (hf p' hp'))
  · intro X Y f hf A B p hp
    exact (adj.hasLiftingProperty_iff f p).mpr
      (hf ((CompatibleCotensorFraming.cotensorAt a Z).map p)
        ((fibrations SSet.{v}ᵒᵖ).map_mem_map _ p hp))

include a in
/-- Every supplied original pushout preserves the actual raw mapping test. -/
theorem rawTests_isStableUnderCobaseChange (Z : C) :
    (rawTests Z).IsStableUnderCobaseChange := by
  rw [rawTests_eq_llp a Z]
  infer_instance

include a in
/-- Original coproducts in every working size preserve the actual mapping test. -/
theorem rawTests_isStableUnderCoproducts (Z : C) :
    (rawTests Z).IsStableUnderCoproducts.{w} :=
  MorphismProperty.IsStableUnderCoproducts.of_llp_eq (rawTests Z)
    ((fibrations SSet.{v}ᵒᵖ).map (CompatibleCotensorFraming.cotensorAt a Z))
    (rawTests_eq_llp a Z).symm

include a in
/-- Every actual well ordered continuous transfinite composition preserves
the raw mapping test, including all original continuous limit stages. -/
theorem rawTests_isStableUnderTransfiniteComposition (Z : C) :
    (rawTests Z).IsStableUnderTransfiniteComposition.{w} :=
  MorphismProperty.IsStableUnderTransfiniteComposition.of_llp_eq (rawTests Z)
    ((fibrations SSet.{v}ᵒᵖ).map (CompatibleCotensorFraming.cotensorAt a Z))
    (rawTests_eq_llp a Z).symm

end HomotopicalAlgebra.LocalTrivialCofibrationClosure

namespace HomotopicalAlgebra.LocalTrivialCofibrationClosure

open GeneratedFunctorialReplacements GeneratedLocalReplacement

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {I : Type wS} (S : I → Arrow C)

/-- Compatibility form of generic local two-out-of-three, retaining the
historical simplicial action input and every original endpoint. -/
theorem nativeLocal_two_out_of_three
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty :=
  CellularLocalizationFactorizations.weak_twoOutOfThree d S

/-- Compatibility form of generic local retract closure for the complete
original Arrow, retaining the historical simplicial action input. -/
theorem nativeLocal_retracts
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (generatedLocalEquivalences d S).IsStableUnderRetracts :=
  CellularLocalizationFactorizations.weak_retracts d S

omit [SimplicialCategory C] in
/-- Every original base weak map is weak in the same generated local class. -/
theorem nativeBaseWeak_le : weakEquivalences C ≤ generatedLocalEquivalences d S :=
  CellularLocalizationFactorizations.baseWeak_le d S

include a in
/-- At genuinely cofibrant source endpoints, the exact raw mapping tests
give the original generated derived local-equivalence test. -/
theorem nativeLocal_of_rawTests {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : ∀ Z : C, generatedLocalFibrant d S Z → rawTests Z f) :
    generatedLocalEquivalences d S f := by
  intro Z hZ
  let _ : IsFibrant Z := hZ.1
  exact (nativePrecomp_isIso_iff_raw_weak d a f Z).mpr ((rawTests_iff f Z).mp (hf Z hZ)).2

variable [IsLeftProper C]

include a in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual original local cofibration has the exact raw trivial
mapping-fibration test, even at uncofibrant original endpoints. The original
Q/I relative factor, its actual pushout, and source left properness transfer
the cofibrant mapping lifts to the original arrow. -/
theorem rawTests_of_nativeLocal_cofibration {X Y : C} (f : X ⟶ Y) [Cofibration f]
    (hf : generatedLocalEquivalences d S f) (Z : C)
    (hZ : generatedLocalFibrant d S Z) : rawTests Z f := by
  let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty :=
    nativeLocal_two_out_of_three d a S
  let _ : IsFibrant Z := hZ.1
  let q : (Q d).obj X ⟶ X := (counit d).app X
  let c := d.cofibrantFactorizationData.factorizationData (q ≫ f)
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : Cofibration c.i := (cofibration_iff _).mpr c.hi
  let _ : IsCofibrant c.Z := isCofibrant_of_cofibration c.i
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (counit_weak d X)
  let _ : WeakEquivalence c.p := (weakEquivalence_iff _).mpr c.hp.2
  have hq : generatedLocalEquivalences d S q := nativeBaseWeak_le d S q (mem_weakEquivalences q)
  have hp : generatedLocalEquivalences d S c.p := nativeBaseWeak_le d S c.p c.hp.2
  have hi : generatedLocalEquivalences d S c.i := by
    apply (generatedLocalEquivalences d S).of_postcomp c.i c.p hp
    rw [c.fac]
    exact (generatedLocalEquivalences d S).comp_mem q f hq hf
  have hiRaw : rawTests Z c.i := by
    apply (rawTests_iff c.i Z).mpr
    exact ⟨CompatibleSimplicialMapping.sm7_fibration a
      (CompatibleSimplicialMapping.terminalCorner a c.i Z) c.hi
      ((fibration_iff _).mp hZ.1), (nativePrecomp_isIso_iff_raw_weak d a c.i Z).mp (hi Z hZ)⟩
  let R := (fibrations SSet.{v}ᵒᵖ).map (CompatibleCotensorFraming.cotensorAt a Z)
  have hiLift : R.llp c.i := by
    rw [← rawTests_eq_llp a Z]
    exact hiRaw
  rw [rawTests_eq_llp a Z]
  intro A B p hpR
  rcases hpR with ⟨A', B', p', hp', ⟨e⟩⟩
  let adj := CompatibleCotensorFraming.cotensorAdjunction a Z
  let _ : adj.IsQuillenAdjunction := CompatibleCotensorFraming.cotensor_isQuillen a Z
  let p₀ := (CompatibleCotensorFraming.cotensorAt a Z).map p'
  let _ : Fibration p₀ := (fibration_iff _).mpr
    ((inferInstance : adj.IsQuillenAdjunction).preservesFibrations _ hp')
  let _ : HasLiftingProperty c.i p₀ :=
    hiLift p₀ ((fibrations SSet.{v}ᵒᵖ).map_mem_map _ p' hp')
  have hLift : HasLiftingProperty f p₀ :=
    OriginalRelativeMapping.hasLiftingProperty_of_relative_factor q c.i c.p f c.fac p₀
  exact (HasLiftingProperty.iff_of_arrow_iso_right f e).mp hLift

end HomotopicalAlgebra.LocalTrivialCofibrationClosure

namespace HomotopicalAlgebra.LocalTrivialCofibrationClosure

open GeneratedFunctorialReplacements

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {I : Type wS} (S : I → Arrow C)

set_option backward.isDefEq.respectTransparency false in
/-- The generic cobase-change result retains this original compatibility
statement, including its historical cofibrant new-source hypothesis. -/
theorem nativeLocal_pushout_of_cofibrant_source
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C)
    {A B X P : C} (i : A ⟶ B) (g : A ⟶ X) (p : B ⟶ P) (q : X ⟶ P)
    (sq : IsPushout i g p q) [Cofibration i] [_hX : IsCofibrant X]
    (hi : generatedLocalEquivalences d S i) : generatedLocalEquivalences d S q :=
  (CellularLocalEquivalenceClosure.pushout_local d S sq ⟨mem_cofibrations i, hi⟩).2

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility form of generic cobase change for actual local cofibrations,
including every original uncofibrant endpoint and the supplied pushout. -/
theorem nativeLocal_of_isPushout
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C)
    {A B X P : C} (i : A ⟶ B) (g : A ⟶ X) (p : B ⟶ P) (q : X ⟶ P)
    (sq : IsPushout i g p q) [Cofibration i]
    (hi : generatedLocalEquivalences d S i) : generatedLocalEquivalences d S q :=
  (CellularLocalEquivalenceClosure.pushout_local d S sq ⟨mem_cofibrations i, hi⟩).2

/-- The exact intersection of original cofibrations with generated
derived local equivalences has cobase closure on all original pushouts. -/
theorem nativeCofibrations_cobase
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (cofibrations C ⊓ generatedLocalEquivalences d S).IsStableUnderCobaseChange :=
  CellularLocalEquivalenceClosure.cobaseChange d S

end HomotopicalAlgebra.LocalTrivialCofibrationClosure

namespace HomotopicalAlgebra.LocalTrivialCofibrationClosure

open OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {I : Type wS} (S : I → Arrow C)

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility form of generic continuous local closure for the original
bottom leg, retaining the supplied chain and its entire colimit cocone. -/
theorem nativeLocal_of_continuousCocone
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j →
      (cofibrations C ⊓ generatedLocalEquivalences d S) (F.map (homOfLE (Order.le_succ j))))
    (cF : Cocone F) (hcF : IsColimit cF) :
    generatedLocalEquivalences d S (cF.ι.app ⊥) :=
  (CellularLocalEquivalenceClosure.continuous_local d S F cF hcF hF).2

set_option backward.isDefEq.respectTransparency false in
/-- The exact actual intersection class is stable under every well ordered
continuous transfinite composition in the original working universe.
Its whole original endpoint Arrow is retained through the supplied bottom
isomorphism and actual colimit cocone. -/
theorem nativeCofibrations_transfinite
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (cofibrations C ⊓ generatedLocalEquivalences d S).IsStableUnderTransfiniteComposition.{w} :=
  CellularLocalEquivalenceClosure.transfiniteComposition d S

end HomotopicalAlgebra.LocalTrivialCofibrationClosure

namespace HomotopicalAlgebra.LocalTrivialCofibrationClosure

open GeneratedLocalReplacement

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {I : Type wS} (S : I → Arrow C)

/-- Compatibility form of generic coproduct closure in the original working
universe, retaining the historical simplicial action input. -/
theorem nativeCofibrations_coproducts
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    [IsLeftProper C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (cofibrations C ⊓ generatedLocalEquivalences d S).IsStableUnderCoproducts.{w} :=
  CellularLocalEquivalenceClosure.coproducts d S

omit [IsLeftProper C] in
/-- Both parts of the exact actual class preserve whole original Arrow
retracts, with all four original source/target morphisms. -/
theorem nativeCofibrations_retracts
    {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) (_a : CompatibleSimplicialMapping.Action C)
    {I : Type wS} (S : I → Arrow C) :
    (cofibrations C ⊓ generatedLocalEquivalences d S).IsStableUnderRetracts :=
  CellularLocalEquivalenceClosure.retracts d S

variable [MorphismProperty.HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [MorphismProperty.HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

include d a in
/-- Original cofibrations intersected with the exact original derived
`S`-local equivalences have cobase closure, with arbitrary original endpoints. -/
theorem originalCofibrations_cobase :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderCobaseChange := by
  rw [← generatedLocalEquivalences_eq_original d a S]
  exact CellularLocalEquivalenceClosure.cobaseChange d S

include d a in
/-- The exact original local trivial-cofibration class preserves all
original coproducts in the source working universe. -/
theorem originalCofibrations_coproducts :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderCoproducts.{w} := by
  rw [← generatedLocalEquivalences_eq_original d a S]
  exact CellularLocalEquivalenceClosure.coproducts d S

include d a in
/-- Full well ordered continuous transfinite closure of the exact original
local trivial-cofibration class, retaining all supplied endpoint Arrows and cocones. -/
theorem originalCofibrations_transfinite :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderTransfiniteComposition.{w} := by
  rw [← generatedLocalEquivalences_eq_original d a S]
  exact CellularLocalEquivalenceClosure.transfiniteComposition d S

omit [IsLeftProper C] in
/-- Whole original Arrow retract closure of the exact original class. -/
theorem originalCofibrations_retracts :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderRetracts := by
  let _ : (localEquivalences S).IsStableUnderRetracts := localEquivalences_isStableUnderRetracts S
  infer_instance

include d a in
/-- All four original cell-attachment closure conclusions hold for the
actual class, without any localized model, WFS, or closure input. -/
theorem originalCofibrations_closed :
    (cofibrations C ⊓ localEquivalences S).IsStableUnderCobaseChange ∧
    (cofibrations C ⊓ localEquivalences S).IsStableUnderCoproducts.{w} ∧
    (cofibrations C ⊓ localEquivalences S).IsStableUnderTransfiniteComposition.{w} ∧
    (cofibrations C ⊓ localEquivalences S).IsStableUnderRetracts :=
  ⟨originalCofibrations_cobase d a S, originalCofibrations_coproducts d a S,
    originalCofibrations_transfinite d a S, originalCofibrations_retracts S⟩

include d a in
/-- The actual original generator left class gives Smith's cobase field
for the exact original local weak class. -/
theorem originalSmith_cobase :
    (d.I.rlp.llp ⊓ localEquivalences S).IsStableUnderCobaseChange := by
  rw [d.I_rlp, trivialFibrations_llp]
  exact originalCofibrations_cobase d a S

include d a in
/-- The same original generator class gives Smith's full transfinite field
from actual source mapping and model lifting laws. -/
theorem originalSmith_transfinite :
    (d.I.rlp.llp ⊓ localEquivalences S).IsStableUnderTransfiniteComposition.{w} := by
  rw [d.I_rlp, trivialFibrations_llp]
  exact originalCofibrations_transfinite d a S

include d a in
/-- Every supplied original pushout preserves the entire actual intersection class. -/
theorem original_of_isPushout
    {A B X P : C} {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    (sq : IsPushout i g p q) (hi : (cofibrations C ⊓ localEquivalences S) i) :
    (cofibrations C ⊓ localEquivalences S) q := by
  let _ : (cofibrations C ⊓ localEquivalences S).IsStableUnderCobaseChange :=
    originalCofibrations_cobase d a S
  exact MorphismProperty.of_isPushout sq.flip hi

include d a in
/-- The actual map between any pair of colimiting original cofans is in
the exact class, with every original injection equation retained. -/
theorem original_of_cofans {K : Type w} {A B : K → C}
    (f : ∀ k, A k ⟶ B k) (hf : ∀ k, (cofibrations C ⊓ localEquivalences S) (f k))
    (cA : Cofan A) (cB : Cofan B) (hcA : IsColimit cA) (hcB : IsColimit cB)
    (t : cA.pt ⟶ cB.pt) (ht : ∀ k, cA.inj k ≫ t = f k ≫ cB.inj k) :
    (cofibrations C ⊓ localEquivalences S) t := by
  let _ : (cofibrations C ⊓ localEquivalences S).IsStableUnderCoproducts.{w} :=
    originalCofibrations_coproducts d a S
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := cofibrations C ⊓ localEquivalences S) (J := Discrete K)
    (Discrete.functor A) (Discrete.functor B) cA cB hcA hcB
    (Discrete.natTrans (fun k => f k.as)) (fun k => hf k.as) t (fun k => ht k.as)

include d a in
/-- Every original whole transfinite composition record has its exact
endpoint in the actual class. -/
theorem original_of_transfiniteComposition
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : C} {f : X ⟶ Y}
    (c : (cofibrations C ⊓ localEquivalences S).TransfiniteCompositionOfShape J f) :
    (cofibrations C ⊓ localEquivalences S) f := by
  let _ : (cofibrations C ⊓ localEquivalences S).IsStableUnderTransfiniteComposition.{w} :=
    originalCofibrations_transfinite d a S
  exact (cofibrations C ⊓ localEquivalences S).transfiniteCompositionsOfShape_le J _ c.mem

include d a in
/-- Every given original continuous chain and its actual endpoint cocone
give the exact original bottom leg in the class, with arbitrary endpoints. -/
theorem original_of_continuousCocone
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j →
      (cofibrations C ⊓ localEquivalences S) (F.map (homOfLE (Order.le_succ j))))
    (cF : Cocone F) (hcF : IsColimit cF) :
    (cofibrations C ⊓ localEquivalences S) (cF.ι.app ⊥) :=
  original_of_transfiniteComposition d a S
    { F := F, isoBot := Iso.refl _, incl := cF.ι, isColimit := hcF,
      fac := Category.id_comp _, map_mem := hF }

omit [IsLeftProper C] in
/-- The complete supplied Arrow retract retains the actual class at
arbitrary original source and target endpoints. -/
theorem original_of_arrowRetract
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (r : RetractArrow f g) (hg : (cofibrations C ⊓ localEquivalences S) g) :
    (cofibrations C ⊓ localEquivalences S) f := by
  let _ : (cofibrations C ⊓ localEquivalences S).IsStableUnderRetracts := originalCofibrations_retracts S
  exact (cofibrations C ⊓ localEquivalences S).of_retract r hg

end HomotopicalAlgebra.LocalTrivialCofibrationClosure
