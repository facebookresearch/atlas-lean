/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.MonoidWordPushoutEndpoint
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom
public import MathlibExt.CategoryTheory.MorphismProperty.MappedCoproducts
public import MathlibExt.CategoryTheory.SmallObject.Image
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Underlying cellular maps of associative free-algebra attachments

The original positive-degree word boundaries are tensors of trivial
cofibrations by arbitrary old coefficient objects. The actual word-stage
history therefore belongs to the source monoid-axiom closure. Sifted colimits
of genuine monoid diagrams retain their constructed underlying colimits.
-/

@[expose] public section

noncomputable section

universe w u v uJ vJ
universe uD vD

open CategoryTheory Limits MonoidalCategory MorphismProperty
open scoped MonoidalCategory

attribute [local instance] IsFiltered.isSifted


namespace HomotopicalAlgebra.MonoidTransfer

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- The actual tensor-word free functor, including its original degree-zero unit. -/
abbrev free : C ⥤ Mon C := TensorWord.tensorWordFunctor

/-- The generating family consists literally of the actual original free images. -/
abbrev freeGenerators (P : MorphismProperty C) : MorphismProperty (Mon C) := P.strictMap free

/-- The actual original free and forgetful functors have the full word adjunction. -/
abbrev adjunction : free (C := C) ⊣ Mon.forget C := TensorWord.tensorWordAdjunction

local instance : (free (C := C)).IsLeftAdjoint := ⟨Mon.forget C, ⟨adjunction⟩⟩

omit [HasColimitsOfSize.{w, w} C] in
/-- Native sifted colimits in `Mon C` preserve the complete underlying cocone. -/
theorem forgetPreservesSiftedColimits (J : Type uJ) [Category.{vJ} J] [IsSifted J]
    [HasColimitsOfShape J C] : PreservesColimitsOfShape J (Mon.forget C) where
  preservesColimit := fun {D} => by
    apply preservesColimit_of_preserves_colimit_cocone
      (MonoidWordPushout.MonSiftedColimit.isColimit D)
    change IsColimit (colimit.cocone (D ⋙ Mon.forget C))
    exact colimit.isColimit _

/-- Filtered preservation uses the actual word monad and the native monoid colimits. -/
theorem tensorWordMonadPreservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{w, w} (TensorWord.tensorWordMonad (C := C) : C ⥤ C) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesColimitsOfShape J (Mon.forget C) := forgetPreservesSiftedColimits J
    change PreservesColimitsOfShape J (free ⋙ Mon.forget C)
    infer_instance

/-- Every original ordinal endpoint and principal-segment colimit is preserved by forgetting. -/
theorem forgetPreservesWellOrderContinuous (J : Type w) [LinearOrder J] [OrderBot J] :
    PreservesWellOrderContinuousOfShape J (Mon.forget C) where
  preservesColimitsOfShape j hj := by
    let : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    exact forgetPreservesSiftedColimits (Set.Iio j)

variable [ModelCategory C]

/-- The source cellular closure keeps arbitrary tensor factors and the original cell universe. -/
abbrev tensorCellularClass : MorphismProperty C :=
  SmallObject.CellularNormalization.cellularClosure.{w, w} (tensorTrivialCofibrationsRight C)

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The actual empty coproducts supply all three cellular closure laws. -/
theorem tensorCellularClass_stable :
    (tensorCellularClass.{w} (C := C)).IsStableUnderCobaseChange ∧
      (tensorCellularClass.{w} (C := C)).IsStableUnderCoproducts.{w} ∧
      (tensorCellularClass.{w} (C := C)).IsStableUnderTransfiniteComposition.{w} := by
  let E : Discrete PEmpty.{w + 1} ⥤ C := Discrete.functor (fun i => i.elim)
  exact SmallObject.CellularNormalization.cellularClosure_stable.{w, w}
    (tensorTrivialCofibrationsRight C) (colimit.cocone E) (colimit.cocone E)
    (colimit.isColimit E) (colimit.isColimit E)

omit [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] in
/-- A whole original Arrow isomorphism transports the same cellular history. -/
theorem tensorCellularClass_respectsIso : (tensorCellularClass.{w} (C := C)).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro a b e ha
  obtain ⟨J, _, _, _, _, ⟨d⟩⟩ := (transfiniteCompositions_iff _ a.hom).mp ha
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ J b.hom ⟨d.ofArrowIso e⟩

local instance : (tensorCellularClass.{w} (C := C)).RespectsIso := tensorCellularClass_respectsIso

variable [IsClosedSymmetricMonoidalModelCategory C]

omit [HasColimitsOfSize.{w, w} C] in
/-- Positive iterated pushout products of original trivial cofibrations are trivial.
The degree-zero initial-to-unit arrow is not used in this claim. -/
theorem positiveIteratedPushoutProduct_trivial :
    ∀ (n : ℕ) {K L : Fin (n + 1) → C} (f : ∀ i, K i ⟶ L i),
      (∀ i, trivialCofibrations C (f i)) →
        trivialCofibrations C (FiniteCube.iteratedPushoutProduct f).hom := by
  intro n
  induction n with
  | zero =>
      intro K L f hf
      exact hf 0
  | succ n ih =>
      intro K L f hf
      exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
        (FiniteCube.iteratedPushoutProduct (fun i : Fin (n + 1) => f i.castSucc)).hom
        (f (Fin.last (n + 1))) (ih _ (fun i => hf i.castSucc)) (hf _).1

/-- Each actual original word-cell arrow lies in the full source monoid-axiom closure. -/
theorem wordCellClass_le_tensorCellularClass (A : Mon C) {K L : C} (f : K ⟶ L)
    (hf : trivialCofibrations C f) :
    MonoidWordPushout.wordCellClass A f ≤ tensorCellularClass.{w} (C := C) := by
  intro X Y g hg
  obtain ⟨n, ⟨e⟩⟩ := hg
  apply ((tensorCellularClass.{w} (C := C)).arrow_iso_iff e).mpr
  apply le_transfiniteCompositions
    ((tensorTrivialCofibrationsRight C).coproducts.{w}).pushouts
  apply le_pushouts
  apply le_coproducts
  exact whiskerRight_mem_tensorTrivialCofibrationsRight C _
    (positiveIteratedPushoutProduct_trivial (C := C) n (fun _ => f) (fun _ => hf))
    (FiniteCube.coefficientObj (fun _ : Fin ((n + 1) + 1) => A.X))

/-- A4's original countable cellular history proves membership for its actual old leg. -/
theorem originalFreeAttachment_underlying_cellular (A : Mon C) {K L : C} (f : K ⟶ L)
    (hf : trivialCofibrations C f) (a : free.obj K ⟶ A) :
    tensorCellularClass.{w} (C := C) (MonoidWordPushout.oldι A f a).hom := by
  let Q := tensorCellularClass.{w} (C := C)
  let : Q.IsStableUnderCobaseChange := tensorCellularClass_stable.{w}.1
  let : Q.IsStableUnderTransfiniteComposition.{w} := tensorCellularClass_stable.{w}.2.2
  let : Q.IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ (W := Q)
  let d := (MonoidWordPushout.originalWordCellComplex A f a).ofLE
    ((pushouts_le_iff (Q := Q)).mpr (wordCellClass_le_tensorCellularClass A f hf))
  exact Q.transfiniteCompositionsOfShape_le ℕ _ d.mem

/-- Any actual pushout of the original free trivial-cofibration arrow has a cellular old leg. -/
theorem freePushout_underlying_cellular {K L : C} (f : K ⟶ L)
    (hf : trivialCofibrations C f) {A B : Mon C} (a : free.obj K ⟶ A)
    (b : free.obj L ⟶ B) (g : A ⟶ B) (sq : IsPushout a (free.map f) g b) :
    tensorCellularClass.{w} (C := C) g.hom := by
  let e : MonoidWordPushout.freeAttachment A f a ≅ B :=
    (MonoidWordPushout.originalIsPushout A f a).isColimit.coconePointUniqueUpToIso sq.isColimit
  have he : MonoidWordPushout.oldι A f a ≫ e.hom = g := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (MonoidWordPushout.originalIsPushout A f a).isColimit sq.isColimit WalkingSpan.left
  let ae : Arrow.mk (MonoidWordPushout.oldι A f a) ≅ Arrow.mk g :=
    Arrow.isoMk (Iso.refl A) e (by
      change 𝟙 A ≫ g = MonoidWordPushout.oldι A f a ≫ e.hom
      exact (Category.id_comp g).trans he.symm)
  exact ((tensorCellularClass.{w} (C := C)).arrow_iso_iff ((Mon.forget C).mapArrow.mapIso ae)).mp
    (originalFreeAttachment_underlying_cellular A f hf a)

/-- An entire coproduct of actual free trivial-cofibration cells has the source tensor closure.
Only the free functor preserves the original coproduct; forgetting is applied after A4. -/
theorem freeTrivialCofibrationCoproductPushouts_underlying_cellular :
    ((freeGenerators (trivialCofibrations C)).coproducts.{w}).pushouts ≤
      (tensorCellularClass.{w} (C := C)).inverseImage (Mon.forget C) := by
  let : (trivialCofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← fibrations_llp C]
    infer_instance
  intro A B g hg
  obtain ⟨X, Y, q, a, b, hq, sq⟩ := hg
  have hFree := coproducts_strictMap_le_map (trivialCofibrations C) (free (C := C)) q hq
  obtain ⟨K, L, f, hf, ⟨χ⟩⟩ := hFree
  let s : free.obj K ≅ X := Arrow.leftFunc.mapIso χ
  let t : free.obj L ≅ Y := Arrow.rightFunc.mapIso χ
  have hχ : s.hom ≫ q = free.map f ≫ t.hom := χ.hom.w
  have sq' : IsPushout (s.hom ≫ a) (free.map f) g (t.hom ≫ b) :=
    sq.of_iso' s (Iso.refl A) t (Iso.refl B)
      (by simp) hχ (by simp) (by simp)
  exact freePushout_underlying_cellular f hf (s.hom ≫ a) (t.hom ≫ b) g sq'

omit [HasColimitsOfSize.{w, w} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original source fibration equality forces every original J-generator to be trivial. -/
theorem sourceJ_le_trivialCofibrations (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) : J ≤ trivialCofibrations C := by
  have h := J.le_llp_rlp
  rwa [hJ, fibrations_llp] at h

/-- Every original free-J coproduct attachment belongs to the source cellular closure. -/
theorem freeJCoproductPushouts_underlying_cellular (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) :
    ((freeGenerators J).coproducts.{w}).pushouts ≤
      (tensorCellularClass.{w} (C := C)).inverseImage (Mon.forget C) :=
  (pushouts_monotone (coproducts_monotone
    (monotone_strictMap free (sourceJ_le_trivialCofibrations J hJ)))).trans
      freeTrivialCofibrationCoproductPushouts_underlying_cellular

section OriginalCellHistory

variable (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
  {T : Type w} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {A B : Mon C} {f : A ⟶ B}
  (c : ((freeGenerators J).coproducts.{w}).pushouts.TransfiniteCompositionOfShape T f)

/-- Forget the original whole free-J cellular history into the derived source tensor closure. -/
def freeJCellMappedHistory :
    (tensorCellularClass.{w} (C := C)).TransfiniteCompositionOfShape T f.hom := by
  let : PreservesColimitsOfShape T (Mon.forget C) := forgetPreservesSiftedColimits T
  let : PreservesWellOrderContinuousOfShape T (Mon.forget C) := forgetPreservesWellOrderContinuous T
  exact (c.ofLE (freeJCoproductPushouts_underlying_cellular J hJ)).map

/-- The mapped cellular record has precisely the caller's original diagram followed by forgetting. -/
theorem freeJCellMappedHistory_diagram :
    (freeJCellMappedHistory J hJ c).F = c.F ⋙ Mon.forget C := rfl

/-- Every original endpoint cocone map is retained in the mapped tensor-cell history. -/
theorem freeJCellMappedHistory_incl (j : T) :
    (freeJCellMappedHistory J hJ c).incl.app j = (c.incl.app j).hom := by
  change (c.incl.app j).hom ≫ 𝟙 B.X = (c.incl.app j).hom
  exact Category.comp_id _

include J hJ c in
/-- The source tensor-cell closure contains the original whole free-J endpoint map. -/
theorem freeJCell_underlying_cellular : tensorCellularClass.{w} (C := C) f.hom := by
  let : (tensorCellularClass.{w} (C := C)).IsStableUnderTransfiniteComposition.{w} :=
    tensorCellularClass_stable.{w}.2.2
  exact (tensorCellularClass.{w} (C := C)).transfiniteCompositionsOfShape_le T _
    (freeJCellMappedHistory J hJ c).mem

variable [MonoidAxiom.{w} C]

include J hJ c in
/-- The original source monoid axiom makes every whole free-J-cell arrow weak. -/
theorem freeJCell_underlying_weak : weakEquivalences C f.hom :=
  MonoidAxiom.cellularClosure_le_weakEquivalences _ (freeJCell_underlying_cellular J hJ c)

end OriginalCellHistory

variable [MonoidAxiom.{w} C]

/-- The actual original cardinal cell complex is weak by its retained entire tensor-cell history. -/
theorem freeJRelativeCellComplex_underlying_weak (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C)
    {T : Type w} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Mon C} {f : A ⟶ B}
    (c : RelativeCellComplex.{w} (fun _ : T => (freeGenerators J).homFamily) f) :
    weakEquivalences C f.hom :=
  freeJCell_underlying_weak J hJ (c.transfiniteCompositionOfShape' (fun s => s.i.2))

/-- Retracting the actual original small-object left factor proves acyclicity of the full J-left class. -/
theorem freeJLeft_underlying_weak (J : MorphismProperty C) (hJ : J.rlp = fibrations C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(freeGenerators J).IsCardinalForSmallObjectArgument κ] :
    (freeGenerators J).rlp.llp ≤ (weakEquivalences C).inverseImage (Mon.forget C) := by
  apply rlp_llp_le_inverseImage_of_cardinal_cells (freeGenerators J) (weakEquivalences C) (Mon.forget C) κ
  intro A B f c
  exact freeJRelativeCellComplex_underlying_weak J hJ c









end HomotopicalAlgebra.MonoidTransfer
