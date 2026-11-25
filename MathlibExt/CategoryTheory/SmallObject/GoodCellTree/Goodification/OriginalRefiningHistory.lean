/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSuccessorPreservation
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPrefixUnion
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-!
# Genuine complete original refining histories

The original empty-root seed, actual predecessor-local compact successors and literal original
BEFORE unions construct the whole compatible history by well-order induction. Every original
lower universal property, all old maps and the actual original source/cell laws are retained.
The original root, total carrier and endpoint have no compactness bound.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

theorem after_monotone : Monotone (after (P := P)) := by
  intro i j hij p hp
  exact hp.trans hij

theorem after_into_before (j : OriginalCellWellOrderEnumeration.Index (P := P))
    (i : Set.Iio j) : after i.1 ≤ before j := by
  intro p hp
  change labels p < j
  exact hp.trans_lt (show i.1 < j from i.2)

theorem priorPrefixes_directed (j : OriginalCellWellOrderEnumeration.Index (P := P))
    (i k : Set.Iio j) : ∃ l : Set.Iio j, i ≤ l ∧ k ≤ l :=
  ⟨max i k, le_max_left _ _, le_max_right _ _⟩

theorem priorPrefixes_cover (j : OriginalCellWellOrderEnumeration.Index (P := P))
    (p : before j) : ∃ i : Set.Iio j, p.1 ∈ after i.1 := by
  refine ⟨⟨labels p.1, p.2⟩, ?_⟩
  change labels p.1 ≤ labels p.1
  exact le_rfl

variable (j : OriginalCellWellOrderEnumeration.Index (P := P))
  (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
    historyFunctor O M chi (after (P := P)) after_monotone).sections)

/-- The actual compatible predecessor section supplies its own original AFTER prefix. -/
def priorState (i : Set.Iio j) : Prefix O M chi (after i.1) :=
  previousPrefix O M chi (after (P := P)) after_monotone j x i

omit [HasColimitsOfSize.{w, w} C] in
theorem priorState_preserves (i k : Set.Iio j) (hik : i ≤ k) :
    Preserves O M chi (after_monotone hik) (priorState O M chi j x i) (priorState O M chi j x k) :=
  previousPrefix_preserves O M chi (after (P := P)) after_monotone j x i k hik

/-- For a fixed well-founded cell tree `O`, chosen lower-set colimits `M`
and regular `chi`, the compatible section `x` over the strictly earlier
stages `Set.Iio j` determines the prefix on `before j`.

Each `i < j` contributes the prefix `priorState … i` on `after i` read off that
section, so the inputs are that section's own earlier prefixes rather than
unrelated predecessor data. Their supports `after i` are monotone; the
prefix fields are preserved along every `i ≤ k`, admit a common upper stage
below `j` for any two indices, and cover `before j`. Thus `partialLimitPrefix`
assembles them using the working-size colimits of `C`. When no stage precedes
`j`, `before j = ⊥` and the designated empty prefix is returned. -/
def historyBefore : Prefix O M chi (before j) := by
  classical
  by_cases hI : Nonempty (Set.Iio j)
  · letI := hI
    exact partialLimitPrefix O M chi (before j) (fun i : Set.Iio j => after i.1)
      (after_into_before j) (fun _ _ h => after_monotone h)
      (priorState O M chi j x)
      (priorState_preserves O M chi j x)
      (priorPrefixes_directed j) (priorPrefixes_cover j)
  · have hb : before j = (⊥ : LowerSet P) := by
      apply SetLike.coe_injective
      apply Set.ext
      intro p
      constructor
      · intro hp
        exact False.elim (hI ⟨⟨labels p, hp⟩⟩)
      · exact False.elim
    exact hb.symm ▸ emptyPrefix O M chi

theorem historyBefore_preserves (i : Set.Iio j) :
    Preserves O M chi (after_into_before j i) (priorState O M chi j x i)
      (historyBefore O M chi j x) := by
  have hI : Nonempty (Set.Iio j) := ⟨i⟩
  unfold historyBefore
  rw [dite_eq_left hI]
  exact partialLimitPrefix_preserves O M chi (before j) (fun i : Set.Iio j => after i.1)
    (after_into_before j) (fun _ _ h => after_monotone h)
    (priorState O M chi j x)
    (priorState_preserves O M chi j x)
    (priorPrefixes_directed j) (priorPrefixes_cover j) i

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)
  (j : OriginalCellWellOrderEnumeration.Index (P := P))
  (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
    historyFunctor O M chi (after (P := P)) after_monotone).sections)

/-- The original cell and compact capture construct the next complete AFTER prefix. -/
def historyAfter : Prefix O M chi (after j) := by
  letI := hSource (labels.symm j)
  letI := hTarget (labels.symm j)
  let r := historyBefore O M chi j x
  letI := r.ord
  letI : Preorder (before j) := r.ord.toPreorder
  let N := r.tree.lowerData
  exact successorPrefix O M chi j r N

theorem historyAfter_preserves (i : Set.Iio j) :
    Preserves O M chi (after_monotone i.2.le) (priorState O M chi j x i)
      (historyAfter O M chi hSource hTarget j x) := by
  let _ := hSource (labels.symm j)
  let _ := hTarget (labels.symm j)
  let r := historyBefore O M chi j x
  let _ := r.ord
  let _ : Preorder (before j) := r.ord.toPreorder
  exact Preserves.trans O M chi (historyBefore_preserves O M chi j x i)
    (successorPrefix_preserves O M chi j r r.tree.lowerData)

/-- The stored original state is unchanged at every earlier actual index. -/
def extendedState (i : OriginalCellWellOrderEnumeration.Index (P := P)) (hij : i ≤ j) :
    Prefix O M chi (after i) :=
  if h : i < j then priorState O M chi j x ⟨i, h⟩
  else (congrArg after (le_antisymm hij (le_of_not_gt h))).symm ▸
    historyAfter O M chi hSource hTarget j x

theorem extendedState_lt (i : OriginalCellWellOrderEnumeration.Index (P := P))
    (hi : i < j) : extendedState O M chi hSource hTarget j x i hi.le =
      priorState O M chi j x ⟨i, hi⟩ := by
  unfold extendedState
  rw [dite_eq_left hi]

theorem extendedState_self : extendedState O M chi hSource hTarget j x j le_rfl =
    historyAfter O M chi hSource hTarget j x := by
  unfold extendedState
  rw [dite_eq_right (lt_irrefl j)]

/-- The entire original history extends by the constructed complete successor. -/
def extendedHistory : History O M chi (after (P := P)) after_monotone j where
  state := extendedState O M chi hSource hTarget j x
  preserves i k hik hkj := by
    by_cases hk : k < j
    · have hi : i < j := hik.trans_lt hk
      rw [extendedState_lt O M chi hSource hTarget j x i hi,
        extendedState_lt O M chi hSource hTarget j x k hk]
      exact priorState_preserves O M chi j x ⟨i, hi⟩ ⟨k, hk⟩ hik
    · have hkj' : k = j := le_antisymm hkj (le_of_not_gt hk)
      subst k
      by_cases hi : i < j
      · rw [extendedState_lt O M chi hSource hTarget j x i hi,
          extendedState_self O M chi hSource hTarget j x]
        exact historyAfter_preserves O M chi hSource hTarget j x ⟨i, hi⟩
      · have hij' : i = j := le_antisymm hik (le_of_not_gt hi)
        subst i
        exact Preserves.refl O M chi _

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem History.ext_state {J : Type w} [Preorder J]
    (S : J → LowerSet P) (hMono : Monotone S) (j : J)
    (H H' : History O M chi S hMono j)
    (h : ∀ i : J, ∀ hi : i ≤ j, H.state i hi = H'.state i hi) : H = H' := by
  cases H with
  | mk state preserves =>
    cases H' with
    | mk state' preserves' =>
      have hs : state = state' := funext (fun i => funext (fun hi => h i hi))
      cases hs
      rfl

theorem extendedHistory_restrict (i : OriginalCellWellOrderEnumeration.Index (P := P))
    (hi : i < j) :
    (extendedHistory O M chi hSource hTarget j x).restrict O M chi (after (P := P))
        after_monotone hi.le = x.val (op ⟨i, hi⟩) := by
  apply History.ext_state O M chi (after (P := P)) after_monotone i
  intro k hki
  have hk : k < j := hki.trans_lt hi
  change extendedState O M chi hSource hTarget j x k (hki.trans hi.le) = _
  rw [extendedState_lt O M chi hSource hTarget j x k hk]
  have hx := x.property (homOfLE hki : (⟨k, hk⟩ : Set.Iio j) ⟶ ⟨i, hi⟩).op
  exact congrArg (fun H : History O M chi (after (P := P)) after_monotone k =>
    H.state k (le_refl k)) hx.symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

omit pOrder [WellFoundedLT P] in
/-- The actual original enumeration supplies its indexNonempty structure. -/
theorem indexNonempty : Nonempty (OriginalCellWellOrderEnumeration.Index (P := P)) :=
  (inferInstance : Nonempty P).map (labels (P := P))

omit [Nonempty P] in
/-- The actual original enumeration supplies its indexWellFounded structure. -/
theorem indexWellFounded : WellFoundedLT (OriginalCellWellOrderEnumeration.Index (P := P)) :=
  enumeration_wellFounded

/-- The actual original enumeration supplies its indexOrderBot structure. -/
@[instance_reducible]
noncomputable def indexOrderBot : OrderBot (OriginalCellWellOrderEnumeration.Index (P := P)) := by
  letI := indexNonempty (P := P)
  letI := indexWellFounded (P := P)
  exact WellFoundedLT.toOrderBot _

/-- The actual original enumeration supplies its indexSuccOrder structure. -/
@[instance_reducible]
noncomputable def indexSuccOrder : SuccOrder (OriginalCellWellOrderEnumeration.Index (P := P)) := by
  letI := indexNonempty (P := P)
  letI := indexWellFounded (P := P)
  exact SuccOrder.ofLinearWellFoundedLT _

attribute [local instance] indexNonempty indexWellFounded indexOrderBot indexSuccOrder

/-- Literal restrictions of an actual history supply successor predecessor sections. -/
def predecessorSections (j : OriginalCellWellOrderEnumeration.Index (P := P)) (hj : ¬ IsMax j)
    (H : History O M chi (after (P := P)) after_monotone j) :
    ((OrderHom.Subtype.val (· ∈ Set.Iio (Order.succ j))).monotone.functor.op ⋙
      historyFunctor O M chi (after (P := P)) after_monotone).sections where
  val i := H.restrict O M chi (after (P := P)) after_monotone
    ((Order.lt_succ_iff_of_not_isMax hj).1 i.unop.2)
  property := by
    intro i k f
    exact History.restrict_comp O M chi (after (P := P)) after_monotone
      (leOfHom f.unop) ((Order.lt_succ_iff_of_not_isMax hj).1 i.unop.2) H

/-- Actual successor and limit lifts form the genuine inverse-system induction data. -/
def historyInductionData :
    (historyFunctor O M chi (after (P := P)) after_monotone).WellOrderInductionData where
  succ j hj H := extendedHistory O M chi hSource hTarget (Order.succ j)
    (predecessorSections O M chi j hj H)
  map_succ j hj H := by
    exact extendedHistory_restrict O M chi hSource hTarget (Order.succ j)
      (predecessorSections O M chi j hj H) j (Order.lt_succ_of_not_isMax hj)
  lift j _ x := extendedHistory O M chi hSource hTarget j x
  map_lift j _ x i hi := extendedHistory_restrict O M chi hSource hTarget j x i hi

/-- The original bottom index has its genuine empty predecessor section. -/
def emptyPredecessorSections :
    ((OrderHom.Subtype.val (· ∈ Set.Iio
                               (⊥ : OriginalCellWellOrderEnumeration.Index
                                 (P := P)))).monotone.functor.op ⋙
      historyFunctor O M chi (after (P := P)) after_monotone).sections where
  val i := False.elim (not_lt_bot (show i.unop.1 < ⊥ from i.unop.2))
  property := by
    intro i k f
    exact False.elim (not_lt_bot (show i.unop.1 < ⊥ from i.unop.2))

/-- The seed is constructed from the actual empty-root predecessor data and original cell. -/
def historySeed : History O M chi (after (P := P)) after_monotone ⊥ :=
  extendedHistory O M chi hSource hTarget ⊥ (emptyPredecessorSections O M chi)

/-- Well-order induction constructs the entire compatible original history. -/
def fullHistorySections :
    (historyFunctor O M chi (after (P := P)) after_monotone).sections :=
  (historyInductionData O M chi hSource hTarget).sectionsMk (historySeed O M chi hSource hTarget)

end

end CategoryTheory.SmallObject.OriginalGoodification

attribute [local instance]
  CategoryTheory.SmallObject.OriginalGoodification.indexNonempty
  CategoryTheory.SmallObject.OriginalGoodification.indexWellFounded
  CategoryTheory.SmallObject.OriginalGoodification.indexOrderBot
  CategoryTheory.SmallObject.OriginalGoodification.indexSuccOrder


namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- The constructed complete history supplies its actual full AFTER state. -/
def fullAfterPrefix (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    Prefix O M chi (after j) :=
  ((fullHistorySections O M chi hSource hTarget).val (op j)).state j le_rfl

theorem fullAfterPrefix_preserves (i j : OriginalCellWellOrderEnumeration.Index (P := P))
    (hij : i ≤ j) :
    Preserves O M chi (after_monotone hij)
      (fullAfterPrefix O M chi hSource hTarget i) (fullAfterPrefix O M chi hSource hTarget j) := by
  let x := fullHistorySections O M chi hSource hTarget
  have hx : (x.val (op j)).restrict O M chi (after (P := P)) after_monotone hij = x.val (op i) :=
    x.property (homOfLE hij : i ⟶ j).op
  have hs : (x.val (op j)).state i hij = (x.val (op i)).state i le_rfl :=
    congrArg (fun H : History O M chi (after (P := P)) after_monotone i => H.state i le_rfl) hx
  have h := (x.val (op j)).preserves i j hij le_rfl
  rw [hs] at h
  exact h

omit [Nonempty P] in
theorem fullAfter_cover (p : P) :
    ∃ j : OriginalCellWellOrderEnumeration.Index (P := P), p ∈ after j := by
  refine ⟨labels p, ?_⟩
  change labels p ≤ labels p
  exact le_rfl

/-- The actual original AFTER history glues on the entire original carrier. -/
def fullOriginalPrefix : Prefix O M chi (⊤ : LowerSet P) :=
  limitPrefix O M chi (after (P := P)) after_monotone
    (fullAfterPrefix O M chi hSource hTarget)
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩)
    fullAfter_cover
    (fullAfterPrefix_preserves O M chi hSource hTarget)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- The whole original prefix producer also retains the arbitrary-root empty carrier. -/
def fullOriginalPrefixAll : Prefix O M chi (⊤ : LowerSet P) := by
  classical
  by_cases hP : Nonempty P
  · letI := hP
    exact fullOriginalPrefix O M chi hSource hTarget
  · exact {
      ord := inferInstance
      below := fun _ _ h => h
      tree := CellTreeLowerRestriction.tree O M ⊤
      labels := fun _ => rfl
      comparison := OriginalLowerRestrictionComparison.comparison O M ⊤
      good := {
        presentable_source a := False.elim (hP ⟨a.1⟩)
        presentable_target a := False.elim (hP ⟨a.1⟩)
        predecessor_lt a := False.elim (hP ⟨a.1⟩) }
      lowerUP := fun D _ => OriginalLowerRestrictionComparison.lowerIsColimit O M ⊤ D le_top }

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- The actual unique well-order extension retains its original stored history. -/
def fullExtension (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    (historyInductionData O M chi hSource hTarget).Extension
        (historySeed O M chi hSource hTarget) j := by
  letI := indexNonempty (P := P)
  letI := indexWellFounded (P := P)
  letI := indexOrderBot (P := P)
  letI := indexSuccOrder (P := P)
  let d := historyInductionData O M chi hSource hTarget
  let seed := historySeed O M chi hSource hTarget
  exact @Functor.WellOrderInductionData.Extension.instUnique
    (OriginalCellWellOrderEnumeration.Index (P := P))
    (inferInstance : LinearOrder (OriginalCellWellOrderEnumeration.Index (P := P)))
    (indexSuccOrder (P := P)) (historyFunctor O M chi after after_monotone)
    d (indexOrderBot (P := P)) seed (indexWellFounded (P := P)) j |>.default

theorem fullHistory_value (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    (fullHistorySections O M chi hSource hTarget).val (op j) =
      (fullExtension O M chi hSource hTarget j).val := by
  let _ := indexNonempty (P := P)
  let _ := indexWellFounded (P := P)
  let _ := indexOrderBot (P := P)
  let _ := indexSuccOrder (P := P)
  rfl

omit [Nonempty P] in
theorem historyAfter_new_cell (j : OriginalCellWellOrderEnumeration.Index (P := P))
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      historyFunctor O M chi (after (P := P)) after_monotone).sections) :
    let d := historyAfter O M chi hSource hTarget j x
    letI := d.ord
    letI : Preorder (after j) := d.ord.toPreorder
    let a : after j := ⟨labels.symm j, by change labels (labels.symm j) ≤ j; simp⟩
    d.tree.cell a ≫ (d.comparison.app a).right ≍ O.cell (labels.symm j) := by
  let _ := hSource (labels.symm j)
  let _ := hTarget (labels.symm j)
  let r := historyBefore O M chi j x
  let _ := r.ord
  let _ : Preorder (before j) := r.ord.toPreorder
  exact successorPrefix_new_cell_full O M chi j r r.tree.lowerData

theorem fullAfterPrefix_new_cell (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    let d := fullAfterPrefix O M chi hSource hTarget j
    letI := d.ord
    letI : Preorder (after j) := d.ord.toPreorder
    let a : after j := ⟨labels.symm j, by change labels (labels.symm j) ≤ j; simp⟩
    d.tree.cell a ≫ (d.comparison.app a).right ≍ O.cell (labels.symm j) := by
  let _ := indexNonempty (P := P)
  let _ := indexWellFounded (P := P)
  let _ := indexOrderBot (P := P)
  let _ := indexSuccOrder (P := P)
  induction j using Order.isSuccLimitRecOn with
  | isMin j hj =>
    obtain rfl := isMin_iff_eq_bot.1 hj
    have hSeed := (historyInductionData O M chi hSource hTarget).sectionsMk_val_op_bot
      (historySeed O M chi hSource hTarget)
    have hs : fullAfterPrefix O M chi hSource hTarget ⊥ =
        historyAfter O M chi hSource hTarget ⊥ (emptyPredecessorSections O M chi) := by
      unfold fullAfterPrefix fullHistorySections
      rw [hSeed]
      exact extendedState_self O M chi hSource hTarget ⊥ _
    rw [hs]
    exact historyAfter_new_cell O M chi hSource hTarget ⊥ (emptyPredecessorSections O M chi)
  | succ j hj =>
    let e := fullExtension O M chi hSource hTarget (Order.succ j)
    have hm := e.map_succ j (Order.lt_succ_of_not_isMax hj)
    simp only [homOfLE_refl, op_id] at hm
    change e.val = _ at hm
    have hs : fullAfterPrefix O M chi hSource hTarget (Order.succ j) =
        historyAfter O M chi hSource hTarget (Order.succ j)
          (predecessorSections O M chi j hj
            ((historyFunctor O M chi after after_monotone).map
                (homOfLE (Order.le_succ j)).op e.val)) := by
      unfold fullAfterPrefix
      exact (congrArg (fun H : History O M chi after after_monotone (Order.succ j) =>
          H.state (Order.succ j) le_rfl)
        ((fullHistory_value O M chi hSource hTarget (Order.succ j)).trans hm)).trans
        (extendedState_self O M chi hSource hTarget (Order.succ j) _)
    rw [hs]
    exact historyAfter_new_cell O M chi hSource hTarget (Order.succ j) _
  | isSuccLimit j hj =>
    let e := fullExtension O M chi hSource hTarget j
    have hm := e.map_limit j hj le_rfl
    simp only [homOfLE_refl, op_id] at hm
    change e.val = _ at hm
    have hState := congrArg (fun H : History O M chi after after_monotone j => H.state j le_rfl)
      ((fullHistory_value O M chi hSource hTarget j).trans hm)
    let prior : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
          historyFunctor O M chi after after_monotone).sections :=
        { val i := (historyFunctor O M chi after after_monotone).map
            (homOfLE i.unop.2.le).op e.val
          property := by
            intro i k f
            exact History.restrict_comp O M chi after after_monotone
              (leOfHom f.unop) i.unop.2.le e.val }
    have hs : fullAfterPrefix O M chi hSource hTarget j =
        historyAfter O M chi hSource hTarget j prior :=
      hState.trans (extendedState_self O M chi hSource hTarget j prior)
    rw [hs]
    exact historyAfter_new_cell O M chi hSource hTarget j prior

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem fullAfterPrefix_cell_squares (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    PrefixCellSquares O M chi (fullAfterPrefix O M chi hSource hTarget j) := by
  intro a
  have hLabel : labels a.1 ≤ j := a.2
  have hPres := fullAfterPrefix_preserves O M chi hSource hTarget (labels a.1) j hLabel
  have hNew := fullAfterPrefix_new_cell O M chi hSource hTarget (labels a.1)
  have ha : labels.symm (labels a.1) = a.1 := labels.symm_apply_apply a.1
  exact cellSquare_of_preserves O M chi hPres
    (⟨a.1, by change labels a.1 ≤ labels a.1; exact le_rfl⟩ : after (labels a.1))
    (by
      have ha' : (⟨labels.symm (labels a.1), by
        change labels (labels.symm (labels a.1)) ≤ labels a.1; simp⟩ :
          after (labels a.1)) = ⟨a.1, by change labels a.1 ≤ labels a.1; exact le_rfl⟩ :=
        Subtype.ext ha
      have hNew' := hNew
      dsimp only at hNew'
      rw [ha'] at hNew'
      exact ha ▸ hNew')

theorem fullOriginalPrefix_cell_squares :
    PrefixCellSquares O M chi (fullOriginalPrefix O M chi hSource hTarget) := by
  intro a
  let i := labels a.1
  let F := fullAfterPrefix O M chi hSource hTarget
  have hPres := limitPrefix_preserves O M chi after after_monotone F
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩)
    fullAfter_cover (fullAfterPrefix_preserves O M chi hSource hTarget) i
  exact cellSquare_of_preserves O M chi hPres
    (⟨a.1, by change labels a.1 ≤ i; exact le_rfl⟩ : after i)
    (fullAfterPrefix_cell_squares O M chi hSource hTarget i _)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem fullOriginalPrefixAll_cell_squares :
    PrefixCellSquares O M chi (fullOriginalPrefixAll O M chi hSource hTarget) := by
  classical
  by_cases hP : Nonempty P
  · let _ := hP
    unfold fullOriginalPrefixAll
    rw [dite_eq_left hP]
    exact fullOriginalPrefix_cell_squares O M chi hSource hTarget
  · intro a
    exact False.elim (hP ⟨a.1⟩)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem historyAfter_new_attaching (j : OriginalCellWellOrderEnumeration.Index (P := P))
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      historyFunctor O M chi after after_monotone).sections) :
    let d := historyAfter O M chi hSource hTarget j x
    let a : after j := ⟨labels.symm j, by change labels (labels.symm j) ≤ j; simp⟩
    (letI := d.ord
     d.tree.attaching a ≫ (prefixPredecessorComparison O M chi d a).right) ≍
         O.attaching (labels.symm j) := by
  let _ := hSource (labels.symm j)
  let _ := hTarget (labels.symm j)
  let r := historyBefore O M chi j x
  let _ := r.ord
  let _ : Preorder (before j) := r.ord.toPreorder
  exact successorPrefix_new_attaching O M chi j r r.tree.lowerData


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem fullAfterPrefix_new_attaching (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    let d := fullAfterPrefix O M chi hSource hTarget j
    let a : after j := ⟨labels.symm j, by change labels (labels.symm j) ≤ j; simp⟩
    (letI := d.ord
     d.tree.attaching a ≫ (prefixPredecessorComparison O M chi d a).right) ≍
         O.attaching (labels.symm j) := by
  let _ := indexNonempty (P := P)
  let _ := indexWellFounded (P := P)
  let _ := indexOrderBot (P := P)
  let _ := indexSuccOrder (P := P)
  induction j using Order.isSuccLimitRecOn with
  | isMin j hj =>
    obtain rfl := isMin_iff_eq_bot.1 hj
    have hSeed := (historyInductionData O M chi hSource hTarget).sectionsMk_val_op_bot
      (historySeed O M chi hSource hTarget)
    have hs : fullAfterPrefix O M chi hSource hTarget ⊥ =
        historyAfter O M chi hSource hTarget ⊥ (emptyPredecessorSections O M chi) := by
      unfold fullAfterPrefix fullHistorySections
      rw [hSeed]
      exact extendedState_self O M chi hSource hTarget ⊥ _
    rw [hs]
    exact historyAfter_new_attaching O M chi hSource hTarget ⊥ (emptyPredecessorSections O M chi)
  | succ j hj =>
    let e := fullExtension O M chi hSource hTarget (Order.succ j)
    have hm := e.map_succ j (Order.lt_succ_of_not_isMax hj)
    simp only [homOfLE_refl, op_id] at hm
    change e.val = _ at hm
    have hs : fullAfterPrefix O M chi hSource hTarget (Order.succ j) =
        historyAfter O M chi hSource hTarget (Order.succ j)
          (predecessorSections O M chi j hj
            ((historyFunctor O M chi after after_monotone).map
                (homOfLE (Order.le_succ j)).op e.val)) := by
      unfold fullAfterPrefix
      exact (congrArg (fun H : History O M chi after after_monotone (Order.succ j) =>
          H.state (Order.succ j) le_rfl)
        ((fullHistory_value O M chi hSource hTarget (Order.succ j)).trans hm)).trans
        (extendedState_self O M chi hSource hTarget (Order.succ j) _)
    rw [hs]
    exact historyAfter_new_attaching O M chi hSource hTarget (Order.succ j) _
  | isSuccLimit j hj =>
    let e := fullExtension O M chi hSource hTarget j
    have hm := e.map_limit j hj le_rfl
    simp only [homOfLE_refl, op_id] at hm
    change e.val = _ at hm
    have hState := congrArg (fun H : History O M chi after after_monotone j => H.state j le_rfl)
      ((fullHistory_value O M chi hSource hTarget j).trans hm)
    let prior : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
          historyFunctor O M chi after after_monotone).sections :=
        { val i := (historyFunctor O M chi after after_monotone).map
            (homOfLE i.unop.2.le).op e.val
          property := by
            intro i k f
            exact History.restrict_comp O M chi after after_monotone
              (leOfHom f.unop) i.unop.2.le e.val }
    have hs : fullAfterPrefix O M chi hSource hTarget j =
        historyAfter O M chi hSource hTarget j prior :=
      hState.trans (extendedState_self O M chi hSource hTarget j prior)
    rw [hs]
    exact historyAfter_new_attaching O M chi hSource hTarget j prior


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem fullAfterPrefix_attaching_squares (j : OriginalCellWellOrderEnumeration.Index (P := P)) :
    PrefixAttachingSquares O M chi (fullAfterPrefix O M chi hSource hTarget j) := by
  intro a
  have hLabel : labels a.1 ≤ j := a.2
  have hPres := fullAfterPrefix_preserves O M chi hSource hTarget (labels a.1) j hLabel
  have hNew := fullAfterPrefix_new_attaching O M chi hSource hTarget (labels a.1)
  have ha : labels.symm (labels a.1) = a.1 := labels.symm_apply_apply a.1
  exact attachingSquare_of_preserves O M chi _ _ hPres
    (⟨a.1, by change labels a.1 ≤ labels a.1; exact le_rfl⟩ : after (labels a.1))
    (by
      have ha' : (⟨labels.symm (labels a.1), by
        change labels (labels.symm (labels a.1)) ≤ labels a.1; simp⟩ :
          after (labels a.1)) = ⟨a.1, by change labels a.1 ≤ labels a.1; exact le_rfl⟩ :=
        Subtype.ext ha
      have hNew' := hNew
      dsimp only at hNew'
      let r := fullAfterPrefix O M chi hSource hTarget (labels a.1)
      have step (b c : after (labels a.1)) (hbc : b = c)
          (hb : (letI := r.ord
            r.tree.attaching b ≫ (prefixPredecessorComparison O M chi r b).right) ≍
                O.attaching b.1) :
          (letI := r.ord
           r.tree.attaching c ≫ (prefixPredecessorComparison O M chi r c).right) ≍
               O.attaching c.1 := by
        cases hbc
        exact hb
      exact step _ _ ha' hNew')

theorem fullOriginalPrefix_attaching_squares :
    PrefixAttachingSquares O M chi (fullOriginalPrefix O M chi hSource hTarget) := by
  intro a
  let i := labels a.1
  let F := fullAfterPrefix O M chi hSource hTarget
  have hPres := limitPrefix_preserves O M chi after after_monotone F
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩)
    fullAfter_cover (fullAfterPrefix_preserves O M chi hSource hTarget) i
  exact attachingSquare_of_preserves O M chi _ _ hPres
    (⟨a.1, by change labels a.1 ≤ i; exact le_rfl⟩ : after i)
    (fullAfterPrefix_attaching_squares O M chi hSource hTarget i _)


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)


theorem fullOriginalPrefixAll_attaching_squares :
    PrefixAttachingSquares O M chi (fullOriginalPrefixAll O M chi hSource hTarget) := by
  classical
  by_cases hP : Nonempty P
  · let _ := hP
    unfold fullOriginalPrefixAll
    rw [dite_eq_left hP]
    exact fullOriginalPrefix_attaching_squares O M chi hSource hTarget
  · intro a
    exact False.elim (hP ⟨a.1⟩)


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- A complete actual family keeps local histories and their original cell/source laws. -/
structure CompleteRefiningHistory where
  /-- The actual whole family of compatible original histories. -/
  sections : (historyFunctor O M chi (after (P := P)) after_monotone).sections
  /-- Every local original cell-target square. -/
  cellSquares : ∀ j : OriginalCellWellOrderEnumeration.Index (P := P),
    PrefixCellSquares O M chi ((sections.val (op j)).state j le_rfl)
  /-- Every local original cell-source attaching square. -/
  attachingSquares : ∀ j : OriginalCellWellOrderEnumeration.Index (P := P),
    PrefixAttachingSquares O M chi ((sections.val (op j)).state j le_rfl)

/-- Each actual complete family supplies its literal original AFTER prefix. -/
def CompleteRefiningHistory.prefix (H : CompleteRefiningHistory O M chi)
    (j : OriginalCellWellOrderEnumeration.Index (P := P)) : Prefix O M chi (after j) :=
  (H.sections.val (op j)).state j le_rfl

/-- Section compatibility retains every old field between the actual original AFTER prefixes. -/
theorem CompleteRefiningHistory.preserves (H : CompleteRefiningHistory O M chi)
    (i j : OriginalCellWellOrderEnumeration.Index (P := P)) (hij : i ≤ j) :
    Preserves O M chi (after_monotone hij) (H.prefix O M chi i) (H.prefix O M chi j) := by
  have hx : (H.sections.val (op j)).restrict O M chi after after_monotone hij =
      H.sections.val (op i) := H.sections.property (homOfLE hij : i ⟶ j).op
  have hs : (H.sections.val (op j)).state i hij = (H.sections.val (op i)).state i le_rfl :=
    congrArg (fun K : History O M chi after after_monotone i => K.state i le_rfl) hx
  have h := (H.sections.val (op j)).preserves i j hij le_rfl
  rw [hs] at h
  exact h

variable [HasPushouts C] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- Original compact-cell geometry constructs the complete family, including the empty carrier. -/
def constructedRefiningHistory : CompleteRefiningHistory O M chi := by
  classical
  by_cases hP : Nonempty P
  · let _ := hP
    exact {
      sections := fullHistorySections O M chi hSource hTarget
      cellSquares := fullAfterPrefix_cell_squares O M chi hSource hTarget
      attachingSquares := fullAfterPrefix_attaching_squares O M chi hSource hTarget }
  · let x : (historyFunctor O M chi (after (P := P)) after_monotone).sections := {
      val j := False.elim (hP ⟨labels.symm j.unop⟩)
      property := by
        intro i k f
        exact False.elim (hP ⟨labels.symm i.unop⟩) }
    exact {
      sections := x
      cellSquares j := False.elim (hP ⟨labels.symm j⟩)
      attachingSquares j := False.elim (hP ⟨labels.symm j⟩) }

end

end CategoryTheory.SmallObject.OriginalGoodification
