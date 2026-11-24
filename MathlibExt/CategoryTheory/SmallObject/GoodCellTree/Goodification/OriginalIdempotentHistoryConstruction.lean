/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalIdempotentSupportHistory
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.OriginalRetractSplitIso

/-!
# Construction of the original BEFORE and AFTER idempotent history

The history is produced by genuine well-founded recursion on the well-order
extension of the original labels. Each BEFORE is the actual union of earlier
AFTER supports. The original union colimit constructs its idempotent, and the
finite-idempotent intersection theorem constructs its actual bounded birth.
The compatibility and exhaustion laws are proved from the recursion.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w t u v uJ

namespace CategoryTheory.SmallObject.OriginalIdempotentSupportHistory

open CategoryTheory.Limits OriginalIdempotentLowerSupport

variable {C : Type u} [Category.{v} C] {X : C}
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj)

instance (A B : State T L q) : Subsingleton (A ⟶ B) :=
  inferInstanceAs (Subsingleton (State.Inclusion A B))

/-- Compatibility is exactly the original inclusion square on each ordered pair. -/
def Compatible {J : Type uJ} [Preorder J] (f : J → State T L q) : Prop :=
  ∀ a b, a ≤ b → Nonempty (State.Inclusion (f a) (f b))

/-- The actual original inclusion squares form the compatible state functor. -/
abbrev familyFunctor {J : Type uJ} [Preorder J] (f : J → State T L q)
    (hf : Compatible T L q f) : J ⥤ State T L q where
  obj a := f a
  map {a b} h := Classical.choice (hf a b (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The total recursion uses the actual union UP whenever its earlier family is compatible.
The unreachable incompatible branch makes well-founded recursion total. -/
def familyBefore {J : Type uJ} [LinearOrder J] (f : J → State T L q) : State T L q := by
  classical
  exact if h : Nonempty J ∧ Compatible T L q f then
    letI : Nonempty J := h.1
    filteredUnionState (familyFunctor T L q f h.2)
  else State.empty (T := T) (L := L) (q := q)

/-- A compatible original family has exactly its original union support, also when empty. -/
theorem familyBefore_support {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) : (familyBefore T L q f).support = ⨆ a, (f a).support := by
  classical
  by_cases hn : Nonempty J
  · simp only [familyBefore, dite_eq_left (And.intro hn hf)]
    rfl
  · have he : ¬(Nonempty J ∧ Compatible T L q f) := fun h => hn h.1
    simp only [familyBefore, dite_eq_right he]
    change (⊥ : LowerSet P) = ⨆ a, (f a).support
    apply le_antisymm bot_le
    apply iSup_le
    intro a
    exact False.elim (hn ⟨a⟩)

/-- Every actual earlier square enters the BEFORE union through its original inclusion. -/
def familyBeforeInclusion {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) (a : J) : State.Inclusion (f a) (familyBefore T L q f) := by
  classical
  letI : Nonempty J := ⟨a⟩
  have h : Nonempty J ∧ Compatible T L q f := ⟨⟨a⟩, hf⟩
  simp only [familyBefore, dite_eq_left h]
  exact filteredUnionInclusion (familyFunctor T L q f hf) a

/-- The BEFORE cocone consists of the original lower maps and original lower object. -/
abbrev familyCocone {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) : Cocone (originalDiagram (familyFunctor T L q f hf)) where
  pt := L.obj (⨆ a, (f a).support)
  ι :=
    { app a := L.map (le_iSup (fun j => (f j).support) a)
      naturality a b h := by
        change L.map (Classical.choice (hf a b (leOfHom h))).le ≫
          L.map (le_iSup (fun j => (f j).support) b) =
          L.map (le_iSup (fun j => (f j).support) a) ≫ 𝟙 _
        rw [L.map_comp, Category.comp_id] }

/-- The BEFORE union cocone is proved colimiting from the actual original lower UPs. -/
def familyIsColimit {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) : IsColimit (familyCocone T L q f hf) := by
  classical
  by_cases hn : Nonempty J
  · letI : Nonempty J := hn
    exact L.isColimitFilteredCocone
      (B := familyFunctor T L q f hf ⋙ supportFunctor T L q)
  · letI : IsEmpty J := ⟨fun a => hn ⟨a⟩⟩
    have hi : IsInitial (familyCocone T L q f hf).pt := by
      change IsInitial (L.obj (⨆ a, (f a).support))
      simpa using L.isInitialObjBot
    exact
      { desc := fun t => hi.to t.pt
        fac := fun _ a => False.elim (hn ⟨a⟩)
        uniq := fun _ _ _ => hi.hom_ext _ _ }

/-- The actual state BEFORE cocone keeps its selected object and all original inclusions. -/
abbrev familyBeforeCocone {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) : Cocone (originalDiagram (familyFunctor T L q f hf)) where
  pt := L.obj (familyBefore T L q f).support
  ι :=
    { app a := L.map (familyBeforeInclusion T L q f hf a).le
      naturality a b h := by
        change L.map (Classical.choice (hf a b (leOfHom h))).le ≫
          L.map (familyBeforeInclusion T L q f hf b).le =
          L.map (familyBeforeInclusion T L q f hf a).le ≫ 𝟙 _
        rw [L.map_comp, Category.comp_id] }

/-- The constructed idempotent state uses the genuine original union-colimit point. -/
def familyBeforeIsColimit {J : Type uJ} [LinearOrder J] (f : J → State T L q)
    (hf : Compatible T L q f) : IsColimit (familyBeforeCocone T L q f hf) := by
  refine IsColimit.ofIsoColimit (familyIsColimit T L q f hf)
    (Cocone.ext (L.functor.mapIso (eqToIso (familyBefore_support T L q f hf).symm)) ?_)
  intro a
  change L.map (le_iSup (fun j => (f j).support) a) ≫
      L.map (leOfHom (eqToHom (familyBefore_support T L q f hf).symm)) =
    L.map (familyBeforeInclusion T L q f hf a).le
  rw [L.map_comp]

variable [WellFoundedLT P]

/-- The index remains the same original-label well-order extension. -/
abbrev HistoryIndex := OriginalCellWellOrderEnumeration.Index (P := P)

/-- A recursion entry stores its actual BEFORE and the produced bounded birth. -/
structure Entry (chi : Cardinal.{w}) where
  /-- The original BEFORE lower support with its endpoint-compatible idempotent. -/
  before : State T L q
  /-- The bounded birth containing the selected next original-label seed. -/
  birth : BoundedBirth T L q before chi (nextSeed T L q before)

/-- The entry's AFTER is the original union-pushout construction. -/
abbrev Entry.after {chi : Cardinal.{w}} (E : Entry T L q chi) : State T L q :=
  E.birth.after

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hq : q ≫ q = q) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)

/-- The actual next entry uses only the earlier entries, original union UPs and bounded birth. -/
def entryStep (p : HistoryIndex (P := P))
    (f : ∀ j : HistoryIndex (P := P), j < p → Entry T L q chi) : Entry T L q chi :=
  let B := familyBefore T L q (fun j : Set.Iio p => (f j.1 j.2).after)
  { before := B
    birth := nextBirth T L q hq chi hUncountable good B }

/-- The complete history is constructed from the empty support by genuine well-founded recursion. -/
def history : HistoryIndex (P := P) → Entry T L q chi :=
  (OriginalCellWellOrderEnumeration.enumeration_wellFounded (P := P)).fix
    (entryStep T L q hq chi hUncountable good)

theorem history_eq (p : HistoryIndex (P := P)) :
    history T L q hq chi hUncountable good p =
      entryStep T L q hq chi hUncountable good p
        (fun j _ => history T L q hq chi hUncountable good j) :=
  WellFounded.fix_eq _ _ _

/-- Genuine recursion proves every preceding AFTER maps compatibly to the actual BEFORE.
Consequently the totalization's incompatible branch is never used. -/
theorem existsHistoryEarlierInclusion (p : HistoryIndex (P := P)) :
    ∀ j, j < p → Nonempty (State.Inclusion
      (history T L q hq chi hUncountable good j).after
      (history T L q hq chi hUncountable good p).before) := by
  apply (OriginalCellWellOrderEnumeration.enumeration_wellFounded (P := P)).induction p
  intro p ih
  have hc : Compatible T L q
      (fun j : Set.Iio p => (history T L q hq chi hUncountable good j.1).after) := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      exact ⟨State.Inclusion.identity _⟩
    · have hlt : i.1 < j.1 := lt_of_le_of_ne hij (fun h => heq (Subtype.ext h))
      obtain ⟨h⟩ := ih j.1 j.2 i.1 hlt
      exact ⟨State.Inclusion.comp h
        (history T L q hq chi hUncountable good j.1).birth.beforeInclusion⟩
  intro j hj
  rw [history_eq T L q hq chi hUncountable good p]
  exact ⟨familyBeforeInclusion T L q _ hc ⟨j, hj⟩⟩

/-- The actual earlier original map and its full idempotent square are constructed. -/
def historyEarlierInclusion (j p : HistoryIndex (P := P)) (hjp : j < p) :
    State.Inclusion (history T L q hq chi hUncountable good j).after
      (history T L q hq chi hUncountable good p).before :=
  Classical.choice (existsHistoryEarlierInclusion T L q hq chi hUncountable good p j hjp)

/-- All actual original AFTER inclusions commute with the recursively constructed idempotents. -/
theorem historyCompatible : Compatible T L q
    (fun p => (history T L q hq chi hUncountable good p).after) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    exact ⟨State.Inclusion.identity _⟩
  · exact ⟨State.Inclusion.comp
      (historyEarlierInclusion T L q hq chi hUncountable good a b h)
      (history T L q hq chi hUncountable good b).birth.beforeInclusion⟩

theorem historyBelowCompatible (p : HistoryIndex (P := P)) : Compatible T L q
    (fun j : Set.Iio p => (history T L q hq chi hUncountable good j.1).after) := by
  intro a b hab
  exact historyCompatible T L q hq chi hUncountable good a.1 b.1 hab

/-- The actual AFTER state at an original well-order label. -/
abbrev after (p : HistoryIndex (P := P)) : State T L q :=
  (history T L q hq chi hUncountable good p).after

/-- BEFORE uses the actual earlier AFTER family and its original union UP. -/
abbrev before (p : HistoryIndex (P := P)) : State T L q :=
  familyBefore T L q (fun j : Set.Iio p => after T L q hq chi hUncountable good j.1)

/-- The actual bounded birth is constructed from this BEFORE, not supplied as a chart. -/
abbrev birth (p : HistoryIndex (P := P)) :
    BoundedBirth T L q (before T L q hq chi hUncountable good p) chi
      (nextSeed T L q (before T L q hq chi hUncountable good p)) :=
  nextBirth T L q hq chi hUncountable good (before T L q hq chi hUncountable good p)

/-- The recursion's AFTER is exactly the actual constructed birth union. -/
theorem after_eq_birth (p : HistoryIndex (P := P)) :
    after T L q hq chi hUncountable good p =
      (birth T L q hq chi hUncountable good p).after := by
  change (history T L q hq chi hUncountable good p).after = _
  rw [history_eq T L q hq chi hUncountable good p]
  rfl

/-- BEFORE is the literal union of all preceding original AFTER supports at every label. -/
theorem before_union (p : HistoryIndex (P := P)) :
    (before T L q hq chi hUncountable good p).support =
      ⨆ j : Set.Iio p, (after T L q hq chi hUncountable good j.1).support :=
  familyBefore_support T L q _ (historyBelowCompatible T L q hq chi hUncountable good p)

/-- The original earlier-to-BEFORE map and its idempotent square. -/
abbrev earlierToBefore (j p : HistoryIndex (P := P)) (hjp : j < p) :
    State.Inclusion (after T L q hq chi hUncountable good j)
      (before T L q hq chi hUncountable good p) :=
  familyBeforeInclusion T L q _ (historyBelowCompatible T L q hq chi hUncountable good p)
    ⟨j, hjp⟩

/-- The actual birth inclusion retains the original BEFORE object and AFTER object. -/
def beforeToAfter (p : HistoryIndex (P := P)) :
    State.Inclusion (before T L q hq chi hUncountable good p)
      (after T L q hq chi hUncountable good p) := by
  rw [after_eq_birth T L q hq chi hUncountable good p]
  exact (birth T L q hq chi hUncountable good p).beforeInclusion

/-- The actual original lower diagram of all AFTER states. -/
abbrev afterStateFunctor : HistoryIndex (P := P) ⥤ State T L q :=
  familyFunctor T L q (after T L q hq chi hUncountable good)
    (historyCompatible T L q hq chi hUncountable good)

/-- The genuine BEFORE cocone contains the actual original earlier lower-map legs. -/
abbrev beforeCocone (p : HistoryIndex (P := P)) :=
  familyBeforeCocone T L q (fun j : Set.Iio p => after T L q hq chi hUncountable good j.1)
    (historyBelowCompatible T L q hq chi hUncountable good p)

/-- Each BEFORE cocone, including every limit, is the genuine original union colimit. -/
def beforeIsColimit (p : HistoryIndex (P := P)) :
    IsColimit (beforeCocone T L q hq chi hUncountable good p) :=
  familyBeforeIsColimit T L q _ (historyBelowCompatible T L q hq chi hUncountable good p)

/-- Well-order induction proves that each original label is captured by its actual AFTER. -/
theorem captures (p : HistoryIndex (P := P)) :
    OriginalCellWellOrderEnumeration.labels.symm p ∈
      (after T L q hq chi hUncountable good p).support := by
  apply (OriginalCellWellOrderEnumeration.enumeration_wellFounded (P := P)).induction p
  intro p ih
  have hb : ∀ b : P, OriginalCellWellOrderEnumeration.labels b <
      OriginalCellWellOrderEnumeration.labels
        (OriginalCellWellOrderEnumeration.labels.symm p) →
      b ∈ (before T L q hq chi hUncountable good p).support := by
    intro b hbp
    have hp : OriginalCellWellOrderEnumeration.labels b < p := by simpa using hbp
    have hcap := ih (OriginalCellWellOrderEnumeration.labels b) hp
    exact (earlierToBefore T L q hq chi hUncountable good _ p hp).le (by simpa using hcap)
  rw [after_eq_birth T L q hq chi hUncountable good p]
  exact nextBirth_captures T L q hq chi hUncountable good
    (before T L q hq chi hUncountable good p)
    (OriginalCellWellOrderEnumeration.labels.symm p) hb

/-- The same original whole vertex carrier is exhausted; no bound on its size is assumed. -/
theorem exhausts : (⨆ p, (after T L q hq chi hUncountable good p).support) = ⊤ := by
  apply le_antisymm le_top
  intro a _
  apply LowerSet.mem_iSup_iff.2
  refine ⟨OriginalCellWellOrderEnumeration.labels a, ?_⟩
  simpa using captures T L q hq chi hUncountable good
    (OriginalCellWellOrderEnumeration.labels a)

/-- Every actual original birth difference has cardinal below chi. -/
theorem birth_difference_bounded (p : HistoryIndex (P := P)) : HasCardinalLT
    (((after T L q hq chi hUncountable good p).support : Set P) \
      ((before T L q hq chi hUncountable good p).support : Set P) : Set P) chi := by
  rw [after_eq_birth T L q hq chi hUncountable good p]
  exact (birth T L q hq chi hUncountable good p).difference_bounded

/-- The birth's tree retains the literal original difference carrier, root and selected maps. -/
abbrev differenceTree (p : HistoryIndex (P := P)) :=
  CellTreeIncrement.tree T L
    (before T L q hq chi hUncountable good p).support
    (after T L q hq chi hUncountable good p).support
    (beforeToAfter T L q hq chi hUncountable good p).le

/-- The actual relative birth arrow is precisely the same original lower inclusion. -/
theorem differenceTree_hom (p : HistoryIndex (P := P)) :
    (differenceTree T L q hq chi hUncountable good p).hom =
      (L.map (beforeToAfter T L q hq chi hUncountable good p).le).right := rfl

/-- The actual difference labels retain the original generator, with no relabelling. -/
theorem differenceTree_label (p : HistoryIndex (P := P)) :
    (differenceTree T L q hq chi hUncountable good p).label =
      fun a => T.label a.1 := rfl

/-- The literal difference tree retains every original cell's compactness and predecessor bound. -/
theorem differenceTree_good (p : HistoryIndex (P := P)) :
    (differenceTree T L q hq chi hUncountable good p).IsGood chi :=
  CellTreeIncrement.tree_good T L _ _ _ chi good

omit [WellFoundedLT P] in
/-- The original tree supplies its own well-foundedness to construct the complete history. -/
def originalHistory :
    letI := T.wellFoundedLT
    HistoryIndex (P := P) → Entry T L q chi := by
  letI := T.wellFoundedLT
  exact history T L q hq chi hUncountable good

omit [WellFoundedLT P] in
/-- The original good tree and actual endpoint idempotent suffice for full carrier exhaustion. -/
theorem original_exhausts :
    letI := T.wellFoundedLT
    (⨆ p, (originalHistory T L q hq chi hUncountable good p).after.support) = ⊤ := by
  let _ := T.wellFoundedLT
  exact exhausts T L q hq chi hUncountable good

omit [WellFoundedLT P] in
/-- The complete original support history is produced from the actual original retract maps. -/
def fromOriginalRetract {Y : Under X} (i : Y ⟶ T.endpointObj) (r : T.endpointObj ⟶ Y)
    (hir : i ≫ r = 𝟙 Y) :
    letI := T.wellFoundedLT
    HistoryIndex (P := P) → Entry T L (r ≫ i) chi :=
  originalHistory T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good

omit [WellFoundedLT P] in
/-- The actual original source-fixed retract produces an exhaustive same-label history. -/
theorem fromOriginalRetract_exhausts {Y : Under X} (i : Y ⟶ T.endpointObj)
    (r : T.endpointObj ⟶ Y) (hir : i ≫ r = 𝟙 Y) :
    letI := T.wellFoundedLT
    (⨆ p, (fromOriginalRetract T L chi hUncountable good i r hir p).after.support) = ⊤ :=
  original_exhausts T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good

end CategoryTheory.SmallObject.OriginalIdempotentSupportHistory
