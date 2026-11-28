/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.WeakMemory.RC11
import Mathlib.Data.Fintype.Fin

/-!
# Tests for finite RC11 consistency

The same four-event trace has three reads-from witnesses. Reading the latest write gives a
consistent RMW. Dropping the edge leaves every cycle check intact but loses completeness.
Reading the initial write instead keeps completeness and coherence but skips a write in
modification order. The prefix language of this trace makes fullness and read completeness
separate judgements: swapping event numbers preserves fullness, whereas the initial write alone
is generated but not full. A five-event graph tests synchronisation through two fences; a
six-event graph has a cycle in the partial SC relation but none in sequencing plus reads-from.
A seven-event graph has a base SC edge that disappears without the different-location bridge.
All examples concern abstract labelled graphs.
-/

namespace Cslib.Semantics.WeakMemory.RC11.Tests

open Relation

private inductive Feed where
  | missing | initial | latest
  deriving DecidableEq

-- The only location is initialised at event 0. A second write of the same value (1) competes
-- to feed the read (2); the RMW's write (3) stores a different value.
private abbrev lab (e : Fin 4) : Label (Fin 1) Bool :=
  if e = 0 then .write .na 0 false else if e = 1 then .write .rlx 0 false
  else if e = 2 then .read .rlx 0 false else .write .rlx 0 true

private abbrev sb (a b : Fin 4) := (a = 0 ∧ b ≠ 0) ∨ (a = 2 ∧ b = 3)
private abbrev rmw (a b : Fin 4) := a = 2 ∧ b = 3
private abbrev mo (a b : Fin 4) := a ≠ 2 ∧ b ≠ 2 ∧ a < b
private abbrev rf (f : Feed) (a b : Fin 4) :=
  b = 2 ∧ ((f = .initial ∧ a = 0) ∨ (f = .latest ∧ a = 1))

private abbrev trace : Trace (Fin 1) Bool false 4 where
  lab := lab
  legal := by decide
  init := fun _ => 0
  init_lab := by decide
  sb := sb
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw := rmw
  rmw_spec := by unfold Immediate Label.SameLoc; decide

private abbrev graph (f : Feed) : Execution (Fin 1) Bool false 4 where
  toTrace := trace
  rf := rf f
  rf_spec := by cases f <;> decide
  rf_unique := by cases f <;> decide
  mo := mo
  mo_spec := by unfold Label.SameLoc; decide
  mo_irrefl := by decide
  mo_trans := by decide
  mo_total := by unfold Label.SameLoc; decide

-- Each choice has a common increasing rank for hb, eco and sb ∪ rf. When 2 reads from 0,
-- reads-before goes from 2 to 1, so that witness needs the two middle ranks exchanged.
private abbrev rank (f : Feed) (e : Fin 4) : Nat :=
  if f = .initial then (if e = 1 then 2 else if e = 2 then 1 else e.val) else e.val

private theorem path_increases {E : Type*} {s : E → E → Prop} (k : E → Nat)
    (step : ∀ a b, s a b → k a < k b) {a b : E} (h : TransGen s a b) : k a < k b := by
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact lt_trans ih (step _ _ h)

private theorem hb_bound (f : Feed) {a b : Fin 4} (h : (graph f).hb a b) :
    rank f a < rank f b := by
  apply path_increases (rank f) _ h
  intro x y edge
  rcases edge with hs | hw
  · exact (show ∀ i j, sb i j → rank f i < rank f j by cases f <;> decide) x y hs
  · exact False.elim ((show ∀ e : Fin 4, ¬ Mode.rel.atLeast (lab e).mode by decide) x
      ((graph f).sw_source hw))

private theorem eco_bound (f : Feed) {a b : Fin 4} (h : (graph f).eco a b) :
    rank f a < rank f b := by
  apply path_increases (rank f) _ h
  change ∀ a b, ((rf f a b ∨ mo a b) ∨ ∃ w, rf f w a ∧ mo w b) → rank f a < rank f b
  cases f <;> decide

private theorem coherence (f : Feed) : Std.Irrefl (Comp (graph f).hb (ReflGen (graph f).eco)) := by
  constructor
  rintro e ⟨b, hb, ret⟩
  have p := hb_bound f hb
  cases ret with
  | refl => exact (lt_irrefl _ p)
  | single he => exact (lt_asymm p (eco_bound f he))

private theorem sc (f : Feed) : Acyclic (graph f).psc := by
  refine ⟨fun e h => lt_irrefl _ (path_increases (rank f) ?_ h)⟩
  intro a b edge
  exact False.elim ((show ∀ i : Fin 4, (lab i).mode ≠ .sc by decide) a
    ((graph f).psc_source edge))

private theorem nta (f : Feed) : Acyclic ((graph f).sb ⊔ (graph f).rf) := by
  refine ⟨fun e h => lt_irrefl _ (path_increases (rank f) ?_ h)⟩
  change ∀ a b, sb a b ∨ rf f a b → rank f a < rank f b
  cases f <;> decide

-- Positive: both RMW halves participate, with a genuine source and a later write.
example : (graph .latest).Consistent where
  complete := by change ∀ r, (lab r).isRead → ∃ w, rf .latest w r; decide
  coherence := coherence _
  atomicity := by
    rintro a b ⟨rfl, rfl⟩
    change ¬∃ c, (∃ w, rf .latest w 2 ∧ mo w c) ∧ mo c 3
    decide
  sc := sc _
  noThinAir := nta _

-- The release sequence can really grow by an rf ; rmw pair, not only by sequencing.
example : (graph .latest).rs 1 3 :=
  ⟨1, ⟨rfl, rfl⟩, 1, .refl, 1, ⟨rfl, rfl, rfl⟩,
    ReflTransGen.single ⟨2, by decide, by decide⟩⟩

-- Missing rf: both acyclicity axioms hold, as do coherence and atomicity. But event 2 is a
-- read with no source. No program's judgement of fullness can distinguish the memory choices.
example : Acyclic ((graph .missing).sb ⊔ (graph .missing).rf) ∧ Acyclic (graph .missing).psc ∧
    ¬(graph .missing).Complete := by
  refine ⟨nta _, sc _, fun h => ?_⟩
  exact (show ¬∃ w, rf .missing w 2 by decide) (h 2 rfl)

example : ∀ a b, (graph .missing).rmw a b → ¬Comp (graph .missing).rb (graph .missing).mo a b := by
  rintro a b ⟨rfl, rfl⟩
  change ¬∃ c, (∃ w, rf .missing w 2 ∧ mo w c) ∧ mo c 3
  decide

example : ¬(graph .missing).Consistent := by
  intro h
  exact (show ¬∃ w, rf .missing w 2 by decide) (h.complete 2 rfl)

-- The prefix language of this single whole trace makes fullness nonvacuous: the graph with
-- the missing edge really is full. Its four-event prefixes have retained all events.
private def program : ProgramTraces (Fin 1) Bool false where
  generated t := t.IsPrefix trace
  full := fun {n} t => t.IsPrefix trace ∧ n = 4
  full_generated _ h := h.1
  prefix_closed _ _ h i := h.trans i
  full_rename := by
    intro i j t u e h ht
    have size : i = j := by simpa using Fintype.card_congr e
    exact ⟨h.symm.isPrefix.trans ht.1, size.symm.trans ht.2⟩

-- Move the initial event from 0 to 1, without changing any label or either trace relation
-- under the permutation. Applying the public transport law does not inspect a memory witness.
private abbrev swap01 : Fin 4 ≃ Fin 4 := Equiv.swap 0 1

private abbrev renumbered : Trace (Fin 1) Bool false 4 where
  lab a := lab (swap01 a)
  legal := by decide
  init _ := 1
  init_lab := by decide
  sb a b := sb (swap01 a) (swap01 b)
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw := rmw
  rmw_spec := by
    rintro a b ⟨rfl, rfl⟩
    unfold Immediate Label.SameLoc
    decide

private theorem swap_renames : trace.IsRenaming renumbered swap01 where
  init_eq := by decide
  lab_eq := by decide
  sb_iff := by decide
  rmw_iff := by decide

private theorem full_after_swap : trace.init 0 ≠ renumbered.init 0 ∧ program.full renumbered :=
  ⟨by decide, (program.full_iff_of_renaming swap_renames).mp ⟨Trace.IsPrefix.refl trace, rfl⟩⟩

-- The initial write alone is a proper induced prefix, not a bijective renumbering.
private abbrev initOnly : Trace (Fin 1) Bool false 1 where
  lab _ := .write .na 0 false
  legal _ := rfl
  init _ := 0
  init_lab := by decide
  sb _ _ := False
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw _ _ := False
  rmw_spec := fun _ _ h => h.elim

private theorem proper_prefix_not_full : program.generated initOnly ∧ ¬program.full initOnly := by
  refine ⟨⟨fun _ => 0, fun _ _ _ => Subsingleton.elim .., ?_, ?_, ?_, ?_, ?_⟩,
    fun h => (by decide : 1 ≠ 4) h.2⟩ <;> decide

example : program.full (graph .missing).toTrace ∧ ¬(graph .missing).Complete :=
  ⟨⟨Trace.IsPrefix.refl trace, rfl⟩, fun h =>
    (show ¬∃ w, rf .missing w 2 by decide) (h 2 rfl)⟩

-- Stale source: the RMW at 2,3 skips write 1 in mo. The remaining axioms do not rule this out.
example : (graph .initial).Complete ∧ Std.Irrefl (Comp (graph .initial).hb
    (ReflGen (graph .initial).eco)) ∧ Acyclic (graph .initial).psc ∧
    Acyclic ((graph .initial).sb ⊔ (graph .initial).rf) ∧ ¬(graph .initial).Consistent := by
  refine ⟨?_, coherence _, sc _, nta _, fun h => h.atomicity 2 3 (by decide) ?_⟩
  · change ∀ r, (lab r).isRead → ∃ w, rf .initial w r
    decide
  · exact ⟨1, ⟨0, by decide, by decide⟩, by decide⟩

-- Two distinct threads after initialisation: SC fence (1) before a relaxed write (2),
-- and a relaxed read (3) before an SC fence (4). There is no sb edge from 1 to 4.
private abbrev fenceLab (e : Fin 5) : Label (Fin 1) Bool :=
  if e = 0 then .write .na 0 false else if e = 2 then .write .rlx 0 true
  else if e = 3 then .read .rlx 0 true else .fence .sc

private abbrev fences : Execution (Fin 1) Bool false 5 where
  lab := fenceLab
  legal := by decide
  init := fun _ => 0
  init_lab := by decide
  sb a b := (a = 0 ∧ b ≠ 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 3 ∧ b = 4)
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw _ _ := False
  rmw_spec := fun _ _ h => h.elim
  rf a b := a = 2 ∧ b = 3
  rf_spec := by decide
  rf_unique := by decide
  mo a b := a = 0 ∧ b = 2
  mo_spec := by unfold Label.SameLoc; decide
  mo_irrefl := by decide
  mo_trans := by decide
  mo_total := by unfold Label.SameLoc; decide

example : fences.sbDiffLoc 1 2 ∧ ¬(fences.lab 1).SameLoc (fences.lab 4) := by
  unfold Execution.sbDiffLoc Label.SameLoc
  decide

private theorem fence_sw : fences.sw 1 4 := by
  refine ⟨1, ⟨rfl, rfl⟩, 2, .single ⟨1, ⟨rfl, rfl⟩, by decide⟩, 2, ?_, 3, by decide,
    3, ⟨rfl, rfl, rfl⟩, 4, .single ⟨4, by decide, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨2, ⟨rfl, rfl⟩, 2, .refl, 2, ⟨rfl, rfl, rfl⟩, .refl⟩

example : fences.hb 1 4 ∧ ¬fences.sb 1 4 := ⟨.single (Or.inr fence_sw), by decide⟩

-- Exercise the hb ; eco ; hb branch of the SC-fence relation, not just its hb branch.
example : fences.pscF 1 4 :=
  ⟨1, ⟨rfl, rfl, rfl⟩, 4, Or.inr ⟨2, .single (Or.inl (by decide)), 3,
    .single (Or.inl (Or.inl (by decide))), .single (Or.inl (by decide))⟩, rfl, rfl, rfl⟩

-- All four non-initial events are SC. Each of two threads writes its own location then reads
-- the other one's initial value. Sequencing and rf have a common increasing numbering, but
-- alternating sb and rb gives a genuine pscBase cycle: 2 → 3 → 4 → 5 → 2.
private abbrev scLab (e : Fin 6) : Label (Fin 2) Bool :=
  if e = 0 then .write .na 0 false else if e = 1 then .write .na 1 false
  else if e = 2 then .write .sc 0 true else if e = 3 then .read .sc 1 false
  else if e = 4 then .write .sc 1 true else .read .sc 0 false

private abbrev twoLoc : Execution (Fin 2) Bool false 6 where
  lab := scLab
  legal := by decide
  init x := x.castLE (by decide)
  init_lab := by decide
  sb a b := (a < 2 ∧ 2 ≤ b) ∨ (a = 2 ∧ b = 3) ∨ (a = 4 ∧ b = 5)
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw _ _ := False
  rmw_spec := fun _ _ h => h.elim
  rf a b := (a = 0 ∧ b = 5) ∨ (a = 1 ∧ b = 3)
  rf_spec := by decide
  rf_unique := by decide
  mo a b := (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 4)
  mo_spec := by unfold Label.SameLoc; decide
  mo_irrefl := by decide
  mo_trans := by decide
  mo_total := by unfold Label.SameLoc; decide

private theorem scPair {a b : Fin 6} (ha : (scLab a).mode = .sc) (hb : (scLab b).mode = .sc)
    (h : twoLoc.sb a b ∨ twoLoc.rb a b) : twoLoc.psc a b := by
  refine Or.inl ⟨a, Or.inl ⟨rfl, ha⟩, b, ?_, Or.inl ⟨rfl, hb⟩⟩
  rcases h with s | r
  · exact Or.inl (Or.inl (Or.inl (Or.inl s)))
  · exact Or.inr r

example : twoLoc.Complete ∧ Acyclic (twoLoc.sb ⊔ twoLoc.rf) ∧ ¬Acyclic twoLoc.psc := by
  refine ⟨?_, ⟨fun e h => lt_irrefl _ (path_increases Fin.val ?_ h)⟩, fun h => h.irrefl 2 ?_⟩
  · unfold Execution.Complete
    decide
  · change ∀ a b, twoLoc.sb a b ∨ twoLoc.rf a b → a.val < b.val
    decide
  · have s₁ := scPair (a := 2) (b := 3) rfl rfl (Or.inl (by decide))
    have r₁ := scPair (a := 3) (b := 4) rfl rfl (Or.inr ⟨1, by decide, by decide⟩)
    have s₂ := scPair (a := 4) (b := 5) rfl rfl (Or.inl (by decide))
    have r₂ := scPair (a := 5) (b := 2) rfl rfl (Or.inr ⟨0, by decide, by decide⟩)
    exact (((TransGen.single s₁).tail r₁).tail s₂).tail r₂

-- The three initial writes are 0,1,2. On the first thread SC write 3 (X) precedes release
-- write 4 (Y); on the second, acquire read 5 (Y) precedes SC write 6 (Z). No fence is present.
private abbrev bridgeLab (e : Fin 7) : Label (Fin 3) Bool :=
  if e = 0 then .write .na 0 false else if e = 1 then .write .na 1 false
  else if e = 2 then .write .na 2 false else if e = 3 then .write .sc 0 true
  else if e = 4 then .write .rel 1 true else if e = 5 then .read .acq 1 true
  else .write .sc 2 true

private abbrev bridgeGraph : Execution (Fin 3) Bool false 7 where
  lab := bridgeLab
  legal := by decide
  init x := x.castLE (by decide)
  init_lab := by decide
  sb a b := (a < 3 ∧ 3 ≤ b) ∨ (a = 3 ∧ b = 4) ∨ (a = 5 ∧ b = 6)
  sb_irrefl := by decide
  sb_trans := by decide
  init_sb := by decide
  rmw _ _ := False
  rmw_spec := fun _ _ h => h.elim
  rf a b := a = 4 ∧ b = 5
  rf_spec := by decide
  rf_unique := by decide
  mo a b := (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 6)
  mo_spec := by unfold Label.SameLoc; decide
  mo_irrefl := by decide
  mo_trans := by decide
  mo_total := by unfold Label.SameLoc; decide

-- Here the release/acquire pair synchronises directly via its rf edge (neither fence leg).
private theorem bridge_sw : bridgeGraph.sw 4 5 := by
  refine ⟨4, ⟨rfl, rfl⟩, 4, .refl, 4, ?_, 5, by decide, 5, ⟨rfl, rfl, rfl⟩, 5, .refl, rfl, rfl⟩
  exact ⟨4, ⟨rfl, rfl⟩, 4, .refl, 4, ⟨rfl, rfl, rfl⟩, .refl⟩

private theorem viaBridge : bridgeGraph.pscBase 3 6 := by
  refine ⟨3, Or.inl ⟨rfl, rfl⟩, 6, ?_, Or.inl ⟨rfl, rfl⟩⟩
  refine Or.inl (Or.inl (Or.inl (Or.inr ⟨4, ?_, 5, .single (Or.inr bridge_sw), ?_⟩)))
  all_goals unfold Execution.sbDiffLoc Label.SameLoc; decide

-- Change only the middle of the base SC relation: keep both fence alternatives, but remove
-- sbDiffLoc ; hb ; sbDiffLoc from scb. Every remaining way to connect 3 to 6 is impossible.
private abbrev withoutBridge (a b : Fin 7) : Prop :=
  bridgeGraph.sb a b ∨ (bridgeGraph.hb a b ∧ (bridgeLab a).SameLoc (bridgeLab b)) ∨
    bridgeGraph.mo a b ∨ bridgeGraph.rb a b

private abbrev baseUsing (middle : Fin 7 → Fin 7 → Prop) :=
  Comp (bridgeGraph.scEvents ⊔ Comp bridgeGraph.scFences (ReflGen bridgeGraph.hb))
    (Comp middle (bridgeGraph.scEvents ⊔ Comp (ReflGen bridgeGraph.hb) bridgeGraph.scFences))

-- With its original middle restored the comparison is definitionally the library relation.
example : baseUsing bridgeGraph.scb = bridgeGraph.pscBase := rfl

private theorem bridge_necessary : bridgeGraph.pscBase 3 6 ∧ ¬baseUsing withoutBridge 3 6 := by
  refine ⟨viaBridge, ?_⟩
  rintro ⟨x, hx, y, hxy, hy⟩
  have noFence : ∀ a : Fin 7, ¬(bridgeLab a).isFence := by decide
  obtain rfl : 3 = x := hx.elim (fun h => h.1) (fun ⟨_, h, _⟩ => (noFence 3 h.2.1).elim)
  obtain rfl : y = 6 := hy.elim (fun h => h.1) (fun ⟨z, _, h⟩ => (noFence z h.2.1).elim)
  rcases hxy with hs | ⟨_, hloc⟩ | hm | hr
  · exact (by decide : ¬bridgeGraph.sb 3 6) hs
  · exact (by unfold Label.SameLoc; decide : ¬(bridgeLab 3).SameLoc (bridgeLab 6)) hloc
  · exact (by decide : ¬bridgeGraph.mo 3 6) hm
  · exact (by decide : ¬∃ w, bridgeGraph.rf w 3 ∧ bridgeGraph.mo w 6) hr

end Cslib.Semantics.WeakMemory.RC11.Tests
