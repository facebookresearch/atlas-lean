/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaver
meta import CSLibExt.Computability.BusyBeaver
import Mathlib.Tactic.Eval
import Mathlib.Tactic.ToExpr
import Lean.ToExpr

/-!
# Four-state Busy Beaver certificate checker

The finite search over partial transition tables reduces the upper bound to checked batches.
The search uses tape reflection and renames unused states. Repeated configurations, finite
tape windows and finite automata certify nonhalting branches.
-/

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

namespace busyBeaverSteps_four_wanted

private abbrev Sym := Fin 2
private abbrev State := Fin 4
private abbrev Action := Sym × Move × State

/-- The low bits of each side are the cells nearest the head. -/
private structure Tape where
  left : Nat
  scan : Sym
  right : Nat

private def symbol (b : Bool) : Sym := if b then 1 else 0

private def Tape.read (z : Tape) : ℤ → Sym
  | .ofNat 0 => z.scan
  | .ofNat (n + 1) => symbol (z.right.testBit n)
  | .negSucc n => symbol (z.left.testBit n)

private def Tape.move (z : Tape) (w : Sym) : Move → Tape
  | .right => ⟨Nat.bit (w == 1) z.left, symbol (z.right.testBit 0), z.right >>> 1⟩
  | .left => ⟨z.left >>> 1, symbol (z.left.testBit 0), Nat.bit (w == 1) z.right⟩

private theorem symbol_write (w : Sym) : symbol (w == 1) = w := by decide +revert +kernel

private theorem Tape.read_move (z : Tape) (w : Sym) (d : Move) (i : ℤ) :
    (z.move w d).read i = if i + d.shift = 0 then w else z.read (i + d.shift) := by
  cases d <;> cases i with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => first | rfl | simpa only [Tape.move, Tape.read, Nat.testBit_bit_zero,
          show (Int.ofNat (0 + 1) + Move.left.shift = 0) from rfl, ite_true] using symbol_write w
      | succ k =>
        first
        | rw [show Int.ofNat (k + 1 + 1) + Move.left.shift = Int.ofNat (k + 1) by
            change (k : ℤ) + 1 + 1 + (-1) = k + 1
            omega]
          simp [Tape.read, Tape.move, Nat.testBit_bit_succ, show (k : ℤ) + 1 ≠ 0 by omega]
        | change symbol ((z.right >>> 1).testBit (k + 1)) =
            symbol (z.right.testBit (k + 1 + 1))
          rw [Nat.testBit_shiftRight, Nat.add_comm 1]
  | negSucc n =>
    cases n with
    | zero => first | rfl | simpa only [Tape.move, Tape.read, Nat.testBit_bit_zero,
        show (Int.negSucc 0 + Move.right.shift = 0) from rfl, ite_true] using symbol_write w
    | succ k =>
      first
      | change symbol ((z.left >>> 1).testBit (k + 1)) =
          symbol (z.left.testBit (k + 1 + 1))
        rw [Nat.testBit_shiftRight, Nat.add_comm 1]
      | rw [show Int.negSucc (k + 1) + Move.right.shift = Int.negSucc k by
          change -((k : ℤ) + 1 + 1) + 1 = -((k : ℤ) + 1)
          omega]
        simp [Tape.read, Tape.move, Nat.testBit_bit_succ,
          show Int.negSucc k ≠ 0 from Int.noConfusion]

private structure Point where
  state : State
  tape : Tape
  time : Nat

private def Point.next (p : Point) (a : Action) : Point :=
  ⟨a.2.2, p.tape.move a.1 a.2.1, p.time + 1⟩

private def start : Point := ⟨0, ⟨0, 0, 0⟩, 0⟩

private def Fits (M : Machine 4) (p : Point) (h : ℤ) : Prop :=
  (run M p.time).state = some p.state ∧ (run M p.time).head = h ∧
    ∀ i, (run M p.time).tape i = p.tape.read (i - h)

private theorem fits_start (M : Machine 4) : Fits M start 0 := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  rw [sub_zero]
  cases i with
  | ofNat n => cases n <;> simp [start, Tape.read, symbol, run, initial]
  | negSucc n => simp [start, Tape.read, symbol, run, initial]

private theorem Fits.next {M : Machine 4} {p h} (hf : Fits M p h)
    {w d q} (ha : M p.state p.tape.scan = (w, d, some q)) :
    Fits M (p.next (w, d, q)) (h + d.shift) := by
  obtain ⟨hs, hh, ht⟩ := hf
  have readHead := ht h
  rw [sub_self] at readHead
  change (run M p.time).tape h = p.tape.scan at readHead
  unfold Fits Point.next
  simp only
  rw [run_succ, step_of_state_some _ hs, hh, readHead, ha]
  refine ⟨rfl, rfl, fun i => ?_⟩
  rw [Tape.read_move, show i - (h + d.shift) + d.shift = i - h by abel]
  by_cases hi : i = h
  · subst i
    simp
  · simp [Function.update_of_ne hi, ht, sub_ne_zero.mpr hi]

private theorem Fits.halts_next {M : Machine 4} {p h} (hf : Fits M p h)
    {w d} (ha : M p.state p.tape.scan = (w, d, none)) :
    HaltsWithin M (p.time + 1) := by
  obtain ⟨hs, hh, ht⟩ := hf
  have readHead := ht h
  rw [sub_self] at readHead
  change (run M p.time).tape h = p.tape.scan at readHead
  unfold HaltsWithin
  rw [run_succ, step_state_of_some _ hs, hh, readHead, ha]

private def rename (e : Equiv.Perm State) (M : Machine 4) : Machine 4 :=
  fun q x => let (w, d, next) := M (e.symm q) x; (w, d, next.map e)

private def renameConfig (e : Equiv.Perm State) (c : Config 4) : Config 4 :=
  ⟨c.state.map e, c.head, c.tape⟩

private theorem step_rename (e : Equiv.Perm State) (M : Machine 4) (c : Config 4) :
    step (rename e M) (renameConfig e c) = renameConfig e (step M c) := by
  cases h : c.state with
  | none =>
    rw [step_of_state_none M h, step_of_state_none _ (by simp [renameConfig, h])]
  | some q =>
    have h' : (renameConfig e c).state = some (e q) := by simp [renameConfig, h]
    rw [step_of_state_some _ h', step_of_state_some _ h]
    simp [rename, renameConfig]

private theorem run_rename (e : Equiv.Perm State) (he : e 0 = 0) (M : Machine 4) (t : Nat) :
    run (rename e M) t = renameConfig e (run M t) := by
  induction t with
  | zero =>
    change initial 4 = renameConfig e (initial 4)
    change (⟨some 0, 0, fun _ => 0⟩ : Config 4) = ⟨some (e 0), 0, fun _ => 0⟩
    rw [he]
  | succ t ih => rw [run_succ, run_succ, ih, step_rename]

private theorem haltsWithin_rename (e : Equiv.Perm State) (he : e 0 = 0) (M : Machine 4) (t : Nat) :
    HaltsWithin (rename e M) t ↔ HaltsWithin M t := by
  unfold HaltsWithin
  rw [run_rename e he]
  cases h : (run M t).state <;> simp [renameConfig, h]

private theorem steps_le (M : Machine 4) (b : Nat)
    (h : Halts M → HaltsWithin M b) : stepsOf M ≤ b := by
  by_cases hh : Halts M
  · rw [stepsOf, dite_eq_left hh]
    exact haltTime_le M hh (h hh)
  · simp [stepsOf, hh]

private theorem haltsWithin_of_steps_le {M : Machine 4} {b : Nat}
    (h : Halts M) (hb : stepsOf M ≤ b) : HaltsWithin M b := by
  rw [stepsOf, dite_eq_left h] at hb
  exact haltsWithin_mono (haltsWithin_haltTime M h) hb

private structure Table where
  entries : List (Option Action)
  length_eq : entries.length = 8
  maxState : State

private def index (q : State) (x : Sym) : Nat := 2 * q.val + x.val

private theorem index_lt (q : State) (x : Sym) : index q x < 8 := by
  have := q.isLt
  have := x.isLt
  unfold index
  omega

private theorem index_ne {q q' : State} {x x' : Sym} (h : ¬ (q = q' ∧ x = x')) :
    index q x ≠ index q' x' := by
  intro he
  apply h
  have := x.isLt
  have := x'.isLt
  unfold index at he
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private def Table.get (T : Table) (q : State) (x : Sym) : Option Action :=
  T.entries[index q x]?.getD none

private def empty : Table := ⟨List.replicate 8 none, rfl, 0⟩

private def extend (T : Table) (p : Point) (a : Action) : Table :=
  ⟨T.entries.set (index p.state p.tape.scan) (some a), by simp [T.length_eq],
    max T.maxState a.2.2⟩

private theorem extend_here (T : Table) (p : Point) (a : Action) :
    (extend T p a).get p.state p.tape.scan = some a := by
  simp [Table.get, extend, T.length_eq, index_lt]

private theorem extend_other (T : Table) (p : Point) (a : Action) (q : State) (x : Sym)
    (hne : ¬ (q = p.state ∧ x = p.tape.scan)) :
    (extend T p a).get q x = T.get q x := by
  simp [Table.get, extend, List.getElem?_set_ne (index_ne hne).symm]

private def Supports (T : Table) (M : Machine 4) : Prop :=
  ∀ q x w d q', T.get q x = some (w, d, q') → M q x = (w, d, some q')

private def StatesBounded (T : Table) : Prop :=
  ∀ q x a, T.get q x = some a → q ≤ T.maxState ∧ a.2.2 ≤ T.maxState

private theorem empty_get (q : State) (x : Sym) : empty.get q x = none := by
  unfold Table.get empty
  rw [List.getElem?_replicate]
  simp [index_lt]

private theorem extend_states {T : Table} {p : Point} (hs : StatesBounded T)
    (hp : p.state ≤ T.maxState) (a : Action) : StatesBounded (extend T p a) := by
  intro q x a' he
  by_cases h : q = p.state ∧ x = p.tape.scan
  · obtain ⟨rfl, rfl⟩ := h
    rw [extend_here] at he
    cases he
    exact ⟨hp.trans (le_max_left _ _), le_max_right _ _⟩
  · rw [extend_other _ _ _ _ _ h] at he
    obtain ⟨hq, ha⟩ := hs q x a' he
    exact ⟨hq.trans (le_max_left _ _), ha.trans (le_max_left _ _)⟩

private theorem supports_extend {T : Table} {p : Point} {M : Machine 4}
    {w d q'} (hs : Supports T M) (ha : M p.state p.tape.scan = (w, d, some q')) :
    Supports (extend T p (w, d, q')) M := by
  intro q x v δ r h
  by_cases hkey : q = p.state ∧ x = p.tape.scan
  · obtain ⟨rfl, rfl⟩ := hkey
    rw [extend_here] at h
    cases h
    exact ha
  · rw [extend_other _ _ _ _ _ hkey] at h
    exact hs _ _ _ _ _ h

private def last (T : Table) (p : Point) : Bool :=
  (List.range 8).all fun i => i == index p.state p.tape.scan || (T.entries[i]?.getD none).isSome

private theorem last_full {T : Table} {p : Point} (h : last T p = true) (a : Action)
    (q : State) (x : Sym) : ((extend T p a).get q x).isSome = true := by
  by_cases hkey : q = p.state ∧ x = p.tape.scan
  · obtain ⟨rfl, rfl⟩ := hkey
    rw [extend_here]
    rfl
  · rw [extend_other _ _ _ _ _ hkey]
    have hi := List.all_eq_true.mp h (index q x) (List.mem_range.mpr (index_lt q x))
    simpa [index_ne hkey, Table.get] using hi

private theorem full_not_halts {T : Table} {M : Machine 4} (hm : Supports T M)
    (h : ∀ q x, (T.get q x).isSome = true) : ¬ Halts M := by
  have live (t : Nat) : (run M t).state ≠ none := by
    induction t with
    | zero => exact Option.some_ne_none (0 : State)
    | succ t ih =>
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ih
      let x := (run M t).tape (run M t).head
      obtain ⟨⟨w, d, q'⟩, ht⟩ := Option.isSome_iff_exists.mp (h q x)
      rw [run_succ, step_state_of_some _ hq, hm q x _ _ _ ht]
      exact Option.some_ne_none _
  exact fun ⟨t, ht⟩ => live t ht

private theorem last_bound {T : Table} {p : Point} (htime : p.time < 107)
    (hlast : last T p = true) {M : Machine 4} (hm : Supports T M) {h : ℤ} (hf : Fits M p h) :
    stepsOf M ≤ 107 := by
  obtain ⟨w, d, next, ha⟩ : ∃ w d q, M p.state p.tape.scan = (w, d, q) := ⟨_, _, _, rfl⟩
  cases next with
  | none => apply steps_le; exact fun _ => haltsWithin_mono (hf.halts_next ha) (by omega)
  | some q =>
    have nonhalt := full_not_halts (supports_extend hm ha) (last_full hlast (w, d, q))
    simp [stepsOf, nonhalt]

private def Bounded (T : Table) (p : Point) : Prop :=
  ∀ M, Supports T M → ∀ h, Fits M p h → stepsOf M ≤ 107

private def actions (T : Table) : List Action :=
  (List.finRange 2).flatMap fun w => [Move.right, Move.left].flatMap fun d =>
    ((List.finRange 4).take (T.maxState.val + 2)).map fun q => (w, d, q)

private theorem action_mem (T : Table) (w : Sym) (d : Move) (q : State)
    (hq : q.val ≤ T.maxState.val + 1) : (w, d, q) ∈ actions T := by
  unfold actions
  apply List.mem_flatMap.mpr
  refine ⟨w, List.mem_finRange w, List.mem_flatMap.mpr ⟨d, ?_, ?_⟩⟩
  · cases d <;> simp
  · apply List.mem_map.mpr
    refine ⟨q, ?_, rfl⟩
    have h : q.val < T.maxState.val + 2 := by omega
    have hfin := q.isLt
    have iLt : q.val < ((List.finRange 4).take (T.maxState.val + 2)).length := by
      simp [h, hfin]
    have he : ((List.finRange 4).take (T.maxState.val + 2))[q.val] = q := by
      rw [List.getElem_take, List.getElem_finRange]
      exact Fin.ext rfl
    exact List.mem_of_getElem he

private def reverseMove : Move → Move
  | .left => .right
  | .right => .left

private theorem reverseMove_shift (d : Move) : (reverseMove d).shift = -d.shift := by
  cases d <;> rfl

private def reflect (M : Machine 4) : Machine 4 :=
  fun q x => let (w, d, next) := M q x; (w, reverseMove d, next)

private def reflectConfig (c : Config 4) : Config 4 :=
  ⟨c.state, -c.head, fun i => c.tape (-i)⟩

private theorem step_reflect (M : Machine 4) (c : Config 4) :
    step (reflect M) (reflectConfig c) = reflectConfig (step M c) := by
  cases h : c.state with
  | none =>
    rw [step_of_state_none M h, step_of_state_none _ (show (reflectConfig c).state = none from h)]
  | some q =>
    have h' : (reflectConfig c).state = some q := h
    rw [step_of_state_some _ h', step_of_state_some _ h]
    simp only [reflectConfig, reflect, neg_neg, reverseMove_shift, neg_add_rev, add_comm]
    congr 1
    funext i
    by_cases e : i = -c.head
    · subst i
      simp
    · have ei : -i ≠ c.head := by omega
      simp [Function.update_of_ne e, Function.update_of_ne ei]

private theorem haltsWithin_reflect (M : Machine 4) (t : Nat) :
    HaltsWithin (reflect M) t ↔ HaltsWithin M t := by
  have hr : run (reflect M) t = reflectConfig (run M t) := by
    induction t with
    | zero => rfl
    | succ t ih => rw [run_succ, run_succ, ih, step_reflect]
  unfold HaltsWithin
  rw [hr]
  rfl

private theorem continue_bound {T : Table} {p : Point} {M : Machine 4} {w d q h}
    (hs : StatesBounded T) (hq : p.state ≤ T.maxState) (hm : Supports T M)
    (hf : Fits M p h) (ha : M p.state p.tape.scan = (w, d, some q))
    (kids : ∀ r, (w, d, r) ∈ actions T → Bounded (extend T p (w, d, r)) (p.next (w, d, r))) :
    stepsOf M ≤ 107 := by
  by_cases hq' : q.val ≤ T.maxState.val + 1
  · exact kids _ (action_mem T w d q hq') M (supports_extend hm ha) _ (hf.next ha)
  · let r : State := ⟨T.maxState.val + 1, by have := q.isLt; omega⟩
    let e := Equiv.swap q r
    have fix (s : State) (hh : s ≤ T.maxState) : e s = s :=
      Equiv.swap_apply_of_ne_of_ne
        (fun he => by subst s; change q.val ≤ T.maxState.val at hh; omega)
        (fun he => by subst s; change T.maxState.val + 1 ≤ T.maxState.val at hh; omega)
    have e0 : e 0 = 0 := fix 0 (Nat.zero_le _)
    have e_symm (s : State) (hh : s ≤ T.maxState) : e.symm s = s :=
      e.symm_apply_eq.mpr (fix s hh).symm
    have hm' : Supports T (rename e M) := by
      intro s x v δ s' hp
      obtain ⟨h₁, h₂⟩ := hs _ _ _ hp
      simp [rename, e_symm s h₁, hm _ _ _ _ _ hp, fix _ h₂]
    have ha' : rename e M p.state p.tape.scan = (w, d, some r) := by
      unfold rename
      rw [e_symm p.state hq, ha]
      simp [e]
    have hf' : Fits (rename e M) p h := by
      unfold Fits
      rw [run_rename e e0]
      simpa [renameConfig, hf.1, fix p.state hq] using hf.2
    have hb' := kids _ (action_mem T w d r (Nat.le_refl _)) _
      (supports_extend hm' ha') _ (hf'.next ha')
    apply steps_le
    rintro ⟨t, hrun⟩
    apply (haltsWithin_rename e e0 M 107).mp
    exact haltsWithin_of_steps_le ⟨t, (haltsWithin_rename e e0 M t).mpr hrun⟩ hb'


private theorem branch_bound {T : Table} {p : Point} (hs : StatesBounded T)
    (hq : p.state ≤ T.maxState) (ht : p.time < 107)
    (kids : ∀ a ∈ actions T, Bounded (extend T p a) (p.next a)) : Bounded T p := by
  intro M hm h hf
  obtain ⟨w, d, next, ha⟩ : ∃ w d q, M p.state p.tape.scan = (w, d, q) := ⟨_, _, _, rfl⟩
  cases next with
  | none => apply steps_le; exact fun _ => haltsWithin_mono (hf.halts_next ha) (by omega)
  | some q => exact continue_bound hs hq hm hf ha (fun _ h => kids _ h)

private theorem empty_states : StatesBounded empty := by
  intro q x _ h
  rw [empty_get q x] at h
  contradiction

private theorem root_bound (kids : ∀ (w : Sym) (q : Fin 2),
    let a : Action := (w, .right, q.castLE (by decide))
    Bounded (extend empty start a) (start.next a)) (M : Machine 4) : stepsOf M ≤ 107 := by
  have hm (M : Machine 4) : Supports empty M :=
    fun q x _ _ _ h => by rw [empty_get q x] at h; contradiction
  have right (N : Machine 4) {w q}
      (ha : N start.state start.tape.scan = (w, .right, some q)) : stepsOf N ≤ 107 := by
    apply continue_bound empty_states (le_refl _) (hm N) (fits_start N) ha
    intro r hr
    have onlyFirstTwo : ∀ (v : Sym) (r : State),
        (v, Move.right, r) ∈ actions empty → r.val < 2 := by decide +kernel
    have hr' := onlyFirstTwo w r hr
    exact kids w ⟨r.val, hr'⟩
  obtain ⟨w, d, next, ha⟩ : ∃ w d q, M start.state start.tape.scan = (w, d, q) := ⟨_, _, _, rfl⟩
  cases next with
  | none =>
    apply steps_le
    exact fun _ => haltsWithin_mono ((fits_start M).halts_next ha) (by decide)
  | some q =>
    cases d with
    | right => exact right M ha
    | left =>
      have hr : reflect M start.state start.tape.scan = (w, .right, some q) := by
        unfold reflect
        rw [ha]
        rfl
      have hb := right (reflect M) hr
      apply steps_le
      rintro ⟨t, ht⟩
      exact (haltsWithin_reflect M 107).mp
        (haltsWithin_of_steps_le ⟨t, (haltsWithin_reflect M t).mpr ht⟩ hb)

/-- A replay may use the whole tape, or stay on one side of its starting cell. -/
private inductive Scope
  | all
  | right
  | left
deriving Lean.ToExpr

private def Scope.contains : Scope → Nat → ℤ → Prop
  | .all, _, _ => True
  | .right, n, i => -(n : ℤ) ≤ i
  | .left, n, i => i ≤ n

private def Scope.advance : Scope → Nat → Move → Option Nat
  | .all, _, _ => some 0
  | .right, n, .right | .left, n, .left => some (n + 1)
  | .right, 0, .left | .left, 0, .right => none
  | .right, n + 1, .left | .left, n + 1, .right => some n

private theorem Scope.contains_zero (s : Scope) (n : Nat) : s.contains n 0 := by
  cases s <;> simp [Scope.contains]

private theorem Scope.contains_shift {s : Scope} {n n' : Nat} {d : Move}
    (h : s.advance n d = some n') {i : ℤ} (hi : s.contains n' i) :
    s.contains n (i + d.shift) := by
  cases s <;> cases d <;> cases n <;> simp [Scope.advance] at h <;> subst n' <;>
    simp [Scope.contains, Move.shift] at hi ⊢ <;> omega

private theorem Scope.contains_of_zero {s : Scope} {n : Nat} {i : ℤ}
    (h : s.contains 0 i) : s.contains n i := by
  cases s <;> simp [Scope.contains] at h ⊢ <;> omega

private def Agree (s : Scope) (n : Nat) (p p' : Point) : Prop :=
  p.state = p'.state ∧ ∀ i, s.contains n i → p.tape.read i = p'.tape.read i

private theorem Agree.symm {s n p p'} (h : Agree s n p p') : Agree s n p' p :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

private theorem Agree.trans {s n p p' p''} (h₁ : Agree s n p p') (h₂ : Agree s n p' p'') :
    Agree s n p p'' :=
  ⟨h₁.1.trans h₂.1, fun i hi => (h₁.2 i hi).trans (h₂.2 i hi)⟩

private theorem Agree.weaken {s n p p'} (h : Agree s n p p') : Agree s 0 p p' :=
  ⟨h.1, fun i hi => h.2 i (s.contains_of_zero hi)⟩

private theorem Agree.next {s n n' p p'} (h : Agree s n p p') {w d q}
    (hd : s.advance n d = some n') : Agree s n' (p.next (w, d, q)) (p'.next (w, d, q)) := by
  refine ⟨rfl, fun i hi => ?_⟩
  change (p.tape.move w d).read i = (p'.tape.move w d).read i
  rw [Tape.read_move, Tape.read_move]
  split
  · rfl
  · exact h.2 _ (s.contains_shift hd hi)

private def agrees (s : Scope) (p p' : Point) : Bool :=
  (p.state == p'.state) && (p.tape.scan == p'.tape.scan) &&
    match s with
    | .all => p.tape.left == p'.tape.left && p.tape.right == p'.tape.right
    | .right => p.tape.right == p'.tape.right
    | .left => p.tape.left == p'.tape.left

private theorem agrees_sound {s : Scope} {p p' : Point} (h : agrees s p p' = true) :
    Agree s 0 p p' := by
  unfold agrees at h
  obtain ⟨⟨he, hscan⟩, ht⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
  refine ⟨eq_of_beq he, fun i hi => ?_⟩
  cases s
  · obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp ht
    cases i with
    | ofNat n => cases n <;> simp [Tape.read, eq_of_beq hscan, eq_of_beq hr]
    | negSucc n => simp [Tape.read, eq_of_beq hl]
  · have hr := eq_of_beq ht
    cases i with
    | ofNat n => cases n <;> simp [Tape.read, eq_of_beq hscan, hr]
    | negSucc n => simp [Scope.contains] at hi
  · have hl := eq_of_beq ht
    cases i with
    | ofNat n =>
      cases n with
      | zero => exact eq_of_beq hscan
      | succ n => simp [Scope.contains] at hi; omega
    | negSucc n => simp [Tape.read, hl]

private def replay (T : Table) (s : Scope) : Nat → Point → Nat → Option (Point × Nat)
  | 0, p, n => some (p, n)
  | fuel + 1, p, n => do
    let a ← T.get p.state p.tape.scan
    let n' ← s.advance n a.2.1
    replay T s fuel (p.next a) n'

private theorem replay_sound {T : Table} {s : Scope} {fuel : Nat} {p : Point}
    {n : Nat} {r : Point} {width : Nat} (hr : replay T s fuel p n = some (r, width))
    {M : Machine 4} (hm : Supports T M) {p' : Point} {h : ℤ}
    (hf : Fits M p' h) (ha : Agree s n p p') :
    ∃ r' h', Fits M r' h' ∧ Agree s width r r' ∧ r'.time = p'.time + fuel := by
  induction fuel generalizing p p' n h with
  | zero =>
    cases hr
    exact ⟨p', h, hf, ha, by simp⟩
  | succ fuel ih =>
    rw [replay] at hr
    cases hd : T.get p.state p.tape.scan with
    | none => simp [hd] at hr
    | some a =>
      obtain ⟨w, d, q⟩ := a
      rw [hd] at hr
      change (s.advance n d >>= fun n' => replay T s fuel (p.next (w, d, q)) n') =
        some (r, width) at hr
      cases hn : s.advance n d with
      | none => simp [hn] at hr
      | some n' =>
        rw [hn] at hr
        change replay T s fuel (p.next (w, d, q)) n' = some (r, width) at hr
        have hscan : p.tape.scan = p'.tape.scan := ha.2 0 (s.contains_zero n)
        have ht := hm _ _ _ _ _ hd
        rw [ha.1, hscan] at ht
        obtain ⟨r', h', hf', ha', htime⟩ := ih hr (hf.next ht) (ha.next hn)
        exact ⟨r', h', hf', ha', htime.trans (by simp only [Point.next]; omega)⟩

private def verifiesCycle (T : Table) (p : Point) (s : Scope) (wait period : Nat) : Bool :=
  period != 0 &&
    ((replay T .all wait p 0).any fun (q, _) =>
      (replay T s period q 0).any fun (r, _) => agrees s q r)

private theorem cycle_bound {T : Table} {p : Point} {s : Scope} {wait period : Nat}
    (hc : verifiesCycle T p s wait period = true) : Bounded T p := by
  intro M hm h hf
  apply steps_le
  rintro ⟨t, ht⟩
  unfold verifiesCycle at hc
  obtain ⟨hp, hc⟩ := Bool.and_eq_true_iff.mp hc
  have hpos : 0 < period := Nat.pos_of_ne_zero (bne_iff_ne.mp hp)
  cases hwait : replay T .all wait p 0 with
  | none => simp [hwait] at hc
  | some e =>
    obtain ⟨q, k⟩ := e
    cases hloop : replay T s period q 0 with
    | none => simp [hwait, hloop] at hc
    | some e =>
      obtain ⟨r, n⟩ := e
      have hback : Agree s 0 q r := agrees_sound (by simpa [hwait, hloop] using hc)
      obtain ⟨q', j, hq, hinit, _⟩ :=
        replay_sound hwait hm hf ⟨rfl, fun _ _ => rfl⟩
      have cont (i : Nat) : ∃ u j, Fits M u j ∧ Agree s 0 q u ∧ i ≤ u.time := by
        induction i with
        | zero => exact ⟨q', j, hq, ⟨hinit.1, fun i _ => hinit.2 i trivial⟩, Nat.zero_le _⟩
        | succ i ih =>
          obtain ⟨u, j, hu, ha, htime⟩ := ih
          obtain ⟨v, l, hv, hv', htime'⟩ := replay_sound hloop hm hu ha
          exact ⟨v, l, hv, hback.trans hv'.weaken, by omega⟩
      obtain ⟨u, _, hu, _, htu⟩ := cont t
      exact False.elim (Option.some_ne_none _ (hu.1.symm.trans (haltsWithin_mono ht htu)))

private def probe (T : Table) : Nat → Point → Option Point
  | 0, _ => none
  | fuel + 1, p =>
    match T.get p.state p.tape.scan with
    | none => some p
    | some a => probe T fuel (p.next a)

private theorem probe_sound {T : Table} {fuel : Nat} {p r : Point}
    (hr : probe T fuel p = some r) {M : Machine 4} (hm : Supports T M) {h : ℤ} (hf : Fits M p h)
    (hs : StatesBounded T) (hp : p.state ≤ T.maxState) :
    ∃ h', Fits M r h' ∧ r.state ≤ T.maxState ∧ r.time < p.time + fuel := by
  induction fuel generalizing p h with
  | zero => contradiction
  | succ fuel ih =>
    unfold probe at hr
    split at hr
    next =>
      cases hr
      exact ⟨h, hf, hp, by omega⟩
    next a ht =>
      obtain ⟨w, d, q⟩ := a
      obtain ⟨h', hf', hq, htime⟩ := ih hr (hf.next (hm _ _ _ _ _ ht)) (hs _ _ _ ht).2
      exact ⟨h', hf', hq, by simp only [Point.next] at htime; omega⟩

private structure ListTape where
  left : List Sym
  scan : Sym
  right : List Sym

private def ListTape.move (z : ListTape) (w : Sym) : Move → ListTape
  | .right => ⟨w :: z.left, z.right.headD 0, z.right.tail⟩
  | .left => ⟨z.left.tail, z.left.headD 0, w :: z.right⟩

private def packSide : List Sym → Nat
  | [] => 0
  | x :: xs => Nat.bit (x == 1) (packSide xs)

private theorem packSide_head (xs : List Sym) :
    symbol ((packSide xs).testBit 0) = xs.headD 0 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change symbol ((Nat.bit (x == 1) (packSide xs)).testBit 0) = x
    rw [Nat.testBit_bit_zero, symbol_write]

private theorem packSide_tail (xs : List Sym) :
    packSide xs >>> 1 = packSide xs.tail := by
  cases xs <;> simp [packSide, Nat.bit_shiftRight_one]

private def ListTape.pack (z : ListTape) : Tape :=
  ⟨packSide z.left, z.scan, packSide z.right⟩

private theorem ListTape.pack_move (z : ListTape) (w : Sym) (d : Move) :
    z.pack.move w d = (z.move w d).pack := by
  cases d <;> simp only [Tape.move, ListTape.move, ListTape.pack, packSide,
    packSide_head, packSide_tail]

/-- A finite automaton reads the left half-tape from the blank end. A nondeterministic
automaton reads the right half starting at the head. Its states are pairs consisting of
a left-automaton state and a working state, together with one accepting sink. -/
private structure Certificate where
  size : Nat
  rightward : Bool
  delta : List Nat
  rows : List Nat
  final : Nat
  deriving Lean.ToExpr

private def Certificate.forward (c : Certificate) : Move :=
  if c.rightward then .right else .left

private abbrev Certificate.Node (c : Certificate) := Fin (4 * c.size + 1)

private def Certificate.push (c : Certificate) (l : Nat) (x : Sym) :=
  c.delta[2 * l + x.val]?.getD 0

private def Certificate.row (c : Certificate) (p : Nat) (x : Sym) :=
  c.rows[2 * p + x.val]?.getD 0

private def Certificate.edge (c : Certificate) (p : Nat) (x : Sym) (j : Nat) : Bool :=
  (c.row p x).testBit j

private def node (l : Nat) (q : State) := 4 * l + q.val

private def Certificate.sink (c : Certificate) := 4 * c.size

private def Certificate.Accepts (c : Certificate) (p : Nat) : List Sym → Prop
  | [] => c.final.testBit p
  | x :: xs => ∃ j : c.Node, c.edge p x j ∧ c.Accepts j xs

private def Certificate.label (c : Certificate) : List Sym → Nat
  | [] => 0
  | x :: xs => c.push (c.label xs) x

private def Certificate.ClosedAt (c : Certificate) (T : Table) (l : Fin c.size)
    (q : State) (x : Sym) : Prop :=
  match T.get q x with
  | none => c.edge (node l q) x c.sink = true
  | some (w, d, q') =>
    if d = c.forward then c.edge (node l q) x (node (c.push l w) q') = true
    else ∀ b : Fin c.size, ∀ y : Sym, c.push b y = l →
      ∀ j : c.Node, c.edge (node b q') y j = true →
        c.row j w &&& c.row (node l q) x = c.row j w

private instance decClosedAt (c : Certificate) (T : Table) (l : Fin c.size)
    (q : State) (x : Sym) : Decidable (c.ClosedAt T l q x) := by
  unfold Certificate.ClosedAt
  split <;> infer_instance

/-- The automaton accepts a superset of the configurations that can reach a missing
instruction. Its language excludes the initial configuration. -/
@[mk_iff valid_iff]
private structure Certificate.Valid (c : Certificate) (T : Table) : Prop where
  positive : 0 < c.size
  push_blank : c.push 0 0 = 0
  initial_rejected : c.final.testBit 0 = false
  sink_final : c.final.testBit c.sink = true
  sink_loops : ∀ x : Sym, c.edge c.sink x c.sink = true
  padding : ∀ p : c.Node, c.final.testBit p = ((c.row p 0 &&& c.final) != 0)
  push_lt : ∀ l : Fin c.size, ∀ x : Sym, c.push l x < c.size
  closed : ∀ l q x, c.ClosedAt T l q x

private instance decValid (c : Certificate) (T : Table) : Decidable (c.Valid T) :=
  decidable_of_iff' _ (Certificate.valid_iff c T)

private theorem Certificate.Valid.label_lt {c : Certificate} {T : Table} (hv : c.Valid T)
    (xs : List Sym) : c.label xs < c.size := by
  induction xs with
  | nil => exact hv.positive
  | cons x _ ih => exact hv.push_lt ⟨_, ih⟩ x

private theorem Certificate.Valid.accept_sink {c : Certificate} {T : Table} (hv : c.Valid T)
    (xs : List Sym) : c.Accepts c.sink xs := by
  induction xs with
  | nil => exact hv.sink_final
  | cons x _ ih => exact ⟨⟨c.sink, Nat.lt_succ_self _⟩, hv.sink_loops x, ih⟩

private theorem Certificate.Valid.accept_pad {c : Certificate} {T : Table} (hv : c.Valid T)
    (p : c.Node) (xs : List Sym) (h : c.Accepts p (xs.headD 0 :: xs.tail)) :
    c.Accepts p xs := by
  cases xs with
  | cons => exact h
  | nil =>
    obtain ⟨j, he, hj⟩ := h
    change c.final.testBit p = true
    rw [hv.padding p]
    apply bne_iff_ne.mpr
    intro hz
    have hb := congrArg (fun n : Nat => n.testBit j) hz
    change (c.row p 0).testBit j = true at he
    change c.final.testBit j = true at hj
    simp [Nat.testBit_and, he, hj] at hb

private def ListTape.orient (z : ListTape) : Move → ListTape
  | .right => z
  | .left => ⟨z.right, z.scan, z.left⟩

private theorem ListTape.orient_move (z : ListTape) (w : Sym) (d f : Move) :
    (z.move w d).orient f =
    (z.orient f).move w (if d = f then .right else .left) := by
  cases d <;> cases f <;> rfl

private def Certificate.Safe (c : Certificate) (q : State) (z : ListTape) : Prop :=
  let a := z.orient c.forward
  ¬ c.Accepts (node (c.label a.left) q) (a.scan :: a.right)

private theorem Certificate.Valid.advance {c : Certificate} {T : Table} (hv : c.Valid T)
    {q : State} {z : ListTape} (hs : c.Safe q z) :
    ∃ w d q', T.get q z.scan = some (w, d, q') ∧ c.Safe q' (z.move w d) := by
  let a := z.orient c.forward
  have ha : a.scan = z.scan := by cases hf : c.forward <;> simp [a, ListTape.orient, hf]
  let l : Fin c.size := ⟨c.label a.left, hv.label_lt _⟩
  have hc := hv.closed l q a.scan
  unfold Certificate.ClosedAt at hc
  change ¬ c.Accepts (node l q) (a.scan :: a.right) at hs
  cases ht : T.get q a.scan with
  | none =>
    rw [ht] at hc
    exact False.elim (hs ⟨⟨c.sink, Nat.lt_succ_self _⟩, hc, hv.accept_sink _⟩)
  | some act =>
    obtain ⟨w, d, q'⟩ := act
    rw [ht] at hc
    refine ⟨w, d, q', ha ▸ ht, ?_⟩
    unfold Certificate.Safe
    rw [ListTape.orient_move]
    by_cases hd : d = c.forward
    · simp only [ite_eq_left hd] at hc ⊢
      intro bad
      let p : c.Node := ⟨node (c.push l w) q', by
        have := hv.push_lt l w
        have := q'.isLt
        unfold node
        omega⟩
      exact hs ⟨p, hc, hv.accept_pad p a.right bad⟩
    · simp only [ite_eq_right hd] at hc ⊢
      intro bad
      let b : Fin c.size := ⟨c.label a.left.tail, hv.label_lt _⟩
      have hb : c.push b (a.left.headD 0) = l := by
        change c.push (c.label a.left.tail) (a.left.headD 0) = c.label a.left
        cases a.left with
        | nil => exact hv.push_blank
        | cons => rfl
      obtain ⟨j, he, k, hk, htail⟩ := bad
      have hsub := hc b _ hb j he
      have hbit := congrArg (fun n : Nat => n.testBit k) hsub
      change (c.row j w).testBit k = true at hk
      simp only [Nat.testBit_and, hk, Bool.true_and] at hbit
      exact hs ⟨k, hbit, htail⟩

private theorem Certificate.Valid.not_halts {c : Certificate} {T : Table} (hv : c.Valid T)
    {M : Machine 4} (hm : Supports T M) : ¬ Halts M := by
  have live (t : Nat) : ∃ (p : Point) (h : ℤ) (z : ListTape),
      p.time = t ∧ p.tape = z.pack ∧ Fits M p h ∧ c.Safe p.state z := by
    induction t with
    | zero =>
      let z : ListTape := ⟨[], 0, []⟩
      refine ⟨start, 0, z, rfl, rfl, fits_start M, ?_⟩
      have orient : z.orient c.forward = z := by cases c.forward <;> rfl
      unfold Certificate.Safe
      rw [orient]
      change ¬ c.Accepts 0 [0]
      intro bad
      have hb := hv.accept_pad ⟨0, Nat.zero_lt_succ _⟩ [] bad
      exact Bool.noConfusion (hv.initial_rejected.symm.trans hb)
    | succ t ih =>
      obtain ⟨p, h, z, htime, he, hf, hs⟩ := ih
      obtain ⟨w, d, q', ht, hsafe⟩ := hv.advance hs
      have hscan : p.tape.scan = z.scan := congrArg Tape.scan he
      have hstep := hm _ _ _ _ _ ht
      rw [← hscan] at hstep
      refine ⟨p.next (w, d, q'), h + d.shift, z.move w d, ?_, ?_, hf.next hstep, hsafe⟩
      · simp [Point.next, htime]
      · change p.tape.move w d = (z.move w d).pack
        rw [he, ListTape.pack_move]
  rintro ⟨t, ht⟩
  obtain ⟨p, _, _, htime, _, hf, _⟩ := live t
  rw [← htime] at ht
  exact (Option.some_ne_none p.state) (hf.1.symm.trans ht)

/-- Search for a backwards-closed automaton by saturating its transition rows.
An absent instruction can halt. A forward move adds one edge. For a backward
move, prepend the old neighboring symbol and the written symbol to the right word. -/
private def saturate (T : Table) (rightward : Bool) (delta : List Nat) :
    Option Certificate := Id.run do
  let k := delta.length / 2
  let sink := 4 * k
  let forward := if rightward then Move.right else Move.left
  let push := fun (l : Nat) (x : Sym) => delta[2 * l + x.val]?.getD 0
  let mut rows := Array.replicate (2 * (sink + 1)) 0
  let mut rules : Array (Nat × Nat × Nat) := #[]
  for x in [:2] do
    rows := rows.set! (2 * sink + x) (1 <<< sink)
  for l in [:k] do
    for q in List.finRange 4 do
      for x in List.finRange 2 do
        let dst := 2 * node l q + x.val
        match T.get q x with
        | none => rows := rows.set! dst (1 <<< sink)
        | some (w, d, q') =>
          if d = forward then rows := rows.set! dst (1 <<< node (push l w) q')
          else
            for b in [:k] do
              for y in List.finRange 2 do
                if push b y = l then
                  rules := rules.push (dst, 2 * node b q' + y.val, w.val)
  for _ in [:2 * (sink + 1) ^ 2 + 1] do
    let mut changed := false
    for (dst, src, w) in rules do
      let old := rows[dst]!
      let mut mask := old
      for j in [:sink + 1] do
        if rows[src]!.testBit j then mask := mask ||| rows[2 * j + w]!
      if mask != old then
        rows := rows.set! dst mask
        changed := true
    if rows[0]!.testBit sink then return none
    if !changed then
      -- The states accepting an all-blank suffix are closed under reading a blank.
      let mut final := 1 <<< sink
      for _ in [:sink + 1] do
        for p in [:sink] do
          if rows[2 * p]! &&& final != 0 then final := final ||| (1 <<< p)
      if final.testBit 0 then return none
      return some ⟨k, rightward, delta, rows.toList, final⟩
  return none

-- These two deterministic automata complement the finite-window search.
private def findAutomaton (T : Table) : Option Certificate :=
  (saturate T false [0, 1, 2, 0, 2, 2]).orElse fun _ =>
    saturate T false [0, 1, 2, 0, 3, 4, 3, 3, 3, 2]

/-- The checker tracks a finite window to each side of the head. Some certificates
also store the last few writers of each cell to distinguish otherwise identical windows. -/
private structure WindowSpec where
  radius : Nat
  history : Nat
  deriving Lean.ToExpr

private def WindowSpec.read (s : WindowSpec) (T : Table) (tag : Nat) : Sym :=
  if s.history = 0 then ⟨tag % 2, Nat.mod_lt _ (by decide)⟩
  else if tag % 9 = 0 then 0
  else ((T.entries[tag % 9 - 1]?.getD none).map Prod.fst).getD 0

private def WindowSpec.tag (s : WindowSpec) (q : State) (x w : Sym) (old : Nat) : Nat :=
  if s.history = 0 then w.val
  else 1 + index q x + 9 * (old % (9 ^ (s.history - 1)))

private theorem WindowSpec.read_blank (s : WindowSpec) (T : Table) :
    s.read T 0 = 0 := by
  by_cases hs : s.history = 0 <;> simp [WindowSpec.read, hs]

private theorem WindowSpec.read_tag (s : WindowSpec) {T : Table} {q : State} {x w : Sym}
    {d : Move} {r : State} (ha : T.get q x = some (w, d, r)) (old : Nat) :
    s.read T (s.tag q x w old) = w := by
  by_cases hs : s.history = 0
  · simp [WindowSpec.read, WindowSpec.tag, hs, Nat.mod_eq_of_lt w.isLt]
  · have hi := index_lt q x
    have hmod : (1 + index q x + 9 * (old % 9 ^ (s.history - 1))) % 9 = 1 + index q x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hpos : 1 + index q x ≠ 0 := by omega
    simp only [WindowSpec.read, WindowSpec.tag, hs, hmod, hpos, ite_false]
    rw [show 1 + index q x - 1 = index q x by omega]
    change ((T.get q x).map Prod.fst).getD 0 = w
    rw [ha]
    rfl

private structure Window where
  state : State
  scan : Nat
  left : List Nat
  right : List Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Lean.ToExpr

private def Window.side (p : Window) : Move → List Nat
  | .left => p.left
  | .right => p.right

private def Window.advance (p : Window) (d : Move) (q : State) (pushed popped : List Nat) :
    Window :=
  let x := (p.side d).headD 0
  match d with
  | .left => ⟨q, x, popped, pushed⟩
  | .right => ⟨q, x, pushed, popped⟩

private structure Windows where
  spec : WindowSpec
  left : List (List Nat)
  right : List (List Nat)
  live : List Window
  deriving Lean.ToExpr

private def Windows.side (c : Windows) : Move → List (List Nat)
  | .left => c.left
  | .right => c.right

private def WindowSpec.blankSide (s : WindowSpec) : List Nat :=
  List.replicate (s.radius + 1) 0

private def WindowSpec.blank (s : WindowSpec) : Window :=
  ⟨0, 0, s.blankSide, s.blankSide⟩

private def Windows.closed (c : Windows) (T : Table) (p : Window) : Bool :=
  let x := c.spec.read T p.scan
  match T.get p.state x with
  | none => false
  | some (w, d, q) =>
    let behind := reverseMove d
    let pushed := c.spec.tag p.state x w p.scan :: (p.side behind).take c.spec.radius
    decide (pushed ∈ c.side behind) &&
      (c.side d).all fun popped =>
        if popped.take c.spec.radius = (p.side d).tail then
          decide (p.advance d q pushed popped ∈ c.live)
        else true

private def Windows.valid (c : Windows) (T : Table) : Bool :=
  decide (c.spec.blankSide ∈ c.left) && decide (c.spec.blankSide ∈ c.right) &&
    decide (c.spec.blank ∈ c.live) && c.live.all (c.closed T)

private def word (t : ℤ → Nat) (pos : ℤ) (d : Move) : Nat → List Nat
  | 0 => []
  | n + 1 => t pos :: word t (pos + d.shift) d n

private theorem take_word (t : ℤ → Nat) (pos : ℤ) (d : Move) (n : Nat) :
    (word t pos d (n + 1)).take n = word t pos d n := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih => rw [word, List.take_succ_cons, ih, word]

private theorem blank_word (pos : ℤ) (d : Move) (n : Nat) :
    word (fun _ => 0) pos d n = List.replicate n 0 := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih => simp only [word, List.replicate_succ, ih]

private def OnSide (d : Move) (head i : ℤ) : Prop :=
  match d with
  | .left => i < head
  | .right => head < i

private theorem word_update (t : ℤ → Nat) {head i : ℤ} (tag : Nat) {d : Move}
    (hi : OnSide d head i) (n : Nat) :
    word (Function.update t head tag) i d n = word t i d n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [word]
    have hne : i ≠ head := by cases d <;> simp [OnSide] at hi <;> omega
    have hnext : OnSide d head (i + d.shift) := by
      cases d <;> simp [OnSide, Move.shift] at hi ⊢ <;> omega
    rw [Function.update_of_ne hne, ih hnext]

private def WindowSpec.view (s : WindowSpec) (t : ℤ → Nat) (h : ℤ) (q : State) : Window :=
  ⟨q, t h, word t (h - 1) .left (s.radius + 1), word t (h + 1) .right (s.radius + 1)⟩

private theorem WindowSpec.view_side (s : WindowSpec) (t : ℤ → Nat) (h : ℤ)
    (q : State) (d : Move) :
    (s.view t h q).side d = word t (h + d.shift) d (s.radius + 1) := by
  cases d <;> rfl

private def Windows.covers (c : Windows) (t : ℤ → Nat) (h : ℤ) : Prop :=
  ∀ d i, OnSide d h i → word t i d (c.spec.radius + 1) ∈ c.side d

private theorem Windows.can_advance {c : Windows} {T : Table}
    (valid : c.valid T = true) {t : ℤ → Nat} {h : ℤ} {q : State}
    (hc : c.covers t h) (hv : c.spec.view t h q ∈ c.live) :
    ∃ w d q', T.get q (c.spec.read T (t h)) = some (w, d, q') ∧
      let t' := Function.update t h (c.spec.tag q (c.spec.read T (t h)) w (t h))
      c.covers t' (h + d.shift) ∧ c.spec.view t' (h + d.shift) q' ∈ c.live := by
  obtain ⟨_, hclosed⟩ := Bool.and_eq_true_iff.mp valid
  have hl := List.all_eq_true.mp hclosed _ hv
  let p := c.spec.view t h q
  let x := c.spec.read T (t h)
  change c.closed T p = true at hl
  unfold Windows.closed at hl
  cases ha : T.get q x with
  | none =>
    simp [x, p, WindowSpec.view, ha] at hl
  | some a =>
    obtain ⟨w, d, q'⟩ := a
    let behind := reverseMove d
    let tag := c.spec.tag q x w (t h)
    let t' := Function.update t h tag
    let A := word t' h behind (c.spec.radius + 1)
    let far := h + d.shift + d.shift
    let B := word t far d (c.spec.radius + 1)
    have hside : OnSide behind h (h + behind.shift) := by
      cases d <;> simp [behind, reverseMove, OnSide, Move.shift]
    have hA : A = tag :: (p.side behind).take c.spec.radius := by
      unfold A t'
      rw [word, Function.update_self, word_update _ _ hside, WindowSpec.view_side, take_word]
    have hpos : OnSide d h far := by
      cases d <;> simp [far, OnSide, Move.shift]
    have hB : B ∈ c.side d := hc d far hpos
    have htake : B.take c.spec.radius = (p.side d).tail := by
      rw [WindowSpec.view_side, word, List.tail_cons]
      exact take_word ..
    have hakey : T.get p.state (c.spec.read T p.scan) = some (w, d, q') := ha
    dsimp only at hl
    rw [hakey] at hl
    change (decide ((tag :: (p.side behind).take c.spec.radius) ∈ c.side behind) &&
      (c.side d).all fun v => if v.take c.spec.radius = (p.side d).tail then
        decide (p.advance d q' (tag :: (p.side behind).take c.spec.radius) v ∈ c.live)
        else true) = true at hl
    rw [← hA] at hl
    obtain ⟨hpush, hpop⟩ := Bool.and_eq_true_iff.mp hl
    have hpush : A ∈ c.side behind := of_decide_eq_true hpush
    have hnew := List.all_eq_true.mp hpop B hB
    rw [ite_eq_left htake] at hnew
    refine ⟨w, d, q', rfl, ?_, ?_⟩
    · intro e i hi
      by_cases he : e = d
      · subst e
        have hi' : OnSide d h i := by cases d <;> simp [OnSide, Move.shift] at hi ⊢ <;> omega
        rw [word_update _ _ hi']
        exact hc _ _ hi'
      · have heb : e = behind := by cases e <;> cases d <;> first | contradiction | rfl
        rcases eq_or_ne i h with rfl | hne
        · exact heb ▸ hpush
        · have hi' : OnSide e h i := by
            subst e
            cases d <;> simp [behind, OnSide, reverseMove, Move.shift] at hi ⊢ <;> omega
          rw [word_update _ _ hi']
          exact hc _ _ hi'
    · suffices he : c.spec.view t' (h + d.shift) q' = p.advance d q' A B by
        rw [he]
        exact of_decide_eq_true hnew
      have hs : t' (h + d.shift) = t (h + d.shift) := by
        apply Function.update_of_ne
        cases d <;> simp [Move.shift]
      have hscan : (p.side d).headD 0 = t (h + d.shift) := by
        rw [WindowSpec.view_side, word]
        rfl
      have hfar : word t' far d (c.spec.radius + 1) = B := word_update _ _ hpos _
      have hcancel : h + d.shift + behind.shift = h := by
        rw [reverseMove_shift]
        omega
      cases d <;> simp only [WindowSpec.view, Window.advance, Move.shift] at hs hscan ⊢ <;>
        simp only [behind, reverseMove, Move.shift] at hfar hcancel A B <;> congr 1
      all_goals
        simp only [sub_eq_add_neg, hcancel]
        rfl

private theorem Windows.not_halts {c : Windows} {T : Table}
    (valid : c.valid T = true) {M : Machine 4} (hm : Supports T M) : ¬ Halts M := by
  have live (n : Nat) : ∃ (q : State) (h : ℤ) (t : ℤ → Nat), (run M n).state = some q ∧
      (run M n).head = h ∧ (∀ i, (run M n).tape i = c.spec.read T (t i)) ∧
      c.covers t h ∧ c.spec.view t h q ∈ c.live := by
    induction n with
    | zero =>
      have hinit := (Bool.and_eq_true_iff.mp valid).1
      obtain ⟨hside, hzero⟩ := Bool.and_eq_true_iff.mp hinit
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hside
      refine ⟨0, 0, fun _ => 0, rfl, rfl, fun i => ?_, ?_, ?_⟩
      · exact (c.spec.read_blank T).symm
      · intro d i _
        rw [blank_word]
        cases d
        · exact of_decide_eq_true hl
        · exact of_decide_eq_true hr
      · simpa only [WindowSpec.view, WindowSpec.blank, WindowSpec.blankSide, blank_word] using
          (of_decide_eq_true hzero : c.spec.blank ∈ c.live)
    | succ n ih =>
      obtain ⟨q, h, t, hq, hh, ht, hc, hv⟩ := ih
      obtain ⟨w, d, q', ha, hc', hv'⟩ := c.can_advance valid hc hv
      let x := c.spec.read T (t h)
      let tag := c.spec.tag q x w (t h)
      let t' := Function.update t h tag
      have hstep := hm _ _ _ _ _ ha
      rw [run_succ, step_of_state_some M hq, hh, ht h, hstep]
      refine ⟨q', h + d.shift, t', rfl, rfl, fun i => ?_, hc', hv'⟩
      change Function.update (run M n).tape h w i = c.spec.read T (t' i)
      by_cases e : i = h
      · subst i
        simp only [Function.update_self, t']
        exact (c.spec.read_tag ha (t h)).symm
      · unfold t'
        rw [Function.update_of_ne e, Function.update_of_ne e, ht]
  rintro ⟨n, h⟩
  obtain ⟨_, _, _, hs, _⟩ := live n
  exact Option.some_ne_none _ (hs.symm.trans h)

/-- Close the windows and the two sets of side words under the abstract transitions.
The checker independently verifies the resulting lists. -/
private def suggestWindows (s : WindowSpec) (T : Table) : Option Windows := Id.run do
  let blank := s.blankSide
  let mut left := #[blank]
  let mut right := #[blank]
  let mut live := #[s.blank]
  let mut seen := ({} : Std.HashSet Window).insert s.blank
  for _ in [:256] do
    let oldSize := left.size + right.size + live.size
    for i in [:live.size] do
      let some p := live[i]? | return none
      let x := s.read T p.scan
      let some (w, d, q) := T.get p.state x | return none
      let pushed := s.tag p.state x w p.scan :: (p.side (reverseMove d)).take s.radius
      let pops := match d with
        | .left => left
        | .right => right
      match d with
      | .left => if !right.contains pushed then right := right.push pushed
      | .right => if !left.contains pushed then left := left.push pushed
      let near := (p.side d).tail
      for popped in pops do
        if popped.take s.radius == near then
          let next := p.advance d q pushed popped
          if !seen.contains next then
            seen := seen.insert next
            live := live.push next
      if live.size > 3000 then return none
    if oldSize == left.size + right.size + live.size then
      return some ⟨s, left.toList, right.toList, live.toList⟩
  return none

private def findWindows (T : Table) : Option Windows :=
  let modes : List (Nat × Nat) :=
    [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (2, 2), (4, 0), (4, 1), (2, 3),
      (3, 2), (2, 4), (3, 3), (3, 4), (2, 5), (2, 7), (2, 8), (3, 8)]
  modes.findSome? fun (width, history) => suggestWindows ⟨width - 1, history⟩ T

private inductive Hint
  | branch (children : List Hint)
  | cycle (s : Scope) (wait period : Nat)
  | windows (c : Windows)
  | automaton (c : Certificate)
  | bad
deriving Lean.ToExpr

private structure Anchor where
  head : Int
  state : State
  scan : Sym
  side : Nat
  time : Nat

private def Anchor.agrees (a : Anchor) (p : Point) (side : Nat) : Bool :=
  a.state == p.state && a.scan == p.tape.scan && a.side == side

private def Point.key (p : Point) : State × Sym × Nat × Nat :=
  (p.state, p.tape.scan, p.tape.left, p.tape.right)

/-- Find a repeated configuration, or a repeat whose future avoids one half of the tape. -/
private def classify (T : Table) (p : Point) : Point ⊕ Hint := Id.run do
  let mut seen := ({} : Std.HashMap (State × Sym × Nat × Nat) Nat).insert p.key 0
  let mut right : List Anchor := [⟨0, p.state, p.tape.scan, p.tape.right, 0⟩]
  let mut left : List Anchor := [⟨0, p.state, p.tape.scan, p.tape.left, 0⟩]
  let mut r := p
  let mut head : Int := 0
  for t in [:300] do
    let some a := T.get r.state r.tape.scan
      | return if r.time < 107 then .inl r else .inr .bad
    r := r.next a
    head := head + a.2.1.shift
    if let some j := seen[r.key]? then return .inr (.cycle .all j (t + 1 - j))
    right := right.dropWhile fun a => a.head > head
    left := left.dropWhile fun a => a.head < head
    if let some a := right.find? (·.agrees r r.tape.right) then
      return .inr (.cycle .right a.time (t + 1 - a.time))
    if let some a := left.find? (·.agrees r r.tape.left) then
      return .inr (.cycle .left a.time (t + 1 - a.time))
    seen := seen.insert r.key (t + 1)
    right := ⟨head, r.state, r.tape.scan, r.tape.right, t + 1⟩ :: right
    left := ⟨head, r.state, r.tape.scan, r.tape.left, t + 1⟩ :: left
  return .inr .bad

private def advise : Nat → Table → Point → Hint
  | 0, _, _ => .bad
  | n + 1, T, p =>
    match classify T p with
    | .inr .bad =>
      (findWindows T).map Hint.windows |>.orElse
        (fun _ => (findAutomaton T).map Hint.automaton) |>.getD .bad
    | .inr hint => hint
    | .inl r =>
      if last T r then .branch []
      else .branch ((actions T).map fun a => advise n (extend T r a) (r.next a))

private def champion : Machine 4
  | 0, 0 => (1, .right, some 1)
  | 0, _ => (1, .left, some 1)
  | 1, 0 => (1, .left, some 0)
  | 1, _ => (0, .left, some 2)
  | 2, 0 => (1, .right, none)
  | 2, _ => (1, .left, some 3)
  | _, 0 => (1, .right, some 3)
  | _, _ => (0, .right, some 0)

private theorem lower : 107 ≤ busyBeaverSteps 4 := by
  have h₁₀₇ : HaltsWithin champion 107 := by
    change (run champion 107).state = none
    decide +kernel
  have h₁₀₆ : ¬ HaltsWithin champion 106 := by
    change (run champion 106).state ≠ none
    decide +kernel
  have h : Halts champion := ⟨107, h₁₀₇⟩
  have ht : 107 ≤ haltTime champion h := by
    by_contra! hlt
    exact h₁₀₆ (haltsWithin_mono (haltsWithin_haltTime _ h) (by omega))
  exact ht.trans (haltTime_le_busyBeaverSteps _ h)

private def check : Nat → Table → Point → Hint → Bool
  | _, T, p, .cycle s wait period => verifiesCycle T p s wait period
  | _, T, _, .windows c => c.valid T
  | _, T, _, .automaton c => decide (c.Valid T)
  | n + 1, T, p, .branch kids =>
    match probe T (107 - p.time) p with
    | none => false
    | some r => last T r || (List.finRange (actions T).length).all fun i =>
      let a := (actions T)[i.val]
      check n (extend T r a) (r.next a) (kids[i.val]?.getD .bad)
  | _, _, _, _ => false

private theorem check_sound {fuel : Nat} {T : Table} {p : Point} {hint : Hint}
    (hc : check fuel T p hint = true) (hs : StatesBounded T)
    (hp : p.state ≤ T.maxState) (ht : p.time ≤ 107) : Bounded T p := by
  induction fuel generalizing T p hint with
  | zero | succ fuel ih =>
    cases hint with
    | bad => contradiction
    | cycle s wait period => exact cycle_bound hc
    | windows c =>
      intro M hm _ _
      simp [stepsOf, Windows.not_halts hc hm]
    | automaton c =>
      intro M hm _ _
      simp [stepsOf, (of_decide_eq_true hc : c.Valid T).not_halts hm]
    | branch kids =>
      first
      | contradiction
      | simp only [check] at hc
        split at hc
        next => contradiction
        next r he =>
          intro M hm h hf
          obtain ⟨head, hr, hq, htime⟩ := probe_sound he hm hf hs hp
          have htime : r.time < 107 := by omega
          rcases Bool.or_eq_true_iff.mp hc with hl | hk
          · exact last_bound htime hl hm hr
          · apply branch_bound hs hq htime _ M hm head hr
            intro a ha
            obtain ⟨i, hidx, heq⟩ := List.getElem_of_mem ha
            have hcheck := List.all_eq_true.mp hk ⟨i, hidx⟩ (List.mem_finRange ⟨i, hidx⟩)
            dsimp only at hcheck
            rw [heq] at hcheck
            exact ih hcheck (extend_states hs hq a) (le_max_right _ _) (by
              simp only [Point.next]
              omega)

private structure Job where
  table : Table
  point : Point

private def Job.Valid (j : Job) : Prop :=
  StatesBounded j.table ∧ j.point.state ≤ j.table.maxState ∧ j.point.time ≤ 107

private def refine (job : Job) (i : Fin 16) : Option Job :=
  let ⟨T, p⟩ := job
  match probe T (107 - p.time) p with
  | none => if i = 0 then some job else none
  | some r =>
    if last T r then none
    else (actions T)[i.val]?.map fun a => ⟨extend T r a, r.next a⟩

private def Job.Goal (job : Job) : Prop :=
  job.Valid → Bounded job.table job.point

private theorem refine_sound (job : Job)
    (kids : ∀ (i : Fin 16) (j : Job), refine job i = some j → j.Goal) : job.Goal := by
  obtain ⟨T, p⟩ := job
  intro ⟨hs, hp, ht⟩
  cases he : probe T (107 - p.time) p with
  | none => exact kids 0 _ (by simp [refine, he]) ⟨hs, hp, ht⟩
  | some r =>
    intro M hm h hf
    obtain ⟨head, hr, hq, htime⟩ := probe_sound he hm hf hs hp
    have htime : r.time < 107 := by
      have : p.time ≤ 107 := ht
      omega
    by_cases hl : last T r
    · exact last_bound htime hl hm hr
    · apply branch_bound hs hq htime _ M hm head hr
      intro a ha
      obtain ⟨i, hi, hitem⟩ := List.getElem_of_mem ha
      have len : (actions T).length ≤ 16 := by
        unfold actions
        simp [List.length_flatMap]
        omega
      let key : Fin 16 := ⟨i, hi.trans_le len⟩
      apply kids key (⟨extend T r a, r.next a⟩ : Job)
      · simp [refine, he, hl, key, List.getElem?_eq_getElem hi, hitem]
      · exact ⟨extend_states hs hq a, le_max_right _ _, by simp only [Point.next]; omega⟩

private def rightJob (w : Sym) : Job :=
  let a : Action := (w, .right, 1)
  ⟨extend empty start a, start.next a⟩

private def batch (w : Sym) (j k l : Fin 16) : Option Job := do
  let first ← refine (rightJob w) j
  let second ← refine first k
  refine second l

private def batchHints (w : Sym) (j k l : Fin 16) : Hint :=
  match batch w j k l with
  | none => .bad
  | some job => advise 8 job.table job.point

private def batchCheck (w : Sym) (j k l : Fin 16) (hint : Hint) : Bool :=
  match batch w j k l with
  | none => true
  | some job => check 8 job.table job.point hint

private theorem batch_sound {w : Sym} {j k l : Fin 16} {hint : Hint}
    (hc : batchCheck w j k l hint = true) {job : Job} (hj : batch w j k l = some job) :
    job.Goal := by
  intro ⟨hs, hp, ht⟩
  unfold batchCheck at hc
  rw [hj] at hc
  exact check_sound hc hs hp ht

private theorem rightJob_sound
    (batches : ∀ w j k l, ∃ hs, batchCheck w j k l hs = true) (w : Sym) : (rightJob w).Goal := by
  apply refine_sound
  intro j first hfirst
  apply refine_sound
  intro k second hsecond
  apply refine_sound
  intro l child hchild
  obtain ⟨hs, hcheck⟩ := batches w j k l
  have hbatch : batch w j k l = some child := by
    unfold batch
    rw [hfirst]
    change (refine first k >>= fun next => refine next l) = some child
    rw [hsecond]
    exact hchild
  exact batch_sound hcheck hbatch

private theorem upper_of_batches
    (batches : ∀ w j k l, ∃ hs, batchCheck w j k l hs = true) : busyBeaverSteps 4 ≤ 107 := by
  apply Finset.sup_le
  intro M _
  apply root_bound _ M
  intro w q
  fin_cases q
  · apply cycle_bound (s := .right) (wait := 0) (period := 1)
    fin_cases w <;> decide +kernel
  · apply rightJob_sound batches w
    change StatesBounded (extend empty start (w, .right, 1)) ∧ (1 : State) ≤ max 0 1 ∧ 1 ≤ 107
    exact ⟨extend_states empty_states (le_refl _) _, le_max_right _ _, by decide⟩

/-- A batch of the finite search is certified if the checker accepts advice for each subtree. -/
private def isBatchCertified (w : Sym) (j k : Fin 16) : Prop :=
  ∀ l : Fin 16, ∃ hint, batchCheck w j k l hint = true

@[inherit_doc isBatchCertified]
public def BatchCertified (w : Fin 2) (j k : Fin 16) : Prop :=
  isBatchCertified w j k

private theorem certify_absent_row {w : Sym} {j : Fin 16}
    (h : refine (rightJob w) j = none) (k : Fin 16) : BatchCertified w j k := by
  intro l
  exact ⟨.bad, by simp [batchCheck, batch, h]⟩

public theorem value_of_batches (checked : ∀ w j k, BatchCertified w j k) :
    busyBeaverSteps 4 = 107 :=
  le_antisymm (upper_of_batches checked) lower

-- Check separate subtrees so the kernel can release intermediate reductions between checks.
open Lean in
macro "checkFourStateBatches" w:num j:num k:term : tactic => do
  let proofs ← (List.range 16).toArray.mapM fun index => do
    let middle := Syntax.mkNumLit (toString index)
    let subproofs ← (List.range 16).toArray.mapM fun subindex => do
      let last := Syntax.mkNumLit (toString subindex)
      `(tactic| · exact ⟨eval% batchHints $w $j $middle $last, by decide +kernel⟩)
    `(tactic| · intro l
                fin_cases l
                $subproofs*)
  `(tactic| (
    fin_cases $k:term
    $proofs*
  ))

end busyBeaverSteps_four_wanted

end Cslib.BusyBeaverWanted
