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
# Three-state Busy Beaver score

The theorem `busyBeaverOnes_three_wanted` gives the maximum score of six on the
blank tape. The lower bound runs one machine to
completion. For the upper bound, follow each partial table to its first missing
instruction and check the score if that instruction halts. Split on the possible
continuing instructions. For paths that run for 21 steps without a missing
instruction, finite automata certify that no missing instruction can ever be reached.
This also bounds the runtime of every halting three-state machine by 21.
-/

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

private abbrev Sym := Fin 2
private abbrev State := Fin 3
private abbrev Action := Sym × Move × State
private abbrev Table := State → Sym → Option Action

/-- The lists start at the nearest cell and end in implicit blanks. -/
private structure Zipper where
  left : List Sym
  scan : Sym
  right : List Sym

private def Zipper.read (z : Zipper) : ℤ → Sym
  | .ofNat 0 => z.scan
  | .ofNat (n + 1) => z.right[n]?.getD 0
  | .negSucc n => z.left[n]?.getD 0

private def Zipper.shift (z : Zipper) (w : Sym) : Move → Zipper
  | .right => ⟨w :: z.left, z.right.headD 0, z.right.tail⟩
  | .left => ⟨z.left.tail, z.left.headD 0, w :: z.right⟩

private theorem Zipper.read_shift (z : Zipper) (w : Sym) (d : Move) (i : ℤ) :
    (z.shift w d).read i = if i + d.shift = 0 then w else z.read (i + d.shift) := by
  obtain ⟨l, s, r⟩ := z
  cases d <;> cases i with
  | ofNat n =>
    cases n with
    | zero => cases r <;> cases l <;> rfl
    | succ n =>
      cases n with
      | zero => cases r <;> cases l <;> rfl
      | succ k =>
        first
        | rw [show Int.ofNat (k + 1 + 1) + Move.left.shift = Int.ofNat (k + 1) by
            change (k : ℤ) + 1 + 1 + (-1) = k + 1
            omega]
          cases r <;> rfl
        | cases r <;> rfl
  | negSucc n =>
    cases n <;> cases l <;> cases r <;> rfl

private def blank : Zipper := ⟨[], 0, []⟩

private def Fits (M : Machine 3) (t : ℕ) (q : State) (h : ℤ) (z : Zipper) : Prop :=
  (run M t).state = some q ∧ (run M t).head = h ∧
    ∀ i, (run M t).tape i = z.read (i - h)

private theorem fits_blank (M : Machine 3) : Fits M 0 0 0 blank := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  rw [sub_zero]
  cases i with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem Fits.step {M : Machine 3} {t q h z} (hf : Fits M t q h z)
    {w d q'} (ha : M q z.scan = (w, d, some q')) :
    Fits M (t + 1) q' (h + d.shift) (z.shift w d) := by
  obtain ⟨hs, hh, ht⟩ := hf
  have readHead := ht h
  rw [sub_self] at readHead
  change (run M t).tape h = z.scan at readHead
  unfold Fits
  rw [run_succ, step_of_state_some _ hs, hh, readHead, ha]
  refine ⟨rfl, rfl, fun i => ?_⟩
  rw [Zipper.read_shift, show i - (h + d.shift) + d.shift = i - h by abel]
  by_cases hi : i = h
  · subst i
    simp
  · simp [Function.update_of_ne hi, ht, sub_ne_zero.mpr hi]

private def Supports (T : Table) (M : Machine 3) : Prop :=
  ∀ q x w d q', T q x = some (w, d, q') → M q x = (w, d, some q')

/-- A finite automaton reads the left half-tape from the blank end. A nondeterministic
automaton reads the right half starting at the head. Its states are pairs consisting of
a left-automaton state and a working state, together with one accepting sink. -/
private structure Certificate where
  size : Nat
  forward : Move
  delta : List Nat
  rows : List Nat
  final : Nat

private abbrev Certificate.Node (c : Certificate) := Fin (3 * c.size + 1)

private def Certificate.push (c : Certificate) (l : Nat) (x : Sym) :=
  c.delta[2 * l + x.val]?.getD 0

private def Certificate.row (c : Certificate) (p : Nat) (x : Sym) :=
  c.rows[2 * p + x.val]?.getD 0

private def Certificate.edge (c : Certificate) (p : Nat) (x : Sym) (j : Nat) : Bool :=
  (c.row p x).testBit j

private def node (l : Nat) (q : State) := 3 * l + q.val

private def Certificate.sink (c : Certificate) := 3 * c.size

private def Certificate.Accepts (c : Certificate) (p : Nat) : List Sym → Prop
  | [] => c.final.testBit p
  | x :: xs => ∃ j : c.Node, c.edge p x j ∧ c.Accepts j xs

private def Certificate.label (c : Certificate) : List Sym → Nat
  | [] => 0
  | x :: xs => c.push (c.label xs) x

private def Certificate.ClosedAt (c : Certificate) (T : Table) (l : Fin c.size)
    (q : State) (x : Sym) : Prop :=
  match T q x with
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

private def Zipper.orient (z : Zipper) : Move → Zipper
  | .right => z
  | .left => ⟨z.right, z.scan, z.left⟩

private theorem Zipper.orient_shift (z : Zipper) (w : Sym) (d f : Move) :
    (z.shift w d).orient f =
    (z.orient f).shift w (if d = f then .right else .left) := by
  cases d <;> cases f <;> rfl

private def Certificate.Safe (c : Certificate) (q : State) (z : Zipper) : Prop :=
  let a := z.orient c.forward
  ¬ c.Accepts (node (c.label a.left) q) (a.scan :: a.right)

private theorem Certificate.Valid.advance {c : Certificate} {T : Table} (hv : c.Valid T)
    {q : State} {z : Zipper} (hs : c.Safe q z) :
    ∃ w d q', T q z.scan = some (w, d, q') ∧ c.Safe q' (z.shift w d) := by
  let a := z.orient c.forward
  have ha : a.scan = z.scan := by cases hf : c.forward <;> simp [a, Zipper.orient, hf]
  let l : Fin c.size := ⟨c.label a.left, hv.label_lt _⟩
  have hc := hv.closed l q a.scan
  unfold Certificate.ClosedAt at hc
  change ¬ c.Accepts (node l q) (a.scan :: a.right) at hs
  cases ht : T q a.scan with
  | none =>
    rw [ht] at hc
    exact False.elim (hs ⟨⟨c.sink, Nat.lt_succ_self _⟩, hc, hv.accept_sink _⟩)
  | some act =>
    obtain ⟨w, d, q'⟩ := act
    rw [ht] at hc
    refine ⟨w, d, q', ha ▸ ht, ?_⟩
    unfold Certificate.Safe
    rw [Zipper.orient_shift]
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
    {M : Machine 3} (hm : Supports T M) : ¬ Halts M := by
  have live (t : Nat) : ∃ q h z, Fits M t q h z ∧ c.Safe q z := by
    induction t with
    | zero =>
      refine ⟨0, 0, blank, fits_blank M, ?_⟩
      have orient : blank.orient c.forward = blank := by cases c.forward <;> rfl
      unfold Certificate.Safe
      rw [orient]
      change ¬ c.Accepts 0 [0]
      intro bad
      have hb := hv.accept_pad ⟨0, Nat.zero_lt_succ _⟩ [] bad
      exact Bool.noConfusion (hv.initial_rejected.symm.trans hb)
    | succ t ih =>
      obtain ⟨q, h, z, hf, hs⟩ := ih
      obtain ⟨w, d, q', ht, hsafe⟩ := hv.advance hs
      exact ⟨_, _, _, hf.step (hm _ _ _ _ _ ht), hsafe⟩
  rintro ⟨t, ht⟩
  obtain ⟨q, _, _, hf, _⟩ := live t
  exact (Option.some_ne_none q) (hf.1.symm.trans ht)

private structure Stop where
  state : State
  head : ℤ
  tape : Zipper
  time : ℕ

private def Stop.next (p : Stop) (a : Action) : Stop :=
  ⟨a.2.2, p.head + a.2.1.shift, p.tape.shift a.1 a.2.1, p.time + 1⟩

/-- Stop at the first instruction absent from the partial table. -/
private def probe (T : Table) : Nat → Stop → Option Stop
  | 0, _ => none
  | fuel + 1, p =>
    match T p.state p.tape.scan with
    | none => some p
    | some a => probe T fuel (p.next a)

private def start : Stop := ⟨0, 0, blank, 0⟩

private theorem probe_fits {M : Machine 3} {T : Table} (hm : Supports T M)
    (fuel : Nat) {p e : Stop} (hp : Fits M p.time p.state p.head p.tape)
    (he : probe T fuel p = some e) :
    Fits M e.time e.state e.head e.tape ∧ e.time < p.time + fuel := by
  induction fuel generalizing p with
  | zero => contradiction
  | succ n ih =>
    unfold probe at he
    split at he
    next =>
      cases he
      exact ⟨hp, by omega⟩
    next a ht =>
      obtain ⟨w, d, q⟩ := a
      obtain ⟨hf, htime⟩ := ih (hp.step (hm _ _ _ _ _ ht)) he
      change e.time < p.time + 1 + n at htime
      exact ⟨hf, by omega⟩

/-- Upper bound if a missing instruction halts here, allowing a final write of one. -/
private def Stop.upper (p : Stop) : Nat :=
  ((Finset.Icc (-((p.time + 1 : ℕ) : ℤ)) ((p.time + 1 : ℕ) : ℤ)).filter
    fun i => i = p.head ∨ p.tape.read (i - p.head) = 1).card

private theorem Stop.bounds {M : Machine 3} {p : Stop}
    (hf : Fits M p.time p.state p.head p.tape) {w d}
    (ha : M p.state p.tape.scan = (w, d, none)) :
    scoreOf M ≤ p.upper ∧ stepsOf M = p.time + 1 := by
  obtain ⟨hs, hh, ht⟩ := hf
  have readHead := ht p.head
  rw [sub_self] at readHead
  change (run M p.time).tape p.head = p.tape.scan at readHead
  have hstep := step_of_state_some M hs
  rw [hh, readHead, ha] at hstep
  have hh₁ : HaltsWithin M (p.time + 1) := by
    unfold HaltsWithin
    rw [run_succ, hstep]
  have halts : Halts M := ⟨_, hh₁⟩
  have time_eq : haltTime M halts = p.time + 1 := by
    have hb := haltTime_le M halts hh₁
    by_contra! hn
    have h := haltsWithin_mono (haltsWithin_haltTime _ halts)
      (show haltTime M halts ≤ p.time by omega)
    exact (Option.some_ne_none _) (hs.symm.trans h)
  refine ⟨?_, by simpa only [stepsOf, dite_eq_left halts] using time_eq⟩
  rw [scoreOf, dite_eq_left halts, time_eq, onesAt, run_succ, hstep]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hwin, hval⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hwin, ?_⟩
  by_cases heq : i = p.head
  · exact Or.inl heq
  · change Function.update (run M p.time).tape p.head w i = 1 at hval
    rw [Function.update_of_ne heq, ht] at hval
    exact Or.inr hval

private def extend (T : Table) (p : Stop) (a : Action) : Table :=
  fun q x => if q = p.state ∧ x = p.tape.scan then some a else T q x

private def Bounded (T : Table) : Prop :=
  ∀ M, Supports T M → scoreOf M ≤ 6 ∧ stepsOf M ≤ 21

private def action (i : Fin 12) : Action :=
  (⟨i / 6, by omega⟩, if i.val / 3 % 2 = 0 then .left else .right, ⟨i % 3, by omega⟩)

private theorem action_surjective : Function.Surjective action := by decide +kernel

private theorem branch_bound {T : Table} {p : Stop} (he : probe T 21 start = some p)
    (hu : p.upper ≤ 6) (hchild : ∀ i, Bounded (extend T p (action i))) : Bounded T := by
  intro M hm
  obtain ⟨hf, htime⟩ := probe_fits hm 21 (fits_blank M) he
  change p.time < 21 at htime
  obtain ⟨w, d, next, ht⟩ : ∃ w d q, M p.state p.tape.scan = (w, d, q) :=
    ⟨_, _, _, rfl⟩
  cases next with
  | none =>
    obtain ⟨hs, ht⟩ := Stop.bounds hf ht
    exact ⟨hs.trans hu, by omega⟩
  | some q' =>
    obtain ⟨i, hi⟩ := action_surjective (w, d, q')
    apply hchild i M
    intro q x v dir next h
    unfold extend at h
    split at h
    next hqx =>
      obtain ⟨rfl, rfl⟩ := hqx
      rw [hi] at h
      cases h
      exact ht
    next => exact hm _ _ _ _ _ h

private theorem full_bound {T : Table} (h : ∀ q x, (T q x).isSome = true) : Bounded T := by
  intro M hm
  have live (t : Nat) : (run M t).state ≠ none := by
    induction t with
    | zero => exact Option.some_ne_none (0 : State)
    | succ t ih =>
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ih
      let x := (run M t).tape (run M t).head
      obtain ⟨⟨w, d, q'⟩, ht⟩ := Option.isSome_iff_exists.mp (h q x)
      rw [run_succ, step_state_of_some _ hq, hm _ _ _ _ _ ht]
      exact Option.some_ne_none _
  have hn : ¬ Halts M := fun ⟨t, ht⟩ => live t ht
  simp [scoreOf, stepsOf, hn]

/-- All other instructions are known to continue. -/
private def LastEntry (T : Table) (p : Stop) : Prop :=
  ∀ q x, (q = p.state ∧ x = p.tape.scan) ∨ (T q x).isSome = true

private instance decLastEntry (T : Table) (p : Stop) : Decidable (LastEntry T p) := by
  unfold LastEntry
  infer_instance

private theorem last_bound {T : Table} {p : Stop} (he : probe T 21 start = some p)
    (hu : p.upper ≤ 6) (hl : LastEntry T p) : Bounded T := by
  apply branch_bound he hu
  intro i
  apply full_bound
  intro q x
  unfold extend
  split
  · rfl
  next h => exact (hl q x).resolve_left h

/-- Search advice. Every leaf is checked against its partial instruction table. -/
private inductive Advice where
  | last
  | loop (rightward : Bool) (delta rows : List Nat) (final : Nat)
  | branch (children : List Advice)
  deriving Lean.ToExpr

private def cert (rightward : Bool) (delta rows : List Nat) (final : Nat) : Certificate :=
  ⟨delta.length / 2, if rightward then .right else .left, delta, rows, final⟩

private def check : Nat → Table → Advice → Bool
  | _, T, .loop d l r b => decide ((cert d l r b).Valid T)
  | _, T, .last =>
    match probe T 21 start with
    | none => false
    | some p => decide (p.upper ≤ 6 ∧ LastEntry T p)
  | 0, _, .branch _ => false
  | n + 1, T, .branch kids =>
    match probe T 21 start with
    | none => false
    | some p => decide (p.upper ≤ 6) &&
      (List.finRange 12).all fun i => check n (extend T p (action i)) (kids[i.val]?.getD .last)

private theorem check_sound (n : Nat) (T : Table) (a : Advice) (h : check n T a = true) :
    Bounded T := by
  induction n generalizing T a with
  | zero | succ n ih =>
    cases a with
    | loop d l r b =>
      have hv : (cert d l r b).Valid T := of_decide_eq_true h
      intro M hm
      simp [scoreOf, stepsOf, hv.not_halts hm]
    | last =>
      simp only [check] at h
      split at h
      · contradiction
      next p hp =>
        obtain ⟨hu, hl⟩ := of_decide_eq_true h
        exact last_bound hp hu hl
    | branch kids =>
      first
      | contradiction
      | simp only [check] at h
        split at h
        · contradiction
        next p hp =>
          obtain ⟨hu, hk⟩ := Bool.and_eq_true_iff.mp h
          apply branch_bound hp (of_decide_eq_true hu)
          intro i
          exact ih _ _ (List.all_eq_true.mp hk i (List.mem_finRange i))

/-- Search for a backwards-closed automaton by saturating its transition rows.
An absent instruction can halt. A forward move adds one edge. For a backward
move, prepend the old neighboring symbol and the written symbol to the right word. -/
private def saturate (T : Table) (rightward : Bool) (delta : List Nat) : Option Advice := Id.run do
  let k := delta.length / 2
  let sink := 3 * k
  let forward := if rightward then Move.right else Move.left
  let push := fun (l : Nat) (x : Sym) => delta[2 * l + x.val]?.getD 0
  let mut rows := Array.replicate (2 * (sink + 1)) 0
  let mut rules : Array (Nat × Nat × Nat) := #[]
  for x in [:2] do
    rows := rows.set! (2 * sink + x) (1 <<< sink)
  for l in [:k] do
    for q in List.finRange 3 do
      for x in List.finRange 2 do
        let dst := 2 * node l q + x.val
        match T q x with
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
      return some (.loop rightward delta rows.toList final)
  return none

/-- Enumerate deterministic left-half automata by increasing size, numbering their states
in discovery order. The initial state reads an extra leading blank as a self-loop. -/
private def completions (k : Nat) : Nat → Nat → List Nat → List (List Nat)
  | 0, used, rev => if used = k then [rev.reverse] else []
  | fuel + 1, used, rev =>
    if rev.length / 2 ≥ used then []
    else (List.range (min k (used + 1))).flatMap fun next =>
      completions k fuel (max used (next + 1)) (next :: rev)

private def findCertificate (T : Table) : Advice :=
  ((List.range 5).findSome? fun n =>
    (completions (n + 1) (2 * n + 1) 1 [0]).findSome? fun delta =>
      (saturate T false delta).orElse fun _ => saturate T true delta).getD .last

private def suggest : Nat → Table → Advice
  | 0, _ => .last
  | n + 1, T =>
    match probe T 21 start with
    | none => findCertificate T
    | some p =>
      if LastEntry T p then .last
      else .branch ((List.finRange 12).map fun i => suggest n (extend T p (action i)))

private def refineTable (T : Table) (i : Fin 12) : Table :=
  match probe T 21 start with
  | none => T
  | some p => extend T p (action i)

private def empty : Table := fun _ _ => none

private def batch (i j : Fin 12) : Table := refineTable (refineTable empty i) j

private def rowAdvice (i : Fin 12) : List Advice :=
  (List.finRange 12).map fun j => suggest 6 (batch i j)

-- Only the certificate data are interpolated. Each batch below is checked by kernel reduction.
set_option maxRecDepth 8192 in
private noncomputable def advice : Fin 12 → List Advice :=
  ![eval% rowAdvice 0, eval% rowAdvice 1, eval% rowAdvice 2, eval% rowAdvice 3,
    eval% rowAdvice 4, eval% rowAdvice 5, eval% rowAdvice 6, eval% rowAdvice 7,
    eval% rowAdvice 8, eval% rowAdvice 9, eval% rowAdvice 10, eval% rowAdvice 11]

set_option maxHeartbeats 0 in
-- The kernel checks the finite automata for all 144 initial batches.
private theorem batch_bound (i j : Fin 12) : Bounded (batch i j) := by
  apply check_sound 6 _ ((advice i)[j.val]?.getD .last)
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem refine_bound (T : Table)
    (hu : ∀ p, probe T 21 start = some p → p.upper ≤ 6)
    (h : ∀ i, Bounded (refineTable T i)) : Bounded T := by
  cases he : probe T 21 start with
  | none => simpa [refineTable, he] using h 0
  | some p =>
    apply branch_bound he (hu p he)
    simpa only [refineTable, he] using h

/-- Every three-state machine scores at most six and takes at most 21 steps if it halts. -/
public theorem busyBeaverSteps_three_wanted.machine_bounds (M : Machine 3) :
    scoreOf M ≤ 6 ∧ stepsOf M ≤ 21 := by
  have below : Bounded empty := by
    apply refine_bound
    · intro p hp
      have he : probe empty 21 start = some start := rfl
      rw [he] at hp
      cases hp
      decide +kernel
    intro i
    apply refine_bound
    · have ok : ∀ k : Fin 12, ((probe (refineTable empty k) 21 start).all
          fun p => decide (p.upper ≤ 6)) = true := by decide +kernel
      intro p hp
      simpa [hp] using ok i
    exact batch_bound i
  exact below M (fun _ _ _ _ _ h => nomatch h)

private theorem upper : busyBeaverOnes 3 ≤ 6 := by
  apply Finset.sup_le
  intro M _
  exact (busyBeaverSteps_three_wanted.machine_bounds M).1

private def champion : Machine 3
  | 0, 0 => (1, .right, some 1)
  | 0, _ => (1, .left, some 2)
  | 1, 0 => (1, .left, some 0)
  | 1, _ => (1, .right, some 1)
  | _, 0 => (1, .left, some 1)
  | _, _ => (1, .right, none)

private theorem lower : 6 ≤ busyBeaverOnes 3 := by
  have h₁₃ : HaltsWithin champion 13 := by
    change (run champion 13).state = none
    decide +kernel
  have h₁₂ : ¬ HaltsWithin champion 12 := by
    change (run champion 12).state ≠ none
    decide +kernel
  have h : Halts champion := ⟨13, h₁₃⟩
  have ht : haltTime champion h = 13 := by
    have := haltTime_le champion h h₁₃
    by_contra! ne
    exact h₁₂ (haltsWithin_mono (haltsWithin_haltTime _ h) (by omega))
  have hs : onesAt champion 13 = 6 := by decide +kernel
  simpa only [scoreOf, dite_eq_left h, ht, hs] using scoreOf_le_busyBeaverOnes champion

/-- **Three-state Busy Beaver score value.** Rado's score function $\Sigma$ satisfies
$\Sigma(3) = 6$: among the two-symbol Busy Beaver machines with $3$ working states that halt when
started on the blank tape, the largest number of ones left on the tape at the halting time is $6$.

Source: Lin--Radó (1965), determination of `Σ(3) = 6`. -/
public theorem busyBeaverOnes_three_wanted :
    busyBeaverOnes 3 = 6 :=
  le_antisymm upper lower

end Cslib.BusyBeaverWanted
