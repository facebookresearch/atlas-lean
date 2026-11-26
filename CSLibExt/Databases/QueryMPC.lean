/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Massively parallel communication for query reporting

Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013),
§§2.1–2.4. Workers exchange arbitrary strings of bits, not just tuples. A round reads the old
private views; all accepted deliveries extend these views simultaneously. Local computation and
storage are unrestricted. In particular a worker can replay any local state machine on its view.
The observer, not any worker, tests the load and takes the final set union.

The paper does not fix a serialization. In this raw-position model the worker count, relation
lengths and wiring are public parameters, fixed before varying the payload bits. The distributed
initial words read exactly the positions prescribed by the wiring; no data-dependent recoding
or layout selection takes place. Alternatively each input server holds its own relation word.
A protocol family is tested on every schedule and every valid payload of its shape. The cap
bounds *delivered* traffic: an oversized proposal aborts the run before any delivery.
-/

@[expose] public section

namespace Cslib.Databases.QueryMPC

open MeasureTheory
open scoped BigOperators

abbrev Bits := List Bool
abbrev Database (k : ℕ) := Fin k → Bits

variable {k p : ℕ} {Ω α : Type*}

/-- An encoded database has one word per relation. Its size in bits is the sum of the lengths
of those words, with no additive allowance for a relation or a server. -/
def inputBits (D : Database k) : ℕ := ∑ j, (D j).length

inductive Start (p k : ℕ) where
  | distributed (shards : Fin p → Bits)
  | separate (relations : Database k)

abbrev Payload (n : Fin k → ℕ) := (j : Fin k) → Fin (n j) → Bool

def Payload.words {n : Fin k → ℕ} (x : Payload n) : Database k := fun j => List.ofFn (x j)

/-- A public layout for a given worker count and relation lengths assigns a finite ordered list
of slots to each worker. Slot counts differ by at most one; a bijection wires the slots to all
relation/offset pairs. There is no bit value in this structure. -/
structure Layout (p : ℕ) (n : Fin k → ℕ) where
  slots : Fin p → ℕ
  balanced : ∀ u v, slots u ≤ slots v + 1
  wire : (Σ w, Fin (slots w)) ≃ (Σ j, Fin (n j))

variable {n : Fin k → ℕ}

def Layout.shard (L : Layout p n) (x : Payload n) (w : Fin p) : Bits :=
  List.ofFn fun i => let a := L.wire ⟨w, i⟩; x a.1 a.2

/-- Altering payload positions outside a worker's assigned slots does not change its initial
word: agreement at every position wired to that worker suffices. -/
theorem Layout.shard_congr (L : Layout p n) (x y : Payload n) (w : Fin p)
    (agree : ∀ i, let a := L.wire ⟨w, i⟩; x a.1 a.2 = y a.1 a.2) :
    L.shard x w = L.shard y w := congrArg List.ofFn (funext agree)

theorem Layout.total (L : Layout p n) (x : Payload n) :
    (∑ w, (L.shard x w).length) = inputBits x.words := by
  simpa [shard, Payload.words, inputBits, Fintype.card_sigma] using Fintype.card_congr L.wire

/-- Every positive worker count and every public vector of relation lengths admits a balanced
wiring of its positions, even when there are fewer bits than workers. -/
theorem Layout.nonempty (p : ℕ+) (n : Fin k → ℕ) : Nonempty (Layout p n) := by
  classical
  let M := ∑ j, n j
  obtain ⟨t, _, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin p)))
    (n := M % p) (by simpa using (Nat.mod_lt M p.pos).le)
  let s (w : Fin p) := M / p + if w ∈ t then 1 else 0
  have hsum : (∑ w, s w) = M := by
    simp [s, Finset.sum_add_distrib, ht, Nat.div_add_mod]
  refine ⟨s, fun u v => ?_, Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using hsum)⟩
  dsimp [s]; split_ifs <;> omega

-- Invert the wiring only on complete shards; a missing bit has no default value.
def Layout.readBack (L : Layout p n) (s : Fin p → Bits) : Option (Database k) :=
  if h : ∀ u, (s u).length = L.slots u then some fun j => List.ofFn fun i : Fin (n j) =>
    let a := L.wire.symm ⟨j, i⟩
    (s a.1)[a.2.val]'(by rw [h]; exact a.2.isLt)
  else none

theorem Layout.readBack_shard (L : Layout p n) (x : Payload n) :
    L.readBack (L.shard x) = some x.words := by
  simp only [readBack, shard, List.length_ofFn, implies_true, ↓reduceDIte, List.getElem_ofFn,
    Fin.eta, Option.some.injEq]
  funext j; apply congrArg List.ofFn; funext i
  exact congrArg (fun a : Σ j, Fin (n j) => x a.1 a.2) (L.wire.apply_symm_apply ⟨j, i⟩)

inductive Convention where
  | distributed | separate

inductive Schedule (p : ℕ) (n : Fin k → ℕ) : Convention → Type where
  | distributed (layout : Layout p n) : Schedule p n .distributed
  | separate : Schedule p n .separate

variable {mode : Convention}

def Schedule.place (s : Schedule p n mode) (x : Payload n) : Start p k := match s with
  | .distributed L => .distributed (L.shard x)
  | .separate => .separate x.words

-- Mail is indexed by its sender, not an anonymous bag. Empty is the unique zero-bit word.
structure Inbox (p k : ℕ) where
  worker : Fin p → Bits
  source : Fin k → Bits

structure View (p k : ℕ) where
  initial : Bits
  history : List (Inbox p k)

/-- Starting with the local input, apply a local state transition to each private inbox in
chronological order (the stored history has newest inbox first). -/
def View.replay {σ : Type*} (init : Bits → σ) (step : σ → Inbox p k → σ) (v : View p k) : σ :=
  v.history.foldr (fun m s => step s m) (init v.initial)

theorem View.replay_cons {σ : Type*} (init : Bits → σ) (step : σ → Inbox p k → σ)
    (v : View p k) (m : Inbox p k) :
    View.replay init step {v with history := m :: v.history} = step (v.replay init step) m := rfl

/-- A protocol fixes three local functions: worker-to-worker send, relation-server-to-worker
send, and worker report. All see the same random seed. A worker sees only its own view; an
input server sees only its own encoded relation. Sender and destination indices are public. -/
structure Protocol (p k : ℕ) (Ω α : Type*) where
  send : Ω → Fin p → View p k → Fin p → Bits
  inject : Ω → Fin k → Bits → Fin p → Bits
  report : Ω → Fin p → View p k → Finset α

def Start.initial : Start p k → Fin p → View p k
  | .distributed s, w => ⟨s w, []⟩
  | .separate _, _ => ⟨[], []⟩

-- The initial barrier has index zero. The paper's history notation includes a diagonal slot;
-- local data already persist in the view and are not traffic "from all other workers".
def Protocol.mail (A : Protocol p k Ω α) (ω : Ω) (I : Start p k) (r : ℕ)
    (old : Fin p → View p k) (v : Fin p) : Inbox p k where
  worker u := if u = v then [] else A.send ω u (old u) v
  source j := match I, r with
    | .separate D, 0 => A.inject ω j (D j) v
    | _, _ => []

/-- The load of a barrier is the maximum over recipients of the sum of incoming worker
and input-server message lengths at that recipient. In particular, neither a sender's total
nor the largest single message measures this load. -/
def roundLoad (mail : Fin p → Inbox p k) : ℕ :=
  Finset.univ.sup fun v => (∑ u, ((mail v).worker u).length) + ∑ j, ((mail v).source j).length

theorem roundLoad_le_iff (mail : Fin p → Inbox p k) (L : ℕ) : roundLoad mail ≤ L ↔
    ∀ v, (∑ u, ((mail v).worker u).length) + (∑ j, ((mail v).source j).length) ≤ L := by
  simp [roundLoad, Finset.sup_le_iff]

/-- A barrier costs zero bits exactly when every worker and input-server channel to every
recipient carries the empty string. There is no separate zero-length control message. -/
theorem roundLoad_eq_zero_iff (mail : Fin p → Inbox p k) : roundLoad mail = 0 ↔
    ∀ v, (∀ u, (mail v).worker u = []) ∧ ∀ j, (mail v).source j = [] := by
  rw [← Nat.le_zero, roundLoad_le_iff]
  simp [Finset.sum_eq_zero_iff]

theorem Protocol.mail_self (A : Protocol p k Ω α) (ω : Ω) (I : Start p k) (r : ℕ)
    (old : Fin p → View p k) (v : Fin p) : (A.mail ω I r old v).worker v = [] := by simp [mail]

theorem Protocol.no_later_source (A : Protocol p k Ω α) (ω : Ω) (I : Start p k) (r : ℕ)
    (old : Fin p → View p k) (v : Fin p) (j : Fin k) :
    (A.mail ω I (r + 1) old v).source j = [] := by cases I <;> rfl

-- A natural-number cap makes the barrier executable. For the nonnegative real budget below,
-- passing its floor is exactly the test that the integral bit count fits in that budget.
def Protocol.run (A : Protocol p k Ω α) (ω : Ω) (I : Start p k) (L : ℕ) :
    ℕ → Option (Fin p → View p k)
  | 0 => some I.initial
  | r + 1 => do
    let old ← A.run ω I L r
    let mail := A.mail ω I r old
    if roundLoad mail ≤ L then
      return fun w => {old w with history := mail w :: (old w).history}
    else none

/-- A barrier completes exactly when the preceding run completed and the proposed mail fits
the cap. All recipients then retain their own local input and prepend precisely their own inbox. -/
theorem Protocol.run_succ_eq_some_iff (A : Protocol p k Ω α) (ω : Ω) (I : Start p k)
    (L r : ℕ) (next : Fin p → View p k) : A.run ω I L (r + 1) = some next ↔
    ∃ old, A.run ω I L r = some old ∧ roundLoad (A.mail ω I r old) ≤ L ∧
      (fun w => {old w with history := A.mail ω I r old w :: (old w).history}) = next := by
  cases h : A.run ω I L r with
  | none => simp [run, h]
  | some old => by_cases fit : roundLoad (A.mail ω I r old) ≤ L <;> simp [run, h, fit]

-- An abort is not a successful empty answer.
def Protocol.output [DecidableEq α] (A : Protocol p k Ω α) (ω : Ω) (I : Start p k)
    (L R : ℕ) : Option (Finset α) :=
  (A.run ω I L R).map fun views => Finset.univ.biUnion fun w => A.report ω w (views w)

/-- With $p>0$ workers and $M$ input bits the integer receive cap is the floor of
$CM/p^{1-\varepsilon}$. Flooring imposes no slack for empty inputs or sub-bit budgets. -/
noncomputable def receiveCap (C ε : ℝ) (M : ℕ) (p : ℕ+) : ℕ := ⌊C * M / (p : ℝ) ^ (1 - ε)⌋₊

theorem le_receiveCap_iff {C ε : ℝ} (hC : 0 ≤ C) (L M : ℕ) (p : ℕ+) :
    L ≤ receiveCap C ε M p ↔ (L : ℝ) ≤ C * M / (p : ℝ) ^ (1 - ε) := by
  apply Nat.le_floor_iff
  positivity

/-- At bit cap zero, any completed run in the separate-input convention has the same worker
views: empty initial inputs and one all-empty inbox per round. Aborting runs need not agree. -/
theorem Protocol.separate_zero_cap (A : Protocol p k Ω α) (D : Database k) (ω : Ω) (r : ℕ)
    {v : Fin p → View p k} (h : A.run ω (.separate D) 0 r = some v) :
    ∀ w, v w = ⟨[], List.replicate r ⟨fun _ => [], fun _ => []⟩⟩ := by
  induction r generalizing v with
  | zero => intro w; exact congrFun (Option.some.inj h).symm w
  | succ r ih =>
    obtain ⟨old, prev, fit, rfl⟩ := (run_succ_eq_some_iff ..).1 h
    have empty := (roundLoad_eq_zero_iff _).1 (Nat.eq_zero_of_le_zero fit)
    intro w
    have hm : A.mail ω (.separate D) r old w = ⟨fun _ => [], fun _ => []⟩ := by
      obtain ⟨a, b⟩ := empty w
      exact congrArg₂ Inbox.mk (funext a) (funext b)
    simp [hm, ih prev w, List.replicate_succ]

/-- Fix the admissible public worker counts and relation lengths, and a failure tolerance for
these pairs, before choosing a protocol family. The space exponent lies in $[0,1]$. One positive
cap constant works throughout the specified domain. On each admissible pair the tolerance lies
in $[0,1)$; on every schedule and valid payload there, the measurable event of completion with
exactly the query answer as the union of reports has probability at least one minus that tolerance
under the common seed law. Constant tolerance is the special case of a constant function. -/
def Computes [DecidableEq α] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (mode : Convention) (admissible : ℕ+ → (Fin k → ℕ) → Prop) (η : ℕ+ → (Fin k → ℕ) → ℝ)
    (valid : Database k → Prop) (query : Database k → Finset α)
    (A : (p : ℕ+) → (n : Fin k → ℕ) → Schedule p n mode → Protocol p k Ω α)
    (R : ℕ) (ε : ℝ) : Prop :=
  ε ∈ Set.Icc 0 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ+) (n : Fin k → ℕ), admissible p n →
    η p n ∈ Set.Ico 0 1 ∧ ∀ (s : Schedule p n mode) (x : Payload n), valid x.words →
      let ok := {ω | (A p n s).output ω (s.place x) (receiveCap C ε (inputBits x.words) p) R =
        some (query x.words)}
      MeasurableSet ok ∧ ENNReal.ofReal (1 - η p n) ≤ μ ok

section Gather

variable [DecidableEq α]

private def gather (q : Database k → Finset α) (p : ℕ+) (n : Fin k → ℕ)
    (s : Schedule p n mode) : Protocol p k Ω α where
  send _ _ v dst := if dst = 0 then v.initial else []
  inject _ _ data dst := if dst = 0 then data else []
  report _ w v := if w = 0 then match v.history with
    | [] => ∅
    | m :: _ => match s with
      | .separate => q m.source
      | .distributed L =>
        ((L.readBack (fun u => if u = w then v.initial else m.worker u)).map q).getD ∅
    else ∅

private theorem gather_ok (q : Database k → Finset α) (p : ℕ+)
    (s : Schedule p n mode) (x : Payload n) (ω : Ω) :
    (gather q p n s).output ω (s.place x) (inputBits x.words) 1 = some (q x.words) := by
  let I := s.place x
  let m := (gather q p n s).mail ω I 0 I.initial
  have fit : roundLoad m ≤ inputBits x.words := by
    rw [roundLoad_le_iff]; intro v
    cases s with
    | distributed L =>
      simp only [m, I, Schedule.place, Protocol.mail, List.length_nil, Finset.sum_const_zero,
        add_zero, gather, Start.initial]
      rw [← L.total x]
      exact Finset.sum_le_sum fun u _ => by split_ifs <;> simp
    | separate =>
      by_cases hv : v = 0 <;> simp [m, I, Schedule.place, Protocol.mail, gather, Start.initial,
        inputBits, hv]
  have ran : (gather q p n s).run ω I (inputBits x.words) 1 =
      some (fun w => {(I.initial w) with history := m w :: (I.initial w).history}) :=
    (Protocol.run_succ_eq_some_iff _ _ _ _ 0 _).2 ⟨_, rfl, fit, rfl⟩
  rw [Protocol.output, ran]; apply congrArg some; ext a
  have one_report (S : Finset α) : (∃ w : Fin p, a ∈ if w = 0 then S else ∅) ↔ a ∈ S := by
    constructor
    · rintro ⟨w, hw⟩; split at hw <;> simp_all
    · intro ha; exact ⟨0, by simpa using ha⟩
  cases s with
  | separate =>
    simpa +contextual [m, I, Schedule.place, Protocol.mail, gather, Start.initial] using
      one_report (q x.words)
  | distributed L =>
    have self : (fun u : Fin p => if u = 0 then L.shard x 0 else L.shard x u) = L.shard x := by
      funext u; split <;> simp_all
    simpa +contextual [m, I, Schedule.place, Protocol.mail, gather, Start.initial, self,
      L.readBack_shard] using one_report (q x.words)

/-- For every reporting query, in either raw-position input convention and under any common
seed law, one round at space exponent one suffices with zero failure. A designated worker
gathers the shards and inverts the public wiring, or receives complete relation words, then
reports the answer. Its receive cap is the input bit length. -/
theorem computes_one_round_full_load [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (mode : Convention) (admissible : ℕ+ → (Fin k → ℕ) → Prop)
    (valid : Database k → Prop) (q : Database k → Finset α) :
    ∃ A, Computes μ mode admissible (fun _ _ => 0) valid q A 1 1 := by
  refine ⟨gather q, by constructor <;> norm_num, 1, zero_lt_one, ?_⟩
  intro p n _; refine ⟨by constructor <;> norm_num, ?_⟩; intro s x _
  simp [receiveCap, gather_ok q p s x]

end Gather

end Cslib.Databases.QueryMPC
