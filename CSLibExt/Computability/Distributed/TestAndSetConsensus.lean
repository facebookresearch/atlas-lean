/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Two-process consensus from test-and-set

The protocol by which a test-and-set bit and two single-writer registers solve wait-free
consensus for two processes (Herlihy 1991), as a state machine. Process `i`, with input `inp i`:

* writes `inp i` to its register `reg i` (stage `write` to `testAndSet`);
* applies test-and-set to the shared bit `tas`, which sets the bit and returns its old value in
  one atomic step: the process wins if the old value was `false` (stage `decideOwn`) and loses
  otherwise (stage `readOther`);
* the winner decides its own input, and the loser reads the register of the other process and
  decides the value it finds (stage `done`).

A test-and-set step reveals only the old bit, not which process set it. Each write, test-and-set,
and read-and-decide is one atomic step, a transition of the labelled transition system `lts`
labelled by the process that takes it. Initially no register is written, the bit is `false`, and
no process has decided; a state is reachable if the initial state can reach it in `lts`
(`LTS.CanReach`). The field `winner` is ghost state: `step` records the winner there but never
reads it, and it only serves to state the invariant.

## Main results

* `safety`: in every reachable state, any two decisions agree (agreement) and every decision is
  one of the inputs (validity).
* `decision_isSome_of_three_le_count`: wait-free termination. In every execution `LTS.MTr` from
  the initial state, a process that has taken three steps has decided, whatever the other
  process does.
* `mTr_iff_eq_run`: since steps are deterministic, the execution along a schedule ends in
  `run inp σ`.

Impossibility results are not proved here, such as that test-and-set cannot solve consensus for
three processes (so that its consensus number is exactly two) or that read/write registers alone
cannot solve it for two.

## References

* M. Herlihy, *Wait-free synchronization*, ACM Transactions on Programming Languages and
  Systems 13 (1991), no. 1, 124-149.
* M. Herlihy and N. Shavit, *The Art of Multiprocessor Programming*, Morgan Kaufmann (2008),
  Chapter 5.
-/

@[expose] public section

namespace Cslib.Distributed.TestAndSetConsensus

/-- Stages of one process. -/
inductive Stage : Type
  /-- About to write its input to its register. -/
  | write
  /-- About to apply test-and-set to the shared bit. -/
  | testAndSet
  /-- Won the test-and-set; about to decide its own input. -/
  | decideOwn
  /-- Lost the test-and-set; about to read the other register and decide its value. -/
  | readOther
  /-- Decided. -/
  | done
deriving DecidableEq, Repr

/-- Global state of the protocol, with decision values in `V`. -/
structure State (V : Type*) where
  /-- The stage of each process. -/
  pc : Fin 2 → Stage
  /-- The single-writer register of each process, `none` until written. -/
  reg : Fin 2 → Option V
  /-- The shared test-and-set bit. -/
  tas : Bool
  /-- Ghost state: the process whose test-and-set returned `false`. `step` writes this field
  but never reads it. -/
  winner : Option (Fin 2)
  /-- The decision of each process, `none` until it decides. -/
  decision : Fin 2 → Option V

variable {V : Type*}

/-- The other process. -/
def other (i : Fin 2) : Fin 2 := ⟨1 - i.val, by
  have := i.isLt
  omega⟩

/-- One atomic step of process `i`, whose input is `inp i`. -/
def step (inp : Fin 2 → V) (i : Fin 2) (s : State V) : State V :=
  match s.pc i with
  | .write => { s with pc := Function.update s.pc i .testAndSet,
                       reg := Function.update s.reg i (some (inp i)) }
  | .testAndSet =>
      if s.tas then { s with pc := Function.update s.pc i .readOther }
      else { s with pc := Function.update s.pc i .decideOwn, tas := true, winner := some i }
  | .decideOwn => { s with pc := Function.update s.pc i .done,
                           decision := Function.update s.decision i (some (inp i)) }
  | .readOther => { s with pc := Function.update s.pc i .done,
                           decision := Function.update s.decision i (s.reg (other i)) }
  | .done => s

/-- The initial state: no register is written, the bit is `false`, and no process has
decided. -/
def init : State V := ⟨fun _ => .write, fun _ => none, false, none, fun _ => none⟩

/-- The protocol as a labelled transition system; the label is the process that steps. -/
def lts (inp : Fin 2 → V) : LTS (State V) (Fin 2) where
  Tr s i t := step inp i s = t

/-- The states reachable from `init`, by upstream `LTS.CanReach` (a multistep transition
`LTS.MTr` along some schedule). -/
def Reachable (inp : Fin 2 → V) (s : State V) : Prop := (lts inp).CanReach init s

/-- The state reached from `init` when the processes step in the order listed by the
schedule `σ`. -/
def run (inp : Fin 2 → V) (σ : List (Fin 2)) : State V :=
  σ.foldl (fun s i => step inp i s) init

/-- The initial state is reachable. -/
theorem reachable_init (inp : Fin 2 → V) : Reachable inp init := ⟨[], .refl⟩

/-- A step of either process from a reachable state leads to a reachable state. -/
theorem Reachable.step {inp : Fin 2 → V} {s : State V} (hs : Reachable inp s) (i : Fin 2) :
    Reachable inp (TestAndSetConsensus.step inp i s) :=
  let ⟨σ, hm⟩ := hs
  ⟨σ ++ [i], LTS.MTr.stepR _ hm rfl⟩

private theorem mTr_iff_eq_foldl {inp : Fin 2 → V} {t s : State V} {σ : List (Fin 2)} :
    (lts inp).MTr t σ s ↔ s = σ.foldl (fun s i => TestAndSetConsensus.step inp i s) t := by
  induction σ generalizing t with
  | nil => simp [eq_comm]
  | cons j σ ih =>
    rw [LTS.MTr.cons_iff, List.foldl_cons]
    constructor
    · rintro ⟨u, hu, hm⟩
      have hu' : TestAndSetConsensus.step inp j t = u := hu
      subst hu'
      exact ih.mp hm
    · exact fun h => ⟨_, rfl, ih.mpr h⟩

/-- Steps are deterministic: the execution from `init` along a schedule `σ` ends exactly in
`run inp σ`. -/
theorem mTr_iff_eq_run {inp : Fin 2 → V} {σ : List (Fin 2)} {s : State V} :
    (lts inp).MTr init σ s ↔ s = run inp σ :=
  mTr_iff_eq_foldl

/-- The state reached by any schedule is reachable. -/
theorem reachable_run (inp : Fin 2 → V) (σ : List (Fin 2)) : Reachable inp (run inp σ) :=
  ⟨σ, mTr_iff_eq_run.mpr rfl⟩

private theorem eq_other_of_ne {w i : Fin 2} (h : w ≠ i) : w = other i := by
  have hw := w.isLt
  have hi := i.isLt
  have hne : w.val ≠ i.val := fun e => h (Fin.ext e)
  apply Fin.ext
  change w.val = 1 - i.val
  omega

/-- The invariant behind `safety` and `decision_isSome_of_three_le_count`. -/
private def Inv (inp : Fin 2 → V) (s : State V) : Prop :=
  (∀ i, s.pc i ≠ .write → s.reg i = some (inp i)) ∧
  (s.tas = true → ∃ w, s.winner = some w) ∧
  (∀ w, s.winner = some w → s.tas = true ∧ s.pc w ≠ .write ∧ s.pc w ≠ .testAndSet) ∧
  (∀ i, s.pc i = .decideOwn → s.winner = some i) ∧
  (∀ i, s.pc i = .readOther → s.winner = some (other i)) ∧
  (∀ i, s.pc i = .done → ∃ w, s.winner = some w ∧ s.decision i = some (inp w)) ∧
  (∀ i, s.pc i ≠ .done → s.decision i = none)

private theorem inv_init (inp : Fin 2 → V) : Inv inp (init : State V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init]

private theorem inv_step (inp : Fin 2 → V) (i : Fin 2) {s : State V} (hs : Inv inp s) :
    Inv inp (step inp i s) := by
  obtain ⟨hR, hT, hW, hD, hO, hDone, hNone⟩ := hs
  cases hpc : s.pc i with
  | write =>
    simp only [step, hpc]
    refine ⟨?_, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp
      · simp only [Function.update_of_ne hki] at hk ⊢
        exact hR k hk
    · intro w hw
      have hwi : w ≠ i := fun h => (hW w hw).2.1 (h ▸ hpc)
      simpa [Function.update_of_ne hwi] using hW w hw
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hD k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hO k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hDone k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        exact hNone k (by simp [hpc])
      · simp only [Function.update_of_ne hki] at hk
        exact hNone k hk
  | testAndSet =>
    cases htas : s.tas with
    | true =>
      simp only [step, hpc, htas, ↓reduceIte]
      refine ⟨?_, fun _ => hT htas, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki
          exact hR k (by simp [hpc])
        · simp only [Function.update_of_ne hki] at hk
          exact hR k hk
      · intro w hw
        have hwi : w ≠ i := fun h => (hW w hw).2.2 (h ▸ hpc)
        simpa [Function.update_of_ne hwi, htas] using hW w hw
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp at hk
        · simp only [Function.update_of_ne hki] at hk
          exact hD k hk
      · intro k hk
        by_cases hki : k = i
        · subst hki
          obtain ⟨w, hw⟩ := hT htas
          have hwk : w ≠ k := fun h => (hW w hw).2.2 (h ▸ hpc)
          rw [hw, eq_other_of_ne hwk]
        · simp only [Function.update_of_ne hki] at hk
          exact hO k hk
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp at hk
        · simp only [Function.update_of_ne hki] at hk
          exact hDone k hk
      · intro k hk
        by_cases hki : k = i
        · subst hki
          exact hNone k (by simp [hpc])
        · simp only [Function.update_of_ne hki] at hk
          exact hNone k hk
    | false =>
      have hnw : ∀ w, s.winner ≠ some w := fun w hw => by simpa [htas] using (hW w hw).1
      simp only [step, hpc, htas, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun _ => ⟨i, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki
          exact hR k (by simp [hpc])
        · simp only [Function.update_of_ne hki] at hk
          exact hR k hk
      · intro w hw
        obtain rfl : i = w := Option.some_inj.mp hw
        simp
      · intro k hk
        by_cases hki : k = i
        · subst hki
          rfl
        · simp only [Function.update_of_ne hki] at hk
          exact absurd (hD k hk) (hnw k)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp at hk
        · simp only [Function.update_of_ne hki] at hk
          exact absurd (hO k hk) (hnw _)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simp at hk
        · simp only [Function.update_of_ne hki] at hk
          obtain ⟨w, hw, -⟩ := hDone k hk
          exact absurd hw (hnw w)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          exact hNone k (by simp [hpc])
        · simp only [Function.update_of_ne hki] at hk
          exact hNone k hk
  | decideOwn =>
    simp only [step, hpc]
    refine ⟨?_, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki
        exact hR k (by simp [hpc])
      · simp only [Function.update_of_ne hki] at hk
        exact hR k hk
    · intro w hw
      by_cases hwi : w = i
      · subst hwi
        simpa using (hW w hw).1
      · simpa [Function.update_of_ne hwi] using hW w hw
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hD k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hO k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        exact ⟨k, hD k hpc, by simp⟩
      · simp only [Function.update_of_ne hki] at hk ⊢
        exact hDone k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk ⊢
        exact hNone k hk
  | readOther =>
    simp only [step, hpc]
    refine ⟨?_, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki
        exact hR k (by simp [hpc])
      · simp only [Function.update_of_ne hki] at hk
        exact hR k hk
    · intro w hw
      by_cases hwi : w = i
      · subst hwi
        simpa using (hW w hw).1
      · simpa [Function.update_of_ne hwi] using hW w hw
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hD k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk
        exact hO k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        have hw := hO k hpc
        refine ⟨other k, hw, ?_⟩
        simpa using hR (other k) (hW (other k) hw).2.1
      · simp only [Function.update_of_ne hki] at hk ⊢
        exact hDone k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki
        simp at hk
      · simp only [Function.update_of_ne hki] at hk ⊢
        exact hNone k hk
  | done =>
    simp only [step, hpc]
    exact ⟨hR, hT, hW, hD, hO, hDone, hNone⟩

private theorem inv_trInv (inp : Fin 2 → V) : (lts inp).TrInv (Inv inp) := by
  intro s i t htr hs
  have htr' : step inp i s = t := htr
  subst htr'
  exact inv_step inp i hs

private theorem inv_of_reachable {inp : Fin 2 → V} {s : State V} (hs : Reachable inp s) :
    Inv inp s :=
  let ⟨_, hm⟩ := hs
  LTS.mtrInv_of_trInv (inv_trInv inp) _ _ _ hm (inv_init inp)

/-- **Safety of test-and-set consensus.** In every reachable state, any two recorded decisions
agree, and every recorded decision is one of the two inputs. Termination is
`decision_isSome_of_three_le_count`. -/
theorem safety (inp : Fin 2 → V) (s : State V) (hs : Reachable inp s) :
    (∀ i j x y, s.decision i = some x → s.decision j = some y → x = y)
    ∧ (∀ i x, s.decision i = some x → ∃ w, x = inp w) := by
  obtain ⟨-, -, -, -, -, hDone, hNone⟩ := inv_of_reachable hs
  have hdec : ∀ i x, s.decision i = some x → ∃ w, s.winner = some w ∧ x = inp w := by
    intro i x hx
    by_cases hpc : s.pc i = .done
    · obtain ⟨w, hw, hd⟩ := hDone i hpc
      exact ⟨w, hw, Option.some_inj.mp (hx.symm.trans hd)⟩
    · simp [hNone i hpc] at hx
  refine ⟨fun i j x y hi hj => ?_, fun i x hi => ?_⟩
  · obtain ⟨w₁, hw₁, rfl⟩ := hdec i x hi
    obtain ⟨w₂, hw₂, rfl⟩ := hdec j y hj
    obtain rfl : w₁ = w₂ := Option.some_inj.mp (hw₁.symm.trans hw₂)
    rfl
  · obtain ⟨w, -, hx⟩ := hdec i x hi
    exact ⟨w, hx⟩

/-- Steps a process in a given stage takes before it decides. -/
private def stepsLeft : Stage → ℕ
  | .write => 3
  | .testAndSet => 2
  | .decideOwn => 1
  | .readOther => 1
  | .done => 0

/-- A step of process `j` lowers the steps left of process `i` by one if `j = i`, unless `i` has
already decided, and leaves them unchanged otherwise. -/
private theorem stepsLeft_step (inp : Fin 2 → V) (j i : Fin 2) (s : State V) :
    stepsLeft ((step inp j s).pc i) = stepsLeft (s.pc i) - if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst hji
    cases hpc : s.pc j with
    | testAndSet => cases htas : s.tas <;> simp [step, hpc, htas, stepsLeft]
    | _ => simp [step, hpc, stepsLeft]
  · have hij : i ≠ j := Ne.symm hji
    cases hpc : s.pc j with
    | testAndSet => cases htas : s.tas <;> simp [step, hpc, htas, Function.update_of_ne hij, hji]
    | _ => simp [step, hpc, Function.update_of_ne hij, hji]

private theorem stepsLeft_foldl (inp : Fin 2 → V) (i : Fin 2) (σ : List (Fin 2))
    (s : State V) :
    stepsLeft ((σ.foldl (fun s j => step inp j s) s).pc i) = stepsLeft (s.pc i) - σ.count i := by
  induction σ generalizing s with
  | nil => simp
  | cons j σ ih =>
    rw [List.foldl_cons, ih, stepsLeft_step, List.count_cons]
    by_cases hji : j = i <;> simp [hji, Nat.sub_sub, Nat.add_comm]

/-- **Wait-free termination.** In every execution from `init`, a process that has taken at least
three steps has decided, whatever the other process does. -/
theorem decision_isSome_of_three_le_count {inp : Fin 2 → V} {σ : List (Fin 2)} {s : State V}
    (hσ : (lts inp).MTr init σ s) (i : Fin 2) (h : 3 ≤ σ.count i) : (s.decision i).isSome := by
  obtain rfl := mTr_iff_eq_run.mp hσ
  have h0 : stepsLeft ((run inp σ).pc i) = 0 := by
    rw [run, stepsLeft_foldl]
    simp only [init, stepsLeft]
    omega
  have hdone : (run inp σ).pc i = .done := by
    revert h0
    cases (run inp σ).pc i <;> simp [stepsLeft]
  obtain ⟨-, -, -, -, -, hDone, -⟩ := inv_of_reachable (reachable_run inp σ)
  obtain ⟨w, -, hw⟩ := hDone i hdone
  simp [hw]

end Cslib.Distributed.TestAndSetConsensus

end
