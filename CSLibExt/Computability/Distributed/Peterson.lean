/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Function.Basic

/-!
# Peterson's mutual-exclusion algorithm

Peterson's algorithm for two processes, as a state machine. Each process has an entry protocol
of two assignments (raise its own flag, then assign `turn`) followed by a busy-waiting loop, and
an exit protocol that lowers its flag. Every assignment and every evaluation of the loop condition
is one atomic step here; for process `i`:

* `flag i := true` (stage `idle` to `turnSet`);
* `turn := other i` (`turnSet` to `waiting`);
* wait while `flag (other i) ∧ turn = other i`: a step in stage `waiting` evaluates the
  condition, stays put while it holds, and enters `critical` once it fails;
* leave the critical section (`critical` to `exiting`);
* `flag i := false` (`exiting` to `idle`).

Here `turn` holds the favoured process: by assigning `turn := other i`, process `i` defers to
the other process. Recording instead the last process to assign `turn` gives the same algorithm
with `turn` replaced by `other turn`.

Initially both processes are idle and both flags are down; the initial `turn` is arbitrary
(`init t` for either `t`). A state is reachable if some sequence of steps of either process
leads to it from an initial state.

## Main results

* `mutual_exclusion`: no reachable state has both processes in their critical sections.

Starvation freedom is not proved here.

## References

* G. L. Peterson, *Myths about the mutual exclusion problem*, Information Processing Letters 12
  (1981), no. 3, 115-116.
-/

@[expose] public section

namespace Cslib.Distributed.Peterson

/-- Stages of one process in Peterson's algorithm. -/
inductive Stage : Type
  /-- Outside the protocol, with the flag down. -/
  | idle
  /-- The flag is up; `turn` is assigned next. -/
  | turnSet
  /-- Waiting until the other flag is down or `turn` favours this process. -/
  | waiting
  /-- In the critical section. -/
  | critical
  /-- Out of the critical section; the flag is lowered next. -/
  | exiting
deriving DecidableEq, Repr

/-- Global state: the stage of each process, the two flags, and the shared `turn`. -/
structure State where
  /-- The stage of each process. -/
  pc : Fin 2 → Stage
  /-- The flag of each process. -/
  flag : Fin 2 → Bool
  /-- The process favoured when both processes are waiting. -/
  turn : Fin 2

/-- The other process. -/
def other (i : Fin 2) : Fin 2 := ⟨1 - i.val, by
  have := i.isLt
  omega⟩

/-- One atomic step of process `i`. -/
def step (i : Fin 2) (s : State) : State :=
  match s.pc i with
  | .idle => { s with pc := Function.update s.pc i .turnSet,
                      flag := Function.update s.flag i true }
  | .turnSet => { s with pc := Function.update s.pc i .waiting,
                         turn := other i }
  | .waiting =>
      if s.flag (other i) && s.turn = other i then s
      else { s with pc := Function.update s.pc i .critical }
  | .critical => { s with pc := Function.update s.pc i .exiting }
  | .exiting => { s with pc := Function.update s.pc i .idle,
                          flag := Function.update s.flag i false }

/-- The initial state with turn `t`: both processes idle, both flags down. -/
def init (t : Fin 2) : State := ⟨fun _ => .idle, fun _ => false, t⟩

/-- A state is reachable if steps of the two processes lead to it from an initial state, whose
`turn` is arbitrary. -/
def Reachable (s : State) : Prop :=
  ∃ t, Relation.ReflTransGen (fun a b => ∃ i, step i a = b) (init t) s

/-- Every initial state is reachable. -/
theorem reachable_init (t : Fin 2) : Reachable (init t) := ⟨t, .refl⟩

/-- A step of either process from a reachable state leads to a reachable state. -/
theorem Reachable.step {s : State} (hs : Reachable s) (i : Fin 2) :
    Reachable (Peterson.step i s) := by
  obtain ⟨t, h⟩ := hs
  exact ⟨t, .tail h ⟨i, rfl⟩⟩

private theorem other_zero : other 0 = 1 := rfl

private theorem other_one : other 1 = 0 := rfl

private theorem other_other (i : Fin 2) : other (other i) = i := by
  apply Fin.ext
  have h := i.isLt
  change 1 - (1 - i.val) = i.val
  omega

private theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by simp

private theorem fin2_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  have h := Fin.forall_fin_two (p := fun i : Fin 2 => i = 0 ∨ i = 1)
  exact h.mpr ⟨Or.inl rfl, Or.inr rfl⟩

private theorem other_ne_self (i : Fin 2) : other i ≠ i := by
  rcases fin2_cases i with rfl | rfl
  · rw [other_zero]
    exact Ne.symm fin2_zero_ne_one
  · rw [other_one]
    exact fin2_zero_ne_one

private theorem eq_of_ne_other (t i : Fin 2) (h : t ≠ other i) : t = i := by
  rcases fin2_cases t with rfl | rfl <;> rcases fin2_cases i with rfl | rfl
  · rfl
  · rw [other_one] at h
    exact absurd rfl h
  · rw [other_zero] at h
    exact absurd rfl h
  · rfl

private theorem guard_false_cases (b : State) (k : Fin 2)
    (hg : ¬ (b.flag (other k) && (b.turn = other k : Prop)) = true) :
    b.flag (other k) = false ∨ b.turn ≠ other k := by
  cases hf : b.flag (other k)
  · exact Or.inl rfl
  · right
    intro ht
    apply hg
    rw [hf, ht, Bool.true_and]
    exact decide_eq_true rfl

private theorem step_idle_pc (k : Fin 2) (b : State) (h : b.pc k = .idle)
    (j : Fin 2) :
    (step k b).pc j = Function.update b.pc k .turnSet j := by
  simp only [step, h]

private theorem step_idle_flag (k : Fin 2) (b : State) (h : b.pc k = .idle)
    (j : Fin 2) :
    (step k b).flag j = Function.update b.flag k true j := by
  simp only [step, h]

private theorem step_idle_turn (k : Fin 2) (b : State) (h : b.pc k = .idle) :
    (step k b).turn = b.turn := by
  simp only [step, h]

private theorem step_turnSet_pc (k : Fin 2) (b : State) (h : b.pc k = .turnSet)
    (j : Fin 2) :
    (step k b).pc j = Function.update b.pc k .waiting j := by
  simp only [step, h]

private theorem step_turnSet_flag (k : Fin 2) (b : State) (h : b.pc k = .turnSet)
    (j : Fin 2) :
    (step k b).flag j = b.flag j := by
  simp only [step, h]

private theorem step_turnSet_turn (k : Fin 2) (b : State)
    (h : b.pc k = .turnSet) :
    (step k b).turn = other k := by
  simp only [step, h]

private theorem step_waiting_stay (k : Fin 2) (b : State) (h : b.pc k = .waiting)
    (hg : (b.flag (other k) && b.turn = other k) = true) :
    step k b = b := by
  simp only [step, h, ite_eq_left hg]

private theorem step_waiting_go_pc (k : Fin 2) (b : State)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (other k) && b.turn = other k) = true) (j : Fin 2) :
    (step k b).pc j = Function.update b.pc k .critical j := by
  simp only [step, h, ite_eq_right hg]

private theorem step_waiting_go_flag (k : Fin 2) (b : State)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (other k) && b.turn = other k) = true) (j : Fin 2) :
    (step k b).flag j = b.flag j := by
  simp only [step, h, ite_eq_right hg]

private theorem step_waiting_go_turn (k : Fin 2) (b : State)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (other k) && b.turn = other k) = true) :
    (step k b).turn = b.turn := by
  simp only [step, h, ite_eq_right hg]

private theorem step_critical_pc (k : Fin 2) (b : State)
    (h : b.pc k = .critical) (j : Fin 2) :
    (step k b).pc j = Function.update b.pc k .exiting j := by
  simp only [step, h]

private theorem step_critical_flag (k : Fin 2) (b : State)
    (h : b.pc k = .critical) (j : Fin 2) :
    (step k b).flag j = b.flag j := by
  simp only [step, h]

private theorem step_critical_turn (k : Fin 2) (b : State)
    (h : b.pc k = .critical) :
    (step k b).turn = b.turn := by
  simp only [step, h]

private theorem step_exiting_pc (k : Fin 2) (b : State)
    (h : b.pc k = .exiting) (j : Fin 2) :
    (step k b).pc j = Function.update b.pc k .idle j := by
  simp only [step, h]

private theorem step_exiting_flag (k : Fin 2) (b : State)
    (h : b.pc k = .exiting) (j : Fin 2) :
    (step k b).flag j = Function.update b.flag k false j := by
  simp only [step, h]

private theorem step_exiting_turn (k : Fin 2) (b : State)
    (h : b.pc k = .exiting) :
    (step k b).turn = b.turn := by
  simp only [step, h]

/-- In a reachable state, a process in stage `turnSet`, `waiting` or `critical` has its flag up. -/
private theorem flag_of_reachable (s : State) (hs : Reachable s) (i : Fin 2)
    (h : s.pc i = .turnSet ∨ s.pc i = .waiting ∨ s.pc i = .critical) :
    s.flag i = true := by
  obtain ⟨t, hs⟩ := hs
  revert i h
  induction hs with
  | refl =>
      intro i h
      simp [init] at h
  | tail hb hstep ih =>
      rename_i b c
      intro i h
      obtain ⟨k, rfl⟩ := hstep
      cases hstage : b.pc k
      · rw [step_idle_pc k b hstage i] at h
        rw [step_idle_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self]
        · rw [Function.update_of_ne hik] at h ⊢
          exact ih i h
      · rw [step_turnSet_pc k b hstage i] at h
        rw [step_turnSet_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik] at h ⊢
          rw [Function.update_self] at h
          exact ih k (Or.inl hstage)
        · rw [Function.update_of_ne hik] at h
          exact ih i h
      · by_cases hg : (b.flag (other k) && b.turn = other k) = true
        · rw [step_waiting_stay k b hstage hg] at h ⊢
          exact ih i h
        · rw [step_waiting_go_pc k b hstage hg i] at h
          rw [step_waiting_go_flag k b hstage hg i]
          by_cases hik : i = k
          · rw [hik] at h ⊢
            rw [Function.update_self] at h
            exact ih k (Or.inr (Or.inl hstage))
          · rw [Function.update_of_ne hik] at h
            exact ih i h
      · rw [step_critical_pc k b hstage i] at h
        rw [step_critical_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at h
          rcases h with h | h | h <;> exact Stage.noConfusion h
        · rw [Function.update_of_ne hik] at h
          exact ih i h
      · rw [step_exiting_pc k b hstage i] at h
        rw [step_exiting_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at h
          rcases h with h | h | h <;> exact Stage.noConfusion h
        · rw [Function.update_of_ne hik] at h ⊢
          exact ih i h

/-- In a reachable state, if process `i` is critical while the other process is waiting or
critical, then `turn = i`. -/
private theorem turn_of_reachable (s : State) (hs : Reachable s) (i : Fin 2)
    (hi : s.pc i = .critical)
    (hj : s.pc (other i) = .waiting ∨ s.pc (other i) = .critical) :
    s.turn = i := by
  obtain ⟨t, hs⟩ := hs
  revert i hi hj
  induction hs with
  | refl =>
      intro i hi hj
      simp [init] at hi
  | tail hb hstep ih =>
      rename_i b c
      intro i hi hj
      obtain ⟨k, rfl⟩ := hstep
      have ihA : ∀ (j : Fin 2),
          b.pc j = .turnSet ∨ b.pc j = .waiting ∨ b.pc j = .critical →
          b.flag j = true :=
        fun j h => flag_of_reachable b ⟨t, hb⟩ j h
      cases hstage : b.pc k
      · rw [step_idle_pc k b hstage i] at hi
        rw [step_idle_pc k b hstage (other i)] at hj
        rw [step_idle_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact Stage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : other i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact Stage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj
      · rw [step_turnSet_pc k b hstage i] at hi
        rw [step_turnSet_pc k b hstage (other i)] at hj
        rw [step_turnSet_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact Stage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : other i = k
          · rw [← hjk]
            exact other_other i
          · rw [Function.update_of_ne hjk] at hj
            have hne : k ≠ other (other i) := by
              rw [other_other i]
              exact Ne.symm hik
            have hkj : k = other i := eq_of_ne_other k (other i) hne
            exact absurd hkj.symm hjk
      · by_cases hg : (b.flag (other k) && b.turn = other k) = true
        · rw [step_waiting_stay k b hstage hg] at hi hj ⊢
          exact ih i hi hj
        · rw [step_waiting_go_pc k b hstage hg i] at hi
          rw [step_waiting_go_pc k b hstage hg (other i)] at hj
          rw [step_waiting_go_turn k b hstage hg]
          by_cases hik : i = k
          · rw [hik] at hi hj ⊢
            rw [Function.update_self] at hi
            have hjk : other k ≠ k := other_ne_self k
            rw [Function.update_of_ne hjk] at hj
            have hdisj := guard_false_cases b k hg
            rcases hdisj with hfalse | hturn
            · have hflag := ihA (other k) (Or.inr hj)
              rw [hfalse] at hflag
              exact Bool.noConfusion hflag
            · exact eq_of_ne_other _ _ hturn
          · rw [Function.update_of_ne hik] at hi
            by_cases hjk : other i = k
            · rw [hjk, Function.update_self] at hj
              have hpcj : b.pc (other i) = .waiting := by
                rw [hjk]
                exact hstage
              have hturn := ih i hi (Or.inl hpcj)
              have hok : other k = i := by
                rw [← hjk]
                exact other_other i
              have hdisj := guard_false_cases b k hg
              rw [hok] at hdisj
              rcases hdisj with hfalse | hturn_ne
              · have hflag := ihA i (Or.inr (Or.inr hi))
                rw [hfalse] at hflag
                exact Bool.noConfusion hflag
              · exact absurd hturn hturn_ne
            · rw [Function.update_of_ne hjk] at hj
              exact ih i hi hj
      · rw [step_critical_pc k b hstage i] at hi
        rw [step_critical_pc k b hstage (other i)] at hj
        rw [step_critical_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact Stage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : other i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact Stage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj
      · rw [step_exiting_pc k b hstage i] at hi
        rw [step_exiting_pc k b hstage (other i)] at hj
        rw [step_exiting_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact Stage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : other i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact Stage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj

/-- **Mutual exclusion**: in no reachable state are both processes in their critical
sections. -/
theorem mutual_exclusion (s : State) (hs : Reachable s) :
    ¬ (s.pc 0 = .critical ∧ s.pc 1 = .critical) := by
  intro hboth
  obtain ⟨h0, h1⟩ := hboth
  have hj0 : s.pc (other 0) = .waiting ∨ s.pc (other 0) = .critical :=
    Or.inr (by rw [other_zero]; exact h1)
  have ht0 : s.turn = 0 := turn_of_reachable s hs 0 h0 hj0
  have hj1 : s.pc (other 1) = .waiting ∨ s.pc (other 1) = .critical :=
    Or.inr (by rw [other_one]; exact h0)
  have ht1 : s.turn = 1 := turn_of_reachable s hs 1 h1 hj1
  have h01 : (0 : Fin 2) = 1 := ht0.symm.trans ht1
  exact fin2_zero_ne_one h01

end Cslib.Distributed.Peterson

end
