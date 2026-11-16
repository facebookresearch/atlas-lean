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
# Peterson's algorithm

The two-process Peterson mutual-exclusion algorithm as an
atomic-step state machine. Reachable states never have
both processes in their critical sections. Starvation
freedom is not included here.
-/

@[expose] public section

/-- Stages of one process in Peterson's algorithm
(DPA-13 core). -/
inductive PStage : Type
  | idle
  | turnSet
  | waiting
  | critical
  | exiting
deriving DecidableEq, Repr

/-- State: program counters, flags, and the turn variable,
all indexed by `Fin 2`. -/
structure PState where
  pc : Fin 2 → PStage
  flag : Fin 2 → Bool
  turn : Fin 2

/-- The other process. -/
def otherProc (i : Fin 2) : Fin 2 := ⟨1 - i.val, by
  have := i.isLt
  omega⟩

/-- One atomic step of process `i`. -/
def pstep (i : Fin 2) (s : PState) : PState :=
  match s.pc i with
  | .idle => { s with pc := Function.update s.pc i .turnSet,
                      flag := Function.update s.flag i true }
  | .turnSet => { s with pc := Function.update s.pc i .waiting,
                         turn := otherProc i }
  | .waiting =>
      if s.flag (otherProc i) && s.turn = otherProc i then s
      else { s with pc := Function.update s.pc i .critical }
  | .critical => { s with pc := Function.update s.pc i .exiting }
  | .exiting => { s with pc := Function.update s.pc i .idle,
                          flag := Function.update s.flag i false }

/-- Reachability from the initial state (both idle, flags
down; the initial turn is arbitrary). -/
def PReachable (s : PState) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ i, pstep i a = b)
    ⟨fun _ => .idle, fun _ => false, 0⟩ s

private theorem otherProc_zero : otherProc 0 = 1 := rfl

private theorem otherProc_one : otherProc 1 = 0 := rfl

private theorem otherProc_otherProc (i : Fin 2) : otherProc (otherProc i) = i := by
  apply Fin.ext
  have h := i.isLt
  show 1 - (1 - i.val) = i.val
  omega

private theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by simp

private theorem fin2_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  have h := Fin.forall_fin_two (p := fun i : Fin 2 => i = 0 ∨ i = 1)
  exact h.mpr ⟨Or.inl rfl, Or.inr rfl⟩

private theorem otherProc_ne_self (i : Fin 2) : otherProc i ≠ i := by
  rcases fin2_cases i with rfl | rfl
  · rw [otherProc_zero]
    exact Ne.symm fin2_zero_ne_one
  · rw [otherProc_one]
    exact fin2_zero_ne_one

private theorem eq_of_ne_otherProc (t i : Fin 2) (h : t ≠ otherProc i) : t = i := by
  rcases fin2_cases t with rfl | rfl <;> rcases fin2_cases i with rfl | rfl
  · rfl
  · rw [otherProc_one] at h
    exact absurd rfl h
  · rw [otherProc_zero] at h
    exact absurd rfl h
  · rfl

private theorem guard_false_cases (b : PState) (k : Fin 2)
    (hg : ¬ (b.flag (otherProc k) && (b.turn = otherProc k : Prop)) = true) :
    b.flag (otherProc k) = false ∨ b.turn ≠ otherProc k := by
  cases hf : b.flag (otherProc k)
  · exact Or.inl rfl
  · right
    intro ht
    apply hg
    rw [hf, ht, Bool.true_and]
    exact decide_eq_true rfl

private theorem pstep_idle_pc (k : Fin 2) (b : PState) (h : b.pc k = .idle)
    (j : Fin 2) :
    (pstep k b).pc j = Function.update b.pc k .turnSet j := by
  simp only [pstep, h]

private theorem pstep_idle_flag (k : Fin 2) (b : PState) (h : b.pc k = .idle)
    (j : Fin 2) :
    (pstep k b).flag j = Function.update b.flag k true j := by
  simp only [pstep, h]

private theorem pstep_idle_turn (k : Fin 2) (b : PState) (h : b.pc k = .idle) :
    (pstep k b).turn = b.turn := by
  simp only [pstep, h]

private theorem pstep_turnSet_pc (k : Fin 2) (b : PState) (h : b.pc k = .turnSet)
    (j : Fin 2) :
    (pstep k b).pc j = Function.update b.pc k .waiting j := by
  simp only [pstep, h]

private theorem pstep_turnSet_flag (k : Fin 2) (b : PState) (h : b.pc k = .turnSet)
    (j : Fin 2) :
    (pstep k b).flag j = b.flag j := by
  simp only [pstep, h]

private theorem pstep_turnSet_turn (k : Fin 2) (b : PState)
    (h : b.pc k = .turnSet) :
    (pstep k b).turn = otherProc k := by
  simp only [pstep, h]

private theorem pstep_waiting_stay (k : Fin 2) (b : PState) (h : b.pc k = .waiting)
    (hg : (b.flag (otherProc k) && b.turn = otherProc k) = true) :
    pstep k b = b := by
  simp only [pstep, h, ite_eq_left hg]

private theorem pstep_waiting_go_pc (k : Fin 2) (b : PState)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (otherProc k) && b.turn = otherProc k) = true) (j : Fin 2) :
    (pstep k b).pc j = Function.update b.pc k .critical j := by
  simp only [pstep, h, ite_eq_right hg]

private theorem pstep_waiting_go_flag (k : Fin 2) (b : PState)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (otherProc k) && b.turn = otherProc k) = true) (j : Fin 2) :
    (pstep k b).flag j = b.flag j := by
  simp only [pstep, h, ite_eq_right hg]

private theorem pstep_waiting_go_turn (k : Fin 2) (b : PState)
    (h : b.pc k = .waiting)
    (hg : ¬ (b.flag (otherProc k) && b.turn = otherProc k) = true) :
    (pstep k b).turn = b.turn := by
  simp only [pstep, h, ite_eq_right hg]

private theorem pstep_critical_pc (k : Fin 2) (b : PState)
    (h : b.pc k = .critical) (j : Fin 2) :
    (pstep k b).pc j = Function.update b.pc k .exiting j := by
  simp only [pstep, h]

private theorem pstep_critical_flag (k : Fin 2) (b : PState)
    (h : b.pc k = .critical) (j : Fin 2) :
    (pstep k b).flag j = b.flag j := by
  simp only [pstep, h]

private theorem pstep_critical_turn (k : Fin 2) (b : PState)
    (h : b.pc k = .critical) :
    (pstep k b).turn = b.turn := by
  simp only [pstep, h]

private theorem pstep_exiting_pc (k : Fin 2) (b : PState)
    (h : b.pc k = .exiting) (j : Fin 2) :
    (pstep k b).pc j = Function.update b.pc k .idle j := by
  simp only [pstep, h]

private theorem pstep_exiting_flag (k : Fin 2) (b : PState)
    (h : b.pc k = .exiting) (j : Fin 2) :
    (pstep k b).flag j = Function.update b.flag k false j := by
  simp only [pstep, h]

private theorem pstep_exiting_turn (k : Fin 2) (b : PState)
    (h : b.pc k = .exiting) :
    (pstep k b).turn = b.turn := by
  simp only [pstep, h]

private theorem reachable_invA (s : PState) (hs : PReachable s) (i : Fin 2)
    (h : s.pc i = .turnSet ∨ s.pc i = .waiting ∨ s.pc i = .critical) :
    s.flag i = true := by
  unfold PReachable at hs
  revert i h
  induction hs with
  | refl =>
      intro i h
      simp at h
  | tail hb hstep ih =>
      rename_i b c
      intro i h
      obtain ⟨k, rfl⟩ := hstep
      cases hstage : b.pc k
      · rw [pstep_idle_pc k b hstage i] at h
        rw [pstep_idle_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self]
        · rw [Function.update_of_ne hik] at h ⊢
          exact ih i h
      · rw [pstep_turnSet_pc k b hstage i] at h
        rw [pstep_turnSet_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik] at h ⊢
          rw [Function.update_self] at h
          exact ih k (Or.inl hstage)
        · rw [Function.update_of_ne hik] at h
          exact ih i h
      · by_cases hg : (b.flag (otherProc k) && b.turn = otherProc k) = true
        · rw [pstep_waiting_stay k b hstage hg] at h ⊢
          exact ih i h
        · rw [pstep_waiting_go_pc k b hstage hg i] at h
          rw [pstep_waiting_go_flag k b hstage hg i]
          by_cases hik : i = k
          · rw [hik] at h ⊢
            rw [Function.update_self] at h
            exact ih k (Or.inr (Or.inl hstage))
          · rw [Function.update_of_ne hik] at h
            exact ih i h
      · rw [pstep_critical_pc k b hstage i] at h
        rw [pstep_critical_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at h
          rcases h with h | h | h <;> exact PStage.noConfusion h
        · rw [Function.update_of_ne hik] at h
          exact ih i h
      · rw [pstep_exiting_pc k b hstage i] at h
        rw [pstep_exiting_flag k b hstage i]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at h
          rcases h with h | h | h <;> exact PStage.noConfusion h
        · rw [Function.update_of_ne hik] at h ⊢
          exact ih i h

private theorem reachable_invB (s : PState) (hs : PReachable s) (i : Fin 2)
    (hi : s.pc i = .critical)
    (hj : s.pc (otherProc i) = .waiting ∨ s.pc (otherProc i) = .critical) :
    s.turn = i := by
  unfold PReachable at hs
  revert i hi hj
  induction hs with
  | refl =>
      intro i hi hj
      simp at hi
  | tail hb hstep ih =>
      rename_i b c
      intro i hi hj
      obtain ⟨k, rfl⟩ := hstep
      have ihA : ∀ (j : Fin 2),
          b.pc j = .turnSet ∨ b.pc j = .waiting ∨ b.pc j = .critical →
          b.flag j = true :=
        fun j h => reachable_invA b hb j h
      cases hstage : b.pc k
      · rw [pstep_idle_pc k b hstage i] at hi
        rw [pstep_idle_pc k b hstage (otherProc i)] at hj
        rw [pstep_idle_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact PStage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : otherProc i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact PStage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj
      · rw [pstep_turnSet_pc k b hstage i] at hi
        rw [pstep_turnSet_pc k b hstage (otherProc i)] at hj
        rw [pstep_turnSet_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact PStage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : otherProc i = k
          · rw [← hjk]
            exact otherProc_otherProc i
          · rw [Function.update_of_ne hjk] at hj
            have hne : k ≠ otherProc (otherProc i) := by
              rw [otherProc_otherProc i]
              exact Ne.symm hik
            have hkj : k = otherProc i := eq_of_ne_otherProc k (otherProc i) hne
            exact absurd hkj.symm hjk
      · by_cases hg : (b.flag (otherProc k) && b.turn = otherProc k) = true
        · rw [pstep_waiting_stay k b hstage hg] at hi hj ⊢
          exact ih i hi hj
        · rw [pstep_waiting_go_pc k b hstage hg i] at hi
          rw [pstep_waiting_go_pc k b hstage hg (otherProc i)] at hj
          rw [pstep_waiting_go_turn k b hstage hg]
          by_cases hik : i = k
          · rw [hik] at hi hj ⊢
            rw [Function.update_self] at hi
            have hjk : otherProc k ≠ k := otherProc_ne_self k
            rw [Function.update_of_ne hjk] at hj
            have hdisj := guard_false_cases b k hg
            rcases hdisj with hfalse | hturn
            · have hflag := ihA (otherProc k) (Or.inr hj)
              rw [hfalse] at hflag
              exact Bool.noConfusion hflag
            · exact eq_of_ne_otherProc _ _ hturn
          · rw [Function.update_of_ne hik] at hi
            by_cases hjk : otherProc i = k
            · rw [hjk, Function.update_self] at hj
              have hpcj : b.pc (otherProc i) = .waiting := by
                rw [hjk]
                exact hstage
              have hturn := ih i hi (Or.inl hpcj)
              have hok : otherProc k = i := by
                rw [← hjk]
                exact otherProc_otherProc i
              have hdisj := guard_false_cases b k hg
              rw [hok] at hdisj
              rcases hdisj with hfalse | hturn_ne
              · have hflag := ihA i (Or.inr (Or.inr hi))
                rw [hfalse] at hflag
                exact Bool.noConfusion hflag
              · exact absurd hturn hturn_ne
            · rw [Function.update_of_ne hjk] at hj
              exact ih i hi hj
      · rw [pstep_critical_pc k b hstage i] at hi
        rw [pstep_critical_pc k b hstage (otherProc i)] at hj
        rw [pstep_critical_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact PStage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : otherProc i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact PStage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj
      · rw [pstep_exiting_pc k b hstage i] at hi
        rw [pstep_exiting_pc k b hstage (otherProc i)] at hj
        rw [pstep_exiting_turn k b hstage]
        by_cases hik : i = k
        · rw [hik, Function.update_self] at hi
          exact PStage.noConfusion hi
        · rw [Function.update_of_ne hik] at hi
          by_cases hjk : otherProc i = k
          · rw [hjk, Function.update_self] at hj
            rcases hj with hj | hj <;> exact PStage.noConfusion hj
          · rw [Function.update_of_ne hjk] at hj
            exact ih i hi hj

/-- Mutual exclusion: the two processes are never both in
their critical sections in a reachable state. -/
theorem peterson_mutual_exclusion (s : PState) (hs : PReachable s) :
    ¬ (s.pc 0 = .critical ∧ s.pc 1 = .critical) := by
  intro hboth
  obtain ⟨h0, h1⟩ := hboth
  have hj0 : s.pc (otherProc 0) = .waiting ∨ s.pc (otherProc 0) = .critical :=
    Or.inr (by rw [otherProc_zero]; exact h1)
  have ht0 : s.turn = 0 := reachable_invB s hs 0 h0 hj0
  have hj1 : s.pc (otherProc 1) = .waiting ∨ s.pc (otherProc 1) = .critical :=
    Or.inr (by rw [otherProc_one]; exact h0)
  have ht1 : s.turn = 1 := reachable_invB s hs 1 h1 hj1
  have h01 : (0 : Fin 2) = 1 := ht0.symm.trans ht1
  exact fin2_zero_ne_one h01

end
