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
# Test-and-set consensus

The two-process consensus protocol from test-and-set:
write your input, test-and-set, then decide your own input
or read the winner's. Recorded decisions always agree.
The register-only lower bound is not included here.
-/

@[expose] public section

/-- Stages of one process in the two-process test-and-set
consensus protocol (DPA-18 core). Each process first
writes its input to its register slot, then performs
test-and-set on the shared bit: the winner decides its
own input; the loser reads the winner's register. -/
inductive CStage : Type
  | writeReg
  | testSet
  | decideOwn
  | readOther
  | done
deriving DecidableEq, Repr

/-- Protocol state for inputs `inp : Fin 2 → V`. -/
structure CState (V : Type*) where
  pc : Fin 2 → CStage
  reg : Fin 2 → Option V
  tas : Bool
  winner : Option (Fin 2)
  decision : Fin 2 → Option V

/-- The other process. -/
def otherC (i : Fin 2) : Fin 2 := ⟨1 - i.val, by
  have := i.isLt
  omega⟩

/-- One atomic step of process `i`. -/
def cstep {V : Type*} (inp : Fin 2 → V) (i : Fin 2)
    (s : CState V) : CState V :=
  match s.pc i with
  | .writeReg => { s with pc := Function.update s.pc i .testSet,
                          reg := Function.update s.reg i (some (inp i)) }
  | .testSet =>
      if s.tas then { s with pc := Function.update s.pc i .readOther }
      else { s with pc := Function.update s.pc i .decideOwn,
                    tas := true, winner := some i }
  | .decideOwn => { s with pc := Function.update s.pc i .done,
                           decision := Function.update s.decision i (some (inp i)) }
  | .readOther =>
      match s.winner with
      | some w => { s with pc := Function.update s.pc i .done,
                           decision := Function.update s.decision i (s.reg w) }
      | none => s
  | .done => s

/-- Reachability from the initial state. -/
def CReachable {V : Type*} (inp : Fin 2 → V) (s : CState V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ i, cstep inp i a = b)
    ⟨fun _ => .writeReg, fun _ => none, false, none, fun _ => none⟩ s

private def CInv {V : Type*} (inp : Fin 2 → V) (s : CState V) : Prop :=
  (∀ i, s.pc i = .writeReg → s.reg i = none) ∧
  (∀ i, s.pc i ≠ .writeReg → s.reg i = some (inp i)) ∧
  (∀ w, s.winner = some w → s.tas = true) ∧
  (∀ w, s.winner = some w → s.reg w = some (inp w)) ∧
  (∀ i, s.pc i = .decideOwn → s.winner = some i) ∧
  (∀ i x, s.decision i = some x → ∃ w, s.winner = some w ∧ x = inp w)

private theorem cInv_init {V : Type*} (inp : Fin 2 → V) :
    CInv inp ⟨fun _ => .writeReg, fun _ => none, false, none, fun _ => none⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    rfl
  · intro i h
    exact absurd rfl h
  · intro w h
    simp at h
  · intro w h
    simp at h
  · intro i h
    simp at h
  · intro i x h
    simp at h

private theorem cInv_step {V : Type*} (inp : Fin 2 → V) (s : CState V) (i : Fin 2)
    (hs : CInv inp s) : CInv inp (cstep inp i s) := by
  cases hpc : s.pc i
  case writeReg =>
    obtain ⟨hW, hR, hT, hWR, hD, hDec⟩ := hs
    simp only [cstep, hpc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · rw [hki] at hk
        have hk2 : Function.update s.pc i .testSet i = .writeReg := hk
        rw [Function.update_self] at hk2
        nomatch hk2
      · have hk2 : Function.update s.pc i .testSet k = .writeReg := hk
        rw [Function.update_of_ne hki] at hk2
        have g : Function.update s.reg i (some (inp i)) k = none := by
          rw [Function.update_of_ne hki]
          exact hW k hk2
        exact g
    · intro k hk
      by_cases hki : k = i
      · rw [hki]
        exact Function.update_self i (some (inp i)) s.reg
      · have hk2 : Function.update s.pc i .testSet k ≠ .writeReg := hk
        rw [Function.update_of_ne hki] at hk2
        have g : Function.update s.reg i (some (inp i)) k = some (inp k) := by
          rw [Function.update_of_ne hki]
          exact hR k hk2
        exact g
    · intro w hw
      exact hT w hw
    · intro w hw
      by_cases hwi : w = i
      · rw [hwi]
        exact Function.update_self i (some (inp i)) s.reg
      · have g : Function.update s.reg i (some (inp i)) w = some (inp w) := by
          rw [Function.update_of_ne hwi]
          exact hWR w hw
        exact g
    · intro k hk
      by_cases hki : k = i
      · rw [hki] at hk
        have hk2 : Function.update s.pc i .testSet i = .decideOwn := hk
        rw [Function.update_self] at hk2
        nomatch hk2
      · have hk2 : Function.update s.pc i .testSet k = .decideOwn := hk
        rw [Function.update_of_ne hki] at hk2
        exact hD k hk2
    · intro k x hk
      obtain ⟨w, hww, hx⟩ := hDec k x hk
      exact ⟨w, hww, hx⟩
  case testSet =>
    by_cases ht : s.tas = true
    · obtain ⟨hW, hR, hT, hWR, hD, hDec⟩ := hs
      simp only [cstep, hpc]
      rw [ite_eq_left ht]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.pc i .readOther i = .writeReg := hk
          rw [Function.update_self] at hk2
          nomatch hk2
        · have hk2 : Function.update s.pc i .readOther k = .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hW k hk2
      · intro k hk
        by_cases hki : k = i
        · rw [hki]
          exact hR i (by simp [hpc])
        · have hk2 : Function.update s.pc i .readOther k ≠ .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hR k hk2
      · intro w hw
        exact hT w hw
      · intro w hw
        exact hWR w hw
      · intro k hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.pc i .readOther i = .decideOwn := hk
          rw [Function.update_self] at hk2
          nomatch hk2
        · have hk2 : Function.update s.pc i .readOther k = .decideOwn := hk
          rw [Function.update_of_ne hki] at hk2
          exact hD k hk2
      · intro k x hk
        obtain ⟨w, hww, hx⟩ := hDec k x hk
        exact ⟨w, hww, hx⟩
    · obtain ⟨hW, hR, hT, _, hD, hDec⟩ := hs
      simp only [cstep, hpc]
      rw [ite_eq_right ht]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.pc i .decideOwn i = .writeReg := hk
          rw [Function.update_self] at hk2
          nomatch hk2
        · have hk2 : Function.update s.pc i .decideOwn k = .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hW k hk2
      · intro k hk
        by_cases hki : k = i
        · rw [hki]
          exact hR i (by simp [hpc])
        · have hk2 : Function.update s.pc i .decideOwn k ≠ .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hR k hk2
      · intro w hw
        have hw2 : (some i : Option (Fin 2)) = some w := hw
        have hij : i = w := Option.some_inj.mp hw2
        subst hij
        rfl
      · intro w hw
        have hw2 : (some i : Option (Fin 2)) = some w := hw
        have hij : i = w := Option.some_inj.mp hw2
        subst hij
        exact hR i (by simp [hpc])
      · intro k hk
        by_cases hki : k = i
        · rw [hki]
        · have hk2 : Function.update s.pc i .decideOwn k = .decideOwn := hk
          rw [Function.update_of_ne hki] at hk2
          exact absurd (hT k (hD k hk2)) ht
      · intro k x hk
        obtain ⟨w, hww, hx⟩ := hDec k x hk
        exact absurd (hT w hww) ht
  case decideOwn =>
    obtain ⟨hW, hR, hT, hWR, hD, hDec⟩ := hs
    simp only [cstep, hpc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · rw [hki] at hk
        have hk2 : Function.update s.pc i .done i = .writeReg := hk
        rw [Function.update_self] at hk2
        nomatch hk2
      · have hk2 : Function.update s.pc i .done k = .writeReg := hk
        rw [Function.update_of_ne hki] at hk2
        exact hW k hk2
    · intro k hk
      by_cases hki : k = i
      · rw [hki]
        exact hR i (by simp [hpc])
      · have hk2 : Function.update s.pc i .done k ≠ .writeReg := hk
        rw [Function.update_of_ne hki] at hk2
        exact hR k hk2
    · intro w hw
      exact hT w hw
    · intro w hw
      exact hWR w hw
    · intro k hk
      by_cases hki : k = i
      · rw [hki]
        exact hD i hpc
      · have hk2 : Function.update s.pc i .done k = .decideOwn := hk
        rw [Function.update_of_ne hki] at hk2
        exact hD k hk2
    · intro k x hk
      by_cases hki : k = i
      · rw [hki] at hk
        have hk2 : Function.update s.decision i (some (inp i)) i = some x := hk
        rw [Function.update_self] at hk2
        have hx : inp i = x := Option.some_inj.mp hk2
        subst hx
        exact ⟨i, hD i hpc, rfl⟩
      · have hk2 : Function.update s.decision i (some (inp i)) k = some x := hk
        rw [Function.update_of_ne hki] at hk2
        obtain ⟨w, hww, hx⟩ := hDec k x hk2
        exact ⟨w, hww, hx⟩
  case readOther =>
    match hw : s.winner with
    | some w0 =>
      obtain ⟨hW, hR, hT, hWR, hD, hDec⟩ := hs
      have hstep : cstep inp i s =
          { s with pc := Function.update s.pc i .done,
                   decision := Function.update s.decision i (s.reg w0) } := by
        simp [cstep, hpc, hw]
      rw [hstep]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.pc i .done i = .writeReg := hk
          rw [Function.update_self] at hk2
          nomatch hk2
        · have hk2 : Function.update s.pc i .done k = .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hW k hk2
      · intro k hk
        by_cases hki : k = i
        · rw [hki]
          exact hR i (by simp [hpc])
        · have hk2 : Function.update s.pc i .done k ≠ .writeReg := hk
          rw [Function.update_of_ne hki] at hk2
          exact hR k hk2
      · intro w hw'
        exact hT w hw'
      · intro w hw'
        exact hWR w hw'
      · intro k hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.pc i .done i = .decideOwn := hk
          rw [Function.update_self] at hk2
          nomatch hk2
        · have hk2 : Function.update s.pc i .done k = .decideOwn := hk
          rw [Function.update_of_ne hki] at hk2
          exact hD k hk2
      · intro k x hk
        by_cases hki : k = i
        · rw [hki] at hk
          have hk2 : Function.update s.decision i (s.reg w0) i = some x := hk
          rw [Function.update_self] at hk2
          rw [hWR w0 hw] at hk2
          have hx : inp w0 = x := Option.some_inj.mp hk2
          subst hx
          exact ⟨w0, hw, rfl⟩
        · have hk2 : Function.update s.decision i (s.reg w0) k = some x := hk
          rw [Function.update_of_ne hki] at hk2
          obtain ⟨w, hww, hx⟩ := hDec k x hk2
          exact ⟨w, hww, hx⟩
    | none =>
      simp only [cstep, hpc, hw]
      exact hs
  case done =>
    simp only [cstep, hpc]
    exact hs

/-- Agreement and validity: in every reachable state, any
two recorded decisions agree, and every recorded decision
is one of the two inputs (the winner's). -/
theorem tas_consensus {V : Type*} (inp : Fin 2 → V) (s : CState V)
    (hs : CReachable inp s) :
    (∀ i j x y, s.decision i = some x → s.decision j = some y → x = y)
    ∧ (∀ i x, s.decision i = some x → ∃ w, x = inp w) := by
  have hP : ∀ t, CReachable inp t → CInv inp t := by
    intro t ht
    induction ht with
    | refl => exact cInv_init inp
    | tail _ hstep ih =>
      obtain ⟨i, rfl⟩ := hstep
      exact cInv_step inp _ i ih
  obtain ⟨_, _, _, _, _, hDec⟩ := hP s hs
  refine ⟨?_, ?_⟩
  · intro i j x y hi hj
    obtain ⟨w1, hw1, hx⟩ := hDec i x hi
    obtain ⟨w2, hw2, hy⟩ := hDec j y hj
    have h12 : w1 = w2 := Option.some_inj.mp (hw1.symm.trans hw2)
    subst h12
    cases hx
    cases hy
    rfl
  · intro i x hi
    obtain ⟨w, _, hx⟩ := hDec i x hi
    exact ⟨w, hx⟩

end
