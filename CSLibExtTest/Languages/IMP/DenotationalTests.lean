/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.Denotational
public import CSLibExt.Languages.IMP.Equivalence

@[expose] public section

namespace Cslib.IMP.DenotationalTests

def increment (name : Nat) : Cmd :=
  .assign name (.add (.var name) (.const 1))

def setThenIncrement : Cmd :=
  .seq (.assign 0 (.const 4)) (increment 0)

def countdown : Cmd :=
  .while (.not (.eq (.var 0) (.const 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

example : ∃ s', Denote setThenIncrement (fun _ => 0) s' ∧ s' 0 = 5 := by
  refine ⟨Function.update (Function.update (fun _ => 0) 0 4) 0 5, ?_, ?_⟩
  · simp only [setThenIncrement]
    rw [Denote.seq_iff]
    refine ⟨Function.update (fun _ => 0) 0 4, ?_, ?_⟩
    · rw [Denote.assign_iff]
      simp [AExp.eval]
    · simp only [increment]
      rw [Denote.assign_iff]
      simp [AExp.eval, Function.update]
  · simp [Function.update]

theorem countdown_denote (s : State) (h : s 0 = 2) :
    ∃ s', Denote countdown s s' ∧ s' 0 = 0 := by
  refine ⟨Function.update (Function.update s 0 1) 0 0, ?_, ?_⟩
  · simp only [countdown]
    rw [Denote.while_iff]
    refine Or.inr ⟨?_, Function.update s 0 1, ?_, ?_⟩
    · simp [BExp.eval, AExp.eval, h]
    · rw [Denote.assign_iff]
      simp [AExp.eval, h]
    · rw [Denote.while_iff]
      refine Or.inr ⟨?_, Function.update (Function.update s 0 1) 0 0, ?_, ?_⟩
      · simp [BExp.eval, AExp.eval, Function.update]
      · rw [Denote.assign_iff]
        simp [AExp.eval, Function.update]
      · rw [Denote.while_iff]
        refine Or.inl ⟨?_, rfl⟩
        simp [BExp.eval, AExp.eval, Function.update]
  · simp [Function.update]

example (h : Denote (increment 0) (fun _ => 0)
    (Function.update (fun _ => 0) 0 1)) :
    BigStep (increment 0) (fun _ => 0) (Function.update (fun _ => 0) 0 1) :=
  Denote.iff_bigStep.mp h

/-- All three semantics agree on the countdown program from `s 0 = 2`. -/
example (s : State) (h : s 0 = 2) :
    ∃ s', Denote countdown s s' ∧ BigStep countdown s s' ∧
      Terminates countdown s s' ∧ s' 0 = 0 := by
  obtain ⟨s', hdenote, hzero⟩ := countdown_denote s h
  exact ⟨s', hdenote, Denote.iff_bigStep.mp hdenote,
    terminates_iff_bigStep.mpr (Denote.iff_bigStep.mp hdenote), hzero⟩

/-- Regression: `simp` must terminate on a goal mentioning a loop denotation.
`Denote.while_iff` is a recursive unfolding equation and is deliberately not a
simp lemma; marking it `@[simp]` makes `simp` unfold under each fresh
existential until the recursion limit. -/
example {s s' : State} :
    Denote (.while (.truth false) .skip) s s' ↔
      Denote (.while (.truth false) .skip) s s' := by
  simp

#print axioms Cslib.IMP.Denote.iff_bigStep

end Cslib.IMP.DenotationalTests
