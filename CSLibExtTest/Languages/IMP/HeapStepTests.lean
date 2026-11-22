/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.HeapStep

@[expose] public section

namespace Cslib.IMP.Tests

def s0 : State := fun _ => 0

example : HStep (.write (.const 5) (.const 42), s0, Finmap.singleton 5 0)
    (.skip, s0, Finmap.insert 5 42 (Finmap.singleton 5 0)) :=
  HStep.write (by simp)

example : ∃ s', HStep (.read 0 (.const 5), s0, Finmap.singleton 5 41)
    (.skip, s', Finmap.singleton 5 41) ∧ s' 0 = 41 :=
  ⟨_, HStep.read Finmap.lookup_singleton_eq, by simp⟩

example : ∃ cfg, HStep (.alloc 0 (.const 7), s0, (∅ : Heap)) cfg ∧
    cfg.2.2.lookup (cfg.2.1 0) = some 7 := by
  refine ⟨(.skip, Function.update s0 0 0, Finmap.insert 0 7 (∅ : Heap)),
    HStep.alloc Finmap.notMem_empty, ?_⟩
  dsimp only
  rw [Function.update_self]
  exact Finmap.lookup_insert _

example (state : State) : ∃ h', HStep (.free (.const 5), state,
    Finmap.singleton 5 9) (.skip, state, h') ∧ h'.lookup 5 = none :=
  ⟨_, HStep.free (by simp), Finmap.lookup_erase _ _⟩

example : ¬ ∃ cfg, HStep (.read 0 (.const 5), s0, (∅ : Heap)) cfg := by
  rintro ⟨cfg, hstep⟩
  rw [HStep.read_iff] at hstep
  obtain ⟨_value, hlookup, _⟩ := hstep
  simp at hlookup

example : ¬ ∃ cfg, HStep (.write (.const 5) (.const 1), s0, (∅ : Heap)) cfg := by
  rintro ⟨cfg, hstep⟩
  rw [HStep.write_iff] at hstep
  obtain ⟨hmem, _⟩ := hstep
  exact Finmap.notMem_empty hmem

example : ∃ h₁, HStep (.write (.const 5) (.const 42), s0, Finmap.singleton 5 0)
      (.skip, s0, h₁) ∧ Heap.Disjoint h₁ (Finmap.singleton 9 9) ∧
    Finmap.insert 5 42 (Finmap.singleton 5 0 ∪ Finmap.singleton 9 9) =
      h₁ ∪ Finmap.singleton 9 9 := by
  apply HStep.decompose_of_safe_step
  · rw [Heap.disjoint_singleton_left]
    simp
  · exact ⟨_, HStep.write (by simp)⟩
  · exact HStep.write (by simp)

example (h : Heap) : HSteps ((Cmd.assign 0 (.const 3)).toHeap, s0, h)
    (.skip, Function.update s0 0 3, h) :=
  terminates_toHeap.mp (Terminates.assign s0 0 (.const 3))

example : (HeapCmd.seq (.alloc 1 (.const 7)) (.write (.var 1) (.const 0))).modVars
    = {1} := by
  decide

#print axioms Cslib.IMP.HSteps.decompose_of_safe
#print axioms Cslib.IMP.terminates_toHeap

end Cslib.IMP.Tests
