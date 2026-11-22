/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationLogic

@[expose] public section

namespace Cslib.IMP.Tests

open HAssertion

open scoped HAssertion

def zeroState : State := fun _ => 0

theorem allocSeven :
    SepValid HAssertion.emp (.alloc 0 (.const 7))
      (fun s h => h = Finmap.singleton (s 0) 7) := by
  refine SepValid.consequence ?_
    (SepValid.alloc (Q := fun s h => h = Finmap.singleton (s 0) 7)
      0 (.const 7)) (HAssertion.entails_refl _)
  intro s h hemp
  have hh : h = ∅ := hemp
  refine ⟨hh, ?_⟩
  intro a
  show (Finmap.singleton a ((AExp.const 7).eval s) : Heap) =
    Finmap.singleton (Function.update s 0 a 0) 7
  rw [Function.update_self]
  rfl

example :
    SepValid (HAssertion.emp ⋆ pointsTo 100 3) (.alloc 0 (.const 7))
      ((fun s h => h = Finmap.singleton (s 0) 7) ⋆ pointsTo 100 3) :=
  SepValid.frame allocSeven
    (by intro s h s' hR _hagree; exact hR)

theorem writeFive :
    SepValid (pointsTo 5 1) (.write (.const 5) (.const 2))
      (pointsTo 5 2) := by
  refine SepValid.consequence ?_
    (SepValid.write (Q := pointsTo 5 2) (.const 5) (.const 2))
    (HAssertion.entails_refl _)
  intro s h h1
  have hh : h = Finmap.singleton 5 1 := h1
  exact ⟨1, hh, rfl⟩

example :
    SepValid (pointsTo 5 41) (.read 0 (.const 5))
      (fun s h => s 0 = 41 ∧ h = Finmap.singleton 5 41) := by
  refine SepValid.consequence ?_
    (SepValid.read
      (Q := fun s h => s 0 = 41 ∧ h = Finmap.singleton 5 41)
      0 (.const 5)) (HAssertion.entails_refl _)
  intro s h h1
  have hh : h = Finmap.singleton 5 41 := h1
  refine ⟨41, hh, ?_, hh⟩
  rw [Function.update_self]

theorem readFiveTwo :
    SepValid (pointsTo 5 2) (.read 0 (.const 5))
      (fun s h => s 0 = 2 ∧ h = Finmap.singleton 5 2) := by
  refine SepValid.consequence ?_
    (SepValid.read
      (Q := fun s h => s 0 = 2 ∧ h = Finmap.singleton 5 2)
      0 (.const 5)) (HAssertion.entails_refl _)
  intro s h h1
  have hh : h = Finmap.singleton 5 2 := h1
  refine ⟨2, hh, ?_, hh⟩
  rw [Function.update_self]

example :
    SepValid (pointsTo 5 1)
      (.seq (.write (.const 5) (.const 2)) (.read 0 (.const 5)))
      (fun s h => s 0 = 2 ∧ h = Finmap.singleton 5 2) :=
  SepValid.seq writeFive readFiveTwo

example :
    SepValid (fun s _ =>
        Assertion.subst (fun (t : State) => t 0 = 3) 0 (.const 3) s)
      (Cmd.assign 0 (.const 3)).toHeap (fun s _ => s 0 = 3) :=
  SepValid.of_valid (Valid.assign (fun s => s 0 = 3) 0 (.const 3))

example (s' : State) (h' : Heap)
    (hsteps : HSteps ((Cmd.assign 0 (.const 3)).toHeap, zeroState,
      Finmap.singleton 9 9) (.skip, s', h')) : s' 0 = 3 := by
  have hv := SepValid.of_valid
    (Valid.assign (fun s => s 0 = 3) 0 (.const 3))
  have hpre : (fun (s : State) (_ : Heap) =>
        Assertion.subst (fun (t : State) => t 0 = 3) 0 (.const 3) s)
      zeroState (Finmap.singleton 9 9 : Heap) := by
    show Function.update zeroState 0 3 0 = 3
    rw [Function.update_self]
  exact (hv hpre).2 hsteps

example : (pointsTo 1 10 ⋆ pointsTo 2 20) zeroState
    (Finmap.singleton 1 10 ∪ Finmap.singleton 2 20) := by
  rw [HAssertion.star_def]
  exact ⟨Finmap.singleton 1 10, Finmap.singleton 2 20,
    Heap.disjoint_singleton_left.mpr (by simp), rfl, rfl, rfl⟩

example (h : Heap) :
    ¬ (pointsTo 1 10 ⋆ pointsTo 1 11) zeroState h :=
  fun hs => pointsTo_disjoint_false hs

#print axioms Cslib.IMP.SepValid.frame
#print axioms Cslib.IMP.SepValid.whileLoop

end Cslib.IMP.Tests
