/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationRules
public import CSLibExt.Languages.IMP.SeparationAPI

/-!
# Backward reasoning for heap programs

A full resource lifecycle allocates a fresh cell, overwrites it, reads
it into a distinct variable, then frees it. The proof works on every
initial heap and restores that heap exactly. Further tests exercise
framing, old-store evaluation, universal allocation and memory faults.
-/

@[expose] public section

namespace Cslib.IMP.SeparationRulesTests

open HAssertion
open scoped HAssertion

private def cycle : HeapCmd :=
  .seq (.alloc 0 (.const 7))
    (.seq (.write (.var 0) (.const 9))
      (.seq (.read 1 (.var 0)) (.free (.var 0))))

private theorem erase_fresh_insert {a v : Nat} {h : Heap}
    (ha : a ∉ h) : Finmap.erase a (Finmap.insert a v h) = h := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = a
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_eq_none.mpr ha]
  · rw [Finmap.lookup_erase_ne hx, Finmap.lookup_insert_of_ne _ hx]

private theorem cycle_spec (h : Heap) (s : State) :
    safePre cycle (fun t k => t 1 = 9 ∧ k = h) s h := by
  apply safePre.seq
  rw [safePre.alloc_iff]
  intro a ha
  apply safePre.seq
  rw [safePre.write_iff]
  simp only [AExp.eval_var, Function.update_self, AExp.eval_const,
    Finmap.mem_insert, true_or, Finmap.insert_insert, true_and]
  apply safePre.seq
  rw [safePre.read_iff]
  refine ⟨9, ?_, ?_⟩
  · change (Finmap.insert a 9 h).lookup a = some 9
    exact Finmap.lookup_insert h
  · rw [safePre.free_iff]
    simp [AExp.eval, erase_fresh_insert ha]

-- A finite execution witnesses that the lifecycle specification is inhabited.
example (h : Heap) (s : State) :
    ∃ t, HSteps (cycle, s, h) (.skip, t, h) ∧ t 1 = 9 := by
  obtain ⟨a, ha⟩ := Heap.exists_notMem h
  let t := Function.update s 0 a
  let u := Function.update t 1 9
  have halloc : HSteps (.alloc 0 (.const 7), s, h)
      (.skip, t, Finmap.insert a 7 h) := .single (.alloc ha)
  have hwrite : HSteps (.write (.var 0) (.const 9), t,
      Finmap.insert a 7 h) (.skip, t, Finmap.insert a 9 h) := by
    have hm : (AExp.var 0).eval t ∈ Finmap.insert a 7 h := by
      simp [t, AExp.eval]
    simpa [t, AExp.eval] using HSteps.single
      (HStep.write (value := .const 9) hm)
  have hread : HSteps (.read 1 (.var 0), t, Finmap.insert a 9 h)
      (.skip, u, Finmap.insert a 9 h) := by
    apply HSteps.single
    apply HStep.read
    change (Finmap.insert a 9 h).lookup a = some 9
    exact Finmap.lookup_insert h
  have hfree : HSteps (.free (.var 0), u, Finmap.insert a 9 h)
      (.skip, u, h) := by
    have hm : (AExp.var 0).eval u ∈ Finmap.insert a 9 h := by
      simp [u, t, AExp.eval]
    simpa [u, t, AExp.eval, erase_fresh_insert ha] using
      HSteps.single (HStep.free hm)
  refine ⟨u, ?_, by simp [u]⟩
  exact (halloc.seq_congr.trans HSteps.seq_skip).trans
    ((hwrite.seq_congr.trans HSteps.seq_skip).trans
      ((hread.seq_congr.trans HSteps.seq_skip).trans hfree))

example (h : Heap) (s : State) :
    safePre cycle (fun t k => t 1 = 9 ∧ k = h) s h := cycle_spec h s

example : SepValid emp cycle (fun t h => t 1 = 9 ∧ h = ∅) := by
  intro s h hh
  have heq : h = ∅ := hh
  subst h
  exact cycle_spec ∅ s

-- The frame remains present after the fresh cell has been freed.
example : (pointsTo 100 3).Entails
    (safePre cycle ((fun t h => t 1 = 9 ∧ h = ∅) ⋆ pointsTo 100 3)) := by
  have hlocal : emp.Entails
      (safePre cycle (fun t h => t 1 = 9 ∧ h = ∅)) := by
    intro s h hh
    have heq : h = ∅ := hh
    subst h
    exact cycle_spec ∅ s
  have hf := (star_mono hlocal (entails_refl (pointsTo 100 3))).trans
    (safePre.frame (frame_of_storeIrrel pointsTo_storeIrrel _))
  simpa only [emp_star] using hf

-- A read into its own address variable uses the address in the old store.
example (s : State) (h : Heap) (v : Nat) (hv : h.lookup (s 0) = some v) :
    safePre (.read 0 (.var 0)) (fun t k => t 0 = v ∧ k = h) s h := by
  rw [safePre.read_iff]
  exact ⟨v, hv, by simp⟩

example (s : State) (h : Heap) :
    safePre (.assign 0 (.add (.var 0) (.const 1)))
      (fun t k => t 0 = s 0 + 1 ∧ k = h) s h := by
  rw [safePre.assign_iff]
  simp [AExp.eval, Function.update_self]

-- Allocating into a variable also evaluates the stored value before assignment.
example (s : State) (h : Heap) :
    safePre (.alloc 0 (.var 0))
      (fun t k => k.lookup (t 0) = some (s 0)) s h := by
  rw [safePre.alloc_iff]
  intro a _ha
  change (Finmap.insert a (s 0) h).lookup a = some (s 0)
  exact Finmap.lookup_insert h

-- An occupied address is excluded from allocation's quantifier domain.
example (s : State) (h : Heap) (a : Nat) (ha : a ∈ h) :
    safePre (.alloc 0 (.const 7)) (fun t _ => t 0 ≠ a) s h := by
  rw [safePre.alloc_iff]
  intro b hb
  simpa using (ne_of_mem_of_not_mem ha hb).symm

-- No chosen address can be guaranteed on the empty heap.
example (s : State) (a : Nat) :
    ¬ safePre (.alloc 0 (.const 7)) (fun t _ => t 0 = a) s ∅ := by
  rw [safePre.alloc_iff]
  intro hp
  have hb := hp (a + 1) Finmap.notMem_empty
  simp at hb

example (s : State) (h : Heap) (a : Nat) (ha : a ∉ h) :
    ¬ safePre (.read 0 (.const a)) (fun _ _ => True) s h := by
  rw [safePre.read_iff]
  rintro ⟨v, hv, -⟩
  exact ha (Finmap.mem_of_lookup_eq_some hv)

example (s : State) (h : Heap) (a : Nat) (ha : a ∉ h) :
    ¬ safePre (.write (.const a) (.const 9)) (fun _ _ => True) s h := by
  rw [safePre.write_iff]
  exact fun hp => ha hp.1

example (s : State) (h : Heap) (a : Nat) (ha : a ∉ h) :
    ¬ safePre (.free (.const a)) (fun _ _ => True) s h := by
  rw [safePre.free_iff]
  exact fun hp => ha hp.1

-- A real execution reaches the second free after erasing its address.
example (s : State) (h : Heap) (a : Nat) (ha : a ∈ h) :
    ¬ safePre (.seq (.free (.const a)) (.free (.const a)))
      (fun _ _ => True) s h := by
  intro hp
  have hs : HSteps
      (.seq (.free (.const a)) (.free (.const a)), s, h)
      (.free (.const a), s, Finmap.erase a h) :=
    (HSteps.single (.seqStep (.free ha))).tail (.seqSkip _ _ _)
  rcases hp.1 _ hs with hskip | ⟨cfg, hstep⟩
  · cases hskip
  · exact Finmap.notMem_erase_self (HStep.free_iff.mp hstep).1

-- A faulting unselected branch does not invalidate a safe conditional.
example (s : State) :
    safePre (.ite (.truth false) (.free (.const 7)) .skip) emp s ∅ := by
  apply safePre.ite
  constructor
  · simp
  · intro _
    rw [safePre.skip]
    rfl

-- A supplied invariant suffices for partial correctness of a countdown loop.
example : emp.Entails (safePre
    (.while (.not (.eq (.var 0) (.const 0)))
      (.assign 0 (.sub (.var 0) (.const 1))))
    (fun s h => h = ∅ ∧ s 0 = 0)) := by
  apply safePre.whileLoop (I := emp)
  · intro s h hp
    rw [safePre.assign_iff]
    exact hp.1
  · intro s h hp
    exact ⟨hp.1, of_decide_eq_true (Bool.eq_true_of_not_eq_false' hp.2)⟩

end Cslib.IMP.SeparationRulesTests
