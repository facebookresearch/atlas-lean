/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationVCG
public import CSLibExt.Languages.IMP.SeparationAPI

/-!
# Tests for the annotated separation-logic VCG

A resource lifecycle is proved from generated conditions, then used in a
loop and framed by an untouched cell. Negative examples separate generated
preconditions from verification conditions and exercise the obligations
for loop preservation, loop exit and store-dependent frames.
-/

@[expose] public section

namespace Cslib.IMP.SeparationVCGTests

open HAssertion
open scoped HAssertion

private def zero : State := fun _ => 0

private def cycle : AHeapCmd :=
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

private theorem cycle_pre (s : State) (h : Heap) :
    cycle.pre (fun t k => t 1 = 9 ∧ k = h) s h := by
  simp only [cycle, AHeapCmd.pre, AExp.eval, Function.update_self,
    Finmap.mem_insert, true_or, true_and, Finmap.insert_insert]
  intro a ha
  refine ⟨9, Finmap.lookup_insert _, ?_⟩
  simp [erase_fresh_insert ha]

private theorem cycle_run (s : State) (h : Heap) (a : Nat)
    (ha : a ∉ h) : HSteps (cycle.strip, s, h)
      (.skip, Function.update (Function.update s 0 a) 1 9, h) := by
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
  exact (halloc.seq_congr.trans HSteps.seq_skip).trans
    ((hwrite.seq_congr.trans HSteps.seq_skip).trans
      ((hread.seq_congr.trans HSteps.seq_skip).trans hfree))

example (h : Heap) : SepValid (fun _ k => k = h) cycle.strip
    (fun t k => t 1 = 9 ∧ k = h) := by
  apply AHeapCmd.vc_valid (by simp [cycle, AHeapCmd.vc])
  intro s k hk
  subst k
  exact cycle_pre s h

-- Explicit frames erase to exactly the same executable program.
example : (AHeapCmd.frame (pointsTo 100 3)
    (fun t h => t 1 = 9 ∧ h = ∅) cycle).strip = cycle.strip := rfl

example : SepValid (pointsTo 100 3) cycle.strip
    ((fun t h => t 1 = 9 ∧ h = ∅) ⋆ pointsTo 100 3) := by
  apply AHeapCmd.vc_valid (C := .frame (pointsTo 100 3)
    (fun t h => t 1 = 9 ∧ h = ∅) cycle)
  · exact ⟨by simp [cycle, AHeapCmd.vc],
      frame_of_storeIrrel pointsTo_storeIrrel _, entails_refl _⟩
  · have hc : emp.Entails
        (cycle.pre (fun t h => t 1 = 9 ∧ h = ∅)) := by
      intro s h hh
      have heq : h = ∅ := hh
      subst h
      exact cycle_pre s ∅
    simpa only [AHeapCmd.pre, emp_star] using
      star_mono hc (entails_refl (pointsTo 100 3))

private def recycle : AHeapCmd :=
  .while emp (.not (.eq (.var 2) (.const 0)))
    (.seq cycle (.assign 2 (.sub (.var 2) (.const 1))))

private def done : HAssertion := fun s h => h = ∅ ∧ s 2 = 0

private theorem recycle_vc : recycle.vc done := by
  refine ⟨?_, ?_, by simp [cycle, AHeapCmd.vc]⟩
  · intro s h hp
    change cycle.pre emp s h
    have heq : h = ∅ := hp.1
    subst h
    exact AHeapCmd.pre_mono cycle (fun {_ _} hh => hh.2) (cycle_pre s ∅)
  · intro s h hp
    exact ⟨hp.1, of_decide_eq_true (Bool.eq_true_of_not_eq_false' hp.2)⟩

-- Every iteration allocates and frees its own cell; the loop exits at zero.
example : SepValid emp recycle.strip done :=
  AHeapCmd.vc_valid recycle_vc (entails_refl _)

example : SepValid (pointsTo 100 3) recycle.strip (done ⋆ pointsTo 100 3) := by
  apply AHeapCmd.vc_valid (C := .frame (pointsTo 100 3) done recycle)
  · exact ⟨recycle_vc, frame_of_storeIrrel pointsTo_storeIrrel _,
      entails_refl _⟩
  · simpa only [AHeapCmd.pre, recycle, emp_star] using
      entails_refl (pointsTo 100 3)

-- A concrete zero-iteration run checks the erasure's loop and branch shape.
example : HSteps (recycle.strip, zero, ∅) (.skip, zero, ∅) := by
  exact (HSteps.single (.whileStep _ _ _ _)).tail (.iteFalse rfl)

-- One complete iteration allocates, mutates, reads and frees before exit.
example : ∃ t, HSteps (recycle.strip, Function.update zero 2 1, ∅)
    (.skip, t, ∅) ∧ t 1 = 9 ∧ t 2 = 0 := by
  let s := Function.update zero 2 1
  let u := Function.update (Function.update s 0 0) 1 9
  let v := Function.update u 2 ((AExp.sub (.var 2) (.const 1)).eval u)
  have hb : HSteps ((HeapCmd.seq cycle.strip
      (.assign 2 (.sub (.var 2) (.const 1)))), s, ∅) (.skip, v, ∅) :=
    ((cycle_run s ∅ 0 Finmap.notMem_empty).seq_congr.trans
      HSteps.seq_skip).tail (.assign _ _ _ _)
  have hp : HSteps (recycle.strip, s, ∅)
      (.seq (.seq cycle.strip (.assign 2 (.sub (.var 2) (.const 1))))
        recycle.strip, s, ∅) :=
    (HSteps.single (.whileStep _ _ _ _)).tail (.iteTrue rfl)
  have he : HSteps (recycle.strip, v, ∅) (.skip, v, ∅) :=
    (HSteps.single (.whileStep _ _ _ _)).tail (.iteFalse rfl)
  refine ⟨v, hp.trans ((hb.seq_congr.trans HSteps.seq_skip).trans he), ?_⟩
  simp [v, u, s, AExp.eval]

example (s : State) (h : Heap) (v : Nat) (hv : h.lookup (s 0) = some v) :
    (AHeapCmd.read 0 (.var 0)).pre (fun t k => t 0 = v ∧ k = h) s h :=
  ⟨v, hv, by simp⟩

example (s : State) (h : Heap) :
    (AHeapCmd.alloc 0 (.var 0)).pre
      (fun t k => k.lookup (t 0) = some (s 0)) s h := by
  intro a _ha
  change (Finmap.insert a (s 0) h).lookup a = some (s 0)
  exact Finmap.lookup_insert h

example (a : Nat) : ¬ (AHeapCmd.alloc 0 (.const 7)).pre
    (fun t _ => t 0 = a) zero ∅ := by
  intro hp
  have hx := hp (a + 1) Finmap.notMem_empty
  simp at hx

example : (AHeapCmd.free (.const 7)).vc (fun _ _ => True) ∧
    ¬ (AHeapCmd.free (.const 7)).pre (fun _ _ => True) zero ∅ :=
  ⟨trivial, fun hp => Finmap.notMem_empty hp.1⟩

example (s : State) (h : Heap) (a : Nat) (ha : a ∉ h) :
    ¬ (AHeapCmd.read 0 (.const a)).pre (fun _ _ => True) s h := by
  rintro ⟨v, hv, -⟩
  exact ha (Finmap.mem_of_lookup_eq_some hv)

example (s : State) (h : Heap) (a : Nat) (ha : a ∉ h) :
    ¬ (AHeapCmd.write (.const a) (.const 9)).pre (fun _ _ => True) s h :=
  fun hp => ha hp.1

example (s : State) (h : Heap) (a : Nat) :
    ¬ (AHeapCmd.seq (.free (.const a)) (.free (.const a))).pre
      (fun _ _ => True) s h :=
  fun hp => Finmap.notMem_erase_self hp.2.1

example : SepValid emp
    (AHeapCmd.ite (.truth false) (.free (.const 7)) .skip).strip emp := by
  apply AHeapCmd.vc_valid
    (C := .ite (.truth false) (.free (.const 7)) .skip) ⟨trivial, trivial⟩
  intro s h hp
  simpa [AHeapCmd.pre, BExp.eval] using hp

private def badLoop : AHeapCmd :=
  .while emp (.truth true) (.write (.const 7) (.const 9))

-- The invariant allows an empty heap, on which the body faults.
private theorem badLoop_vc : ¬ badLoop.vc emp := by
  intro hv
  have hp := hv.1 (s := zero) (h := ∅) ⟨rfl, rfl⟩
  exact Finmap.notMem_empty hp.1

example : ¬ (AHeapCmd.seq .skip badLoop).vc emp := fun hv => badLoop_vc hv.2

-- Both branch VCs are generated, even for an unselected branch.
example : ¬ (AHeapCmd.ite (.truth false) badLoop .skip).vc emp :=
  fun hv => badLoop_vc hv.1

example : ¬ (AHeapCmd.while emp (.truth false) .skip).vc
    (fun _ _ => False) := by
  intro hv
  exact hv.2.1 (s := zero) (h := ∅) ⟨rfl, rfl⟩

-- A local framed postcondition must actually entail the requested result.
example : ¬ (AHeapCmd.frame emp emp .skip).vc (fun _ _ => False) := by
  intro hv
  apply hv.2.2 (s := zero) (h := ∅)
  rw [emp_star]
  rfl

-- The same rejected annotation has an inhabited generated entry predicate.
example : (AHeapCmd.frame (fun s h => h = ∅ ∧ s 0 = 0) emp
    (.assign 0 (.const 1))).pre (fun _ _ => True) zero ∅ := by
  change (emp ⋆ (fun s h => h = ∅ ∧ s 0 = 0)) zero ∅
  rw [emp_star]
  exact ⟨rfl, rfl⟩

-- Its erased program is safe from that entry despite the false frame VC.
-- Verification conditions are sufficient, not necessary, for this triple.
example : SepValid
    ((AHeapCmd.frame (fun s h => h = ∅ ∧ s 0 = 0) emp
      (.assign 0 (.const 1))).pre (fun _ _ => True))
    (AHeapCmd.frame (fun s h => h = ∅ ∧ s 0 = 0) emp
      (.assign 0 (.const 1))).strip (fun _ _ => True) := by
  apply safePre.valid_iff.mpr
  intro s h _
  exact safePre.assign_iff.mpr trivial

-- Assignment invalidates this store-dependent frame, so its VC is rejected.
example : ¬ (AHeapCmd.frame (fun s h => h = ∅ ∧ s 0 = 0) emp
    (.assign 0 (.const 1))).vc (fun _ _ => True) := by
  intro hv
  have hp := hv.2.1 (s := zero) (h := ∅)
    (s' := Function.update zero 0 1) ⟨rfl, rfl⟩ (by
      intro x hx
      have hne : x ≠ 0 := by simpa [AHeapCmd.strip, HeapCmd.modVars] using hx
      exact Function.update_of_ne hne _ _)
  simp at hp

end Cslib.IMP.SeparationVCGTests
