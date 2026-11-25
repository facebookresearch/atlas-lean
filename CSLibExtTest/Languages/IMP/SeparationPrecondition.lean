/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationPrecondition
public import CSLibExt.Languages.IMP.SeparationAPI

/-!
# Separating implication and safe backward-precondition tests

The examples distinguish disjoint extension from material implication,
fault avoidance from termination, and demonic allocation from a chosen
fresh-address witness. The last example exhibits the frame rule's store
side condition using a real assignment.
-/

@[expose] public section

namespace Cslib.IMP.SeparationPreconditionTests

open HAssertion
open scoped HAssertion

private def zero : State := fun _ => 0

-- A cell can be extended with any disjoint second cell.
example : (pointsTo 0 10).Entails
    (wand (pointsTo 1 20) (pointsTo 0 10 ⋆ pointsTo 1 20)) :=
  star_entails_iff_entails_wand.mp (entails_refl _)

example : wand (pointsTo 1 20) (pointsTo 0 10 ⋆ pointsTo 1 20)
    zero (Finmap.singleton 0 10) :=
  (star_entails_iff_entails_wand.mp (entails_refl _)) rfl

-- The adjunction also consumes a wand and an actually disjoint resource.
example (s : State) (h : Heap)
    (hs : (wand (pointsTo 1 20) (pointsTo 0 10 ⋆ pointsTo 1 20) ⋆
      pointsTo 1 20) s h) : (pointsTo 0 10 ⋆ pointsTo 1 20) s h :=
  star_wand_elim hs

-- Overlapping cells admit no extension, so this wand is vacuously true.
example : wand (pointsTo 1 20) (fun _ _ => False)
    zero (Finmap.singleton 1 10) := by
  intro hf hd hR
  have heq : hf = Finmap.singleton 1 20 := hR
  exact hd 1 (by simp) (by simp [heq])

-- Material implication holds on the empty heap; the corresponding wand fails.
example : (pointsTo 1 20 zero ∅ → False) ∧
    ¬ wand (pointsTo 1 20) (fun _ _ => False) zero ∅ := by
  constructor
  · intro hp
    have hm : 1 ∈ (∅ : Heap) := by rw [hp]; simp
    exact Finmap.notMem_empty hm
  · intro hw
    exact hw (Finmap.singleton 1 20) (Heap.disjoint_empty_left _) rfl

example (Q : HAssertion) : wand emp Q = Q := wand_emp

example {P P' Q Q' : HAssertion} (hP : P'.Entails P)
    (hQ : Q.Entails Q') : (wand P Q).Entails (wand P' Q') :=
  wand_mono hP hQ

example (P Q : HAssertion) (c : HeapCmd) :
    SepValid P c Q ↔ P.Entails (safePre c Q) := safePre.valid_iff

example (P Q : HAssertion) (c : HeapCmd) :
    safePre c (hand P Q) = hand (safePre c P) (safePre c Q) :=
  safePre.hand c P Q

example (Q : HAssertion) : safePre .skip Q = Q := safePre.skip Q

example (c : HeapCmd) (s : State) (h : Heap) :
    safePre c (fun _ _ => True) s h ↔ Safe (c, s, h) :=
  safePre.true_iff

-- There are no terminating runs of a missing read, but safety still fails.
example : ¬ safePre (.read 0 (.const 7)) (fun _ _ => True) zero ∅ := by
  intro hp
  rcases hp.1 _ .refl with hskip | ⟨cfg, hstep⟩
  · cases hskip
  · obtain ⟨v, hv, -⟩ := HStep.read_iff.mp hstep
    simp at hv

-- A safe infinite loop satisfies even the constantly false postcondition.
example (s : State) (h : Heap) :
    safePre (.while (.truth true) .skip) (fun _ _ => False) s h := by
  have hv : SepValid (fun _ _ => True)
      (.while (.truth true) .skip) (fun _ _ => False) := by
    apply SepValid.consequence (entails_refl _)
      (SepValid.whileLoop (I := fun _ _ => True) ?_) ?_
    · exact SepValid.consequence (fun _ _ _ => trivial)
        (SepValid.skip _) (entails_refl _)
    · intro t k hpost
      simpa using hpost.2
  exact (safePre.valid_iff.mp hv) trivial

private theorem allocation : emp.Entails
    (safePre (.alloc 0 (.const 5))
      (fun s h => h = Finmap.singleton (s 0) 5)) := by
  intro s h hh
  apply SepValid.alloc 0 (.const 5)
  refine ⟨hh, ?_⟩
  intro a
  simp [AExp.eval]

-- The returned address owns the new cell, whatever fresh address was chosen.
example (s : State) : safePre (.alloc 0 (.const 5))
    (fun t h => h = Finmap.singleton (t 0) 5) s ∅ :=
  allocation rfl

-- Framing allocation preserves a concrete, disjoint old cell.
example : (pointsTo 100 3).Entails
    (safePre (.alloc 0 (.const 5))
      ((fun s h => h = Finmap.singleton (s 0) 5) ⋆ pointsTo 100 3)) := by
  have hframe := (star_mono allocation (entails_refl (pointsTo 100 3))).trans
    (safePre.frame (frame_of_storeIrrel pointsTo_storeIrrel _))
  simpa only [emp_star] using hframe

-- Choosing address zero is possible, but does not establish a universal postcondition.
example (s : State) :
    (∃ t h, HSteps (.alloc 0 (.const 5), s, ∅) (.skip, t, h) ∧ t 0 = 0) ∧
    ¬ safePre (.alloc 0 (.const 5)) (fun t _ => t 0 = 0) s ∅ := by
  constructor
  · exact ⟨_, _, .single (.alloc (address := 0) Finmap.notMem_empty),
      Function.update_self ..⟩
  · intro hp
    have hz := hp.2 (.single (HStep.alloc (address := 1) Finmap.notMem_empty))
    simp at hz

example (c : HeapCmd) (Q R : HAssertion) (hR : StoreIrrel R) :
    (safePre c Q).Entails (wand R (safePre c (Q ⋆ R))) :=
  safePre.frame_wand (frame_of_storeIrrel hR c)

-- A store-dependent frame invalidated by assignment cannot be framed.
example :
    (safePre (.assign 0 (.const 1)) emp ⋆
      (fun s h => h = ∅ ∧ s 0 = 0)) zero ∅ ∧
    ¬ safePre (.assign 0 (.const 1))
      (emp ⋆ (fun s h => h = ∅ ∧ s 0 = 0)) zero ∅ := by
  constructor
  · refine ⟨∅, ∅, Heap.disjoint_empty_left _, by simp, ?_, rfl, rfl⟩
    exact SepValid.assign (Q := emp) 0 (.const 1) rfl
  · rw [emp_star]
    intro hp
    have hz := (hp.2 (.single (HStep.assign zero 0 (.const 1) ∅))).2
    simp at hz

end Cslib.IMP.SeparationPreconditionTests
