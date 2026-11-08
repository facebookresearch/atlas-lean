/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.KdTree

/-!
# Tests for the kd-tree API

Client examples for empty/singleton trees, axis cycling, split-plane
duplicates, pruning boundaries, and concrete reports through the public
executable and correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KdTreeTests

open Cslib.Algorithms.Lean

/-- A 2D point as a `Fin 2 → Int`. -/
public def pt (x y : Int) : Fin 2 → Int :=
  fun i => if i.val = 0 then x else y

example : (KdTree.empty : KdTree 2).toList = [] := rfl
example : (KdTree.empty : KdTree 2).size = 0 := rfl
example : (KdTree.empty : KdTree 2).report (pt 0 0) (pt 1 1) = [] := rfl
example : (KdTree.leaf (pt 1 2)).toList = [pt 1 2] := rfl
example : (KdTree.leaf (pt 1 2)).size = 1 := rfl

example : (KdTree.build (0 : Fin 2) ([] : List (Fin 2 → Int))).size = 0 :=
  KdTree.size_build _ _
example : (KdTree.build (0 : Fin 2) [pt 3 4]).size = 1 :=
  KdTree.size_build _ _
example : pt 3 4 ∈ (KdTree.build (0 : Fin 2) [pt 3 4, pt 0 0]).toList := by
  rw [KdTree.mem_toList_build_iff]; simp

/-- Axis cycling: `nextAxis` advances and wraps. -/
example : KdTree.nextAxis (0 : Fin 2) = 1 := rfl
example : KdTree.nextAxis (1 : Fin 2) = 0 := rfl

public def sample : List (Fin 2 → Int) := [pt 0 0, pt 1 5, pt 2 2, pt 5 1, pt 5 5]

example : (KdTree.buildRoot sample).Valid := KdTree.valid_buildRoot sample
example : (KdTree.buildRoot sample).size = 5 := KdTree.size_build _ sample
example : (KdTree.buildRoot sample).toList.Perm sample :=
  KdTree.toList_buildRoot_perm sample

/-- Duplicates on the split plane are retained (permutation, with counts). -/
example : ((KdTree.buildRoot [pt 1 1, pt 1 1, pt 1 2]).toList).length = 3 := by
  have h := KdTree.toList_buildRoot_perm [pt 1 1, pt 1 1, pt 1 2]
  rw [h.length_eq]; rfl

example (p : Fin 2 → Int) :
    p ∈ (KdTree.buildRoot sample).report (pt 0 0) (pt 2 2) ↔
      p ∈ sample ∧ KdTree.inBox (pt 0 0) (pt 2 2) p :=
  KdTree.mem_report_buildRoot_iff sample

/-- Concrete membership: `(0,0)` and `(2,2)` lie in `[0,2]×[0,2]`, `(5,5)` does not. -/
example : pt 0 0 ∈ (KdTree.buildRoot sample).report (pt 0 0) (pt 2 2) := by
  rw [KdTree.mem_report_buildRoot_iff]
  constructor
  · simp [sample]
  · intro i; by_cases hi : i.val = 0 <;> simp [pt, hi]

example : pt 5 5 ∉ (KdTree.buildRoot sample).report (pt 0 0) (pt 2 2) := by
  rw [KdTree.mem_report_buildRoot_iff]
  rintro ⟨_, hbox⟩
  have h := (hbox 0).2
  simp [pt] at h

/-- The filtered concrete sample for a far-away box is empty (decidable check). -/
example : sample.filter (fun p => KdTree.inBox (pt 10 10) (pt 20 20) p) = [] := by
  decide

/-- A box disjoint from every point reports nothing (pruning boundary). -/
example : (KdTree.buildRoot sample).report (pt 10 10) (pt 20 20) = [] := by
  show (KdTree.build (Fin.ofNat 2 0) sample).report (pt 10 10) (pt 20 20) = []
  have hperm := KdTree.report_build_perm (Fin.ofNat 2 0) sample (pt 10 10) (pt 20 20)
  have hnil : sample.filter (fun p => KdTree.inBox (pt 10 10) (pt 20 20) p) = [] := by
    decide
  rw [hnil] at hperm
  exact List.length_eq_zero_iff.mp (by rw [hperm.length_eq]; rfl)

/-- The accumulator report agrees with filter-then-append. -/
example (acc : List (Fin 2 → Int)) :
    (KdTree.buildRoot sample).reportAux (pt 0 0) (pt 9 9) acc =
      (KdTree.buildRoot sample).toList.filter
        (fun p => KdTree.inBox (pt 0 0) (pt 9 9) p) ++ acc :=
  KdTree.reportAux_eq_filter_append (KdTree.valid_buildRoot sample) _ _ acc

example {t : KdTree 2} (h : t.Valid) (lo hi p : Fin 2 → Int) :
    p ∈ t.report lo hi ↔ p ∈ t.toList ∧ KdTree.inBox lo hi p :=
  KdTree.mem_report_iff h

#print axioms KdTree.report_eq_filter
#print axioms KdTree.reportAux_eq_filter_append
#print axioms KdTree.valid_build
#print axioms KdTree.mem_report_build_iff

end Cslib.Algorithms.Lean.KdTreeTests
