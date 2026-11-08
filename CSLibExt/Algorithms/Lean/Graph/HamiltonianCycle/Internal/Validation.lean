/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
import Init.Data.Array.Lemmas
import Init.Data.Array.Find
import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Private graph validation refinement

This implementation's diagonal and symmetry validation reads the actual
row-major graph input. CLRS does not specify these encoding-validation steps.
These lemmas refine that same short-circuit computation.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

lemma ret_findSomeM {α β : Type} (f : α → TimeM Nat (Option β)) (xs : Array α) :
    (xs.findSomeM? f).ret = xs.findSome? (fun a => (f a).ret) := by
  rw [← Array.findSomeM?_toList, ← Array.findSome?_toList]
  have h := Cslib.IsMonadHom.map_listFindSomeM?
    (TimeM.isMonadHom_pure_ret (T := Nat)) f xs.toList
  simpa [Function.comp_def] using congrArg Id.run h

lemma verifyHamiltonianCycle_of_nonsquare (x y : Array Bool)
    (h : Nat.sqrt x.size * Nat.sqrt x.size ≠ x.size) :
    verifyHamiltonianCycle x y = ⟨false, 1⟩ := by
  simp [verifyHamiltonianCycle, validateGraph, h]
  rfl

lemma validateGraph_ret_iff (x : Array Bool) (m : Nat) :
    (validateGraph x m).ret = true ↔
      m * m = x.size ∧
      (∀ i : Fin m, x[i.val * m + i.val]?.getD false = false) ∧
      (∀ i j : Fin m, i.val < j.val →
        x[i.val * m + j.val]?.getD false = x[j.val * m + i.val]?.getD false) := by
  by_cases h : m * m = x.size
  · simp only [validateGraph, h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      graphRead, bind_pure_comp, bind_map_left, bne_iff_ne, ne_eq, ite_not,
      Option.not_isSome, TimeM.ret_bind, ret_findSomeM, TimeM.ret_map,
      Array.findSome?_isSome_iff, Array.mem_ofFn, ↓existsAndEq, Option.isSome_ite,
      true_and]
    split_ifs
    · simp_all only [TimeM.ret_pure, Bool.false_eq_true, false_iff, not_and,
        not_forall, isEmpty_Prop, Bool.not_eq_false, IsEmpty.forall_iff]
    · simp_all only [not_exists, Bool.not_eq_true, TimeM.ret_map, ret_findSomeM,
        Option.isNone_iff_eq_none, Array.findSome?_eq_none_iff, Array.mem_ofFn,
        ↓existsAndEq, forall_const, implies_true, true_and]
      constructor
      · intro hs i j hij
        simpa [hij] using hs i j
      · intro hs i j
        by_cases hij : i.val < j.val
        · simp [hij, hs i j hij]
        · simp [hij]
  · simp [validateGraph, h]

lemma row_major_lt (m i j : Nat) (hi : i < m) (hj : j < m) : i * m + j < m * m := by
  calc
    i * m + j < i * m + m := Nat.add_lt_add_left hj _
    _ = (i + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ m * m := Nat.mul_le_mul_right m hi

lemma graph_read_some (x : Array Bool) (index : Nat) (h : index < x.size) :
    x[index]? = some (x[index]?.getD false) := by
  simp [h]

lemma validateGraph_ret_iff_all (x : Array Bool) (m : Nat) :
    (validateGraph x m).ret = true ↔ m * m = x.size ∧
      (∀ i : Fin m, x[i.val * m + i.val]?.getD false = false) ∧
      (∀ i j : Fin m,
        x[i.val * m + j.val]?.getD false = x[j.val * m + i.val]?.getD false) := by
  rw [validateGraph_ret_iff]
  constructor
  · rintro ⟨hs, hd, he⟩
    refine ⟨hs, hd, fun i j => ?_⟩
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact he i j hij
    · have hij' : i = j := Fin.ext hij
      subst j
      rfl
    · exact (he j i hij).symm
  · rintro ⟨hs, hd, he⟩
    exact ⟨hs, hd, fun i j _ => he i j⟩

lemma validateGraph_iff (x : Array Bool) (m : Nat) :
    (validateGraph x m).ret = true ↔ m * m = x.size ∧
      (∀ i : Fin m, x[i.val * m + i.val]? = some false) ∧
      (∀ i j : Fin m, x[i.val * m + j.val]? = x[j.val * m + i.val]?) := by
  rw [validateGraph_ret_iff_all]
  by_cases hs : m * m = x.size
  · simp only [hs, true_and]
    have hb (i j : Fin m) : i.val * m + j.val < x.size := by
      rw [← hs]
      exact row_major_lt m i.val j.val i.isLt j.isLt
    constructor
    · rintro ⟨hd, he⟩
      constructor
      · intro i
        have hr := graph_read_some x _ (hb i i)
        rwa [hd i] at hr
      · intro i j
        rw [graph_read_some x _ (hb i j), graph_read_some x _ (hb j i), he i j]
    · rintro ⟨hd, he⟩
      constructor
      · intro i
        simp [hd i]
      · intro i j
        exact congrArg (fun p : Option Bool => p.getD false) (he i j)
  · simp [hs]

end Cslib.Algorithms.Lean.Graph
