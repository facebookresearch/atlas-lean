/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Sparse characteristic-two row reduction preserves literal source-module relations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalModule
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A sparse source row denotes the sum of its literal generator images. -/
def monsterCo1GeometryVectorRowEval {α V : Type*} [AddCommGroup V]
    (point : α → V) (row : List α) : V := (row.map point).sum

/-- Duplicate indices cancel in a sparse characteristic-two row. -/
def monsterCo1GeometryVectorRowNormalize {α : Type*} [DecidableEq α] : List α → Finset α
  | [] => ∅
  | a :: row =>
      let s := monsterCo1GeometryVectorRowNormalize row
      if a ∈ s then s.erase a else insert a s

/-- A binary-module vector added to itself is zero. -/
theorem monsterCo1GeometryVector_add_self {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (v : V) : v + v = 0 := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  rw [← one_smul (ZMod 2) v, ← add_smul, h, zero_smul]

/-- Sparse duplicate cancellation preserves the evaluated source row. -/
theorem monsterCo1GeometryVectorRowNormalize_eval {α V : Type*} [DecidableEq α]
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V) (row : List α) :
    (∑ a ∈ monsterCo1GeometryVectorRowNormalize row, point a) =
      monsterCo1GeometryVectorRowEval point row := by
  induction row with
  | nil => simp [monsterCo1GeometryVectorRowNormalize, monsterCo1GeometryVectorRowEval]
  | cons a row ih =>
      simp only [monsterCo1GeometryVectorRowNormalize]
      split_ifs with ha
      · have hs := Finset.add_sum_erase _ point ha
        have hc := monsterCo1GeometryVector_add_self (point a)
        simp only [monsterCo1GeometryVectorRowEval, List.map_cons, List.sum_cons] at ih ⊢
        rw [← ih, ← hs, ← add_assoc, hc, zero_add]
      · rw [Finset.sum_insert ha, ih]
        rfl

/-- An empty checked normal form implies the literal source row evaluates to zero. -/
theorem monsterCo1GeometryVectorRowEval_zero_of_normalize {α V : Type*} [DecidableEq α]
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V) (row : List α)
    (h : monsterCo1GeometryVectorRowNormalize row = ∅) :
    monsterCo1GeometryVectorRowEval point row = 0 := by
  rw [← monsterCo1GeometryVectorRowNormalize_eval, h, Finset.sum_empty]

/-- Flattening any finite list of proved source rows gives a proved zero row. -/
theorem monsterCo1GeometryVectorRowEval_flatten_zero {α V : Type*} [AddCommGroup V]
    (point : α → V) (rows : List (List α))
    (h : ∀ row ∈ rows, monsterCo1GeometryVectorRowEval point row = 0) :
    monsterCo1GeometryVectorRowEval point rows.flatten = 0 := by
  induction rows with
  | nil => simp [monsterCo1GeometryVectorRowEval]
  | cons row rows ih =>
      have hr := h row (List.mem_cons_self ..)
      have ht := ih (fun r hh => h r (List.mem_cons_of_mem _ hh))
      change (List.map point (row ++ rows.flatten)).sum = 0
      rw [List.map_append, List.sum_append]
      change monsterCo1GeometryVectorRowEval point row +
        monsterCo1GeometryVectorRowEval point rows.flatten = 0
      rw [hr, ht, zero_add]

/-- A checked sparse cancellation certificate derives a source relation solely from the stated
prior proved relations. -/
theorem monsterCo1GeometryVectorRowEval_zero_of_prior {α V : Type*} [DecidableEq α]
    [AddCommGroup V] [Module (ZMod 2) V] (point : α → V) (rows : List (List α))
    (prior : ∀ row ∈ rows, monsterCo1GeometryVectorRowEval point row = 0)
    (target : List α)
    (check : monsterCo1GeometryVectorRowNormalize (rows.flatten ++ target) = ∅) :
    monsterCo1GeometryVectorRowEval point target = 0 := by
  have h := monsterCo1GeometryVectorRowEval_zero_of_normalize point _ check
  have hp := monsterCo1GeometryVectorRowEval_flatten_zero point rows prior
  change (List.map point (rows.flatten ++ target)).sum = 0 at h
  rw [List.map_append, List.sum_append] at h
  change monsterCo1GeometryVectorRowEval point rows.flatten +
    monsterCo1GeometryVectorRowEval point target = 0 at h
  rw [hp, zero_add] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
