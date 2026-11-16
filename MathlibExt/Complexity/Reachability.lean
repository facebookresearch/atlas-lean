/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation

/-!
# Iterated reachability

Vertices reachable within `k` directed steps, iterated.
Some iterate contains a vertex exactly when a directed
path joins them. Configuration counting is not included
here.
-/

@[expose] public section

/-- Iterated reachability in a finite directed graph
(MOD-40 core). `reachFrom adj s k` is the set of vertices
reachable from `s` in at most `k` steps along `adj`. -/
def reachFrom {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) :
    ℕ → Finset (Fin n)
  | 0 => {s}
  | k + 1 => reachFrom adj s k ∪
      Finset.filter (fun t => ∃ u ∈ reachFrom adj s k, adj u t) Finset.univ

private theorem reachFrom_zero {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) :
    reachFrom adj s 0 = {s} := rfl

private theorem reachFrom_succ {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n)
    (k : ℕ) :
    reachFrom adj s (k + 1) = reachFrom adj s k ∪
      Finset.filter (fun t => ∃ u ∈ reachFrom adj s k, adj u t) Finset.univ := rfl

private theorem reachFrom_mem_of_mem {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s : Fin n) (k : ℕ) (t : Fin n) (h : t ∈ reachFrom adj s k) :
    Relation.ReflTransGen (fun a b => adj a b = true) s t := by
  induction k generalizing t with
  | zero =>
      rw [reachFrom_zero, Finset.mem_singleton] at h
      subst h
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      rw [reachFrom_succ, Finset.mem_union] at h
      rcases h with h | h
      · exact ih t h
      · rw [Finset.mem_filter] at h
        obtain ⟨-, u, hu, hadj⟩ := h
        exact Relation.ReflTransGen.tail (ih u hu) hadj

private theorem mem_of_reachFrom {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s t : Fin n)
    (h : Relation.ReflTransGen (fun a b => adj a b = true) s t) :
    ∃ k, t ∈ reachFrom adj s k := by
  induction h with
  | refl => exact ⟨0, by rw [reachFrom_zero, Finset.mem_singleton]⟩
  | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [reachFrom_succ, Finset.mem_union]
      right
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, _, hk, hstep⟩

/-- Iterated reachability is reachability: some iterate
contains exactly the vertices joined to `s` by a directed
path. Configuration-graph search in polynomial space and
time is downstream. -/
theorem mem_reachFrom_iff {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s t : Fin n) :
    (∃ k, t ∈ reachFrom adj s k)
      ↔ Relation.ReflTransGen (fun a b => adj a b = true) s t := by
  constructor
  · rintro ⟨k, hk⟩
    exact reachFrom_mem_of_mem adj s k t hk
  · intro h
    exact mem_of_reachFrom adj s t h

end
