/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation

/-!
# Iterated reachability

For a finite directed graph on `Fin n` with edges `adj u t = true`, `reachFrom adj s k` is the
set of vertices reachable from `s` in at most `k` steps. Each round adds the out-neighbours of
the previous iterate, which is computed once per round.

## Main results

* `mem_reachFrom_succ`: a vertex is in iterate `k + 1` exactly when it is in iterate `k` or is
  an out-neighbour of a vertex of iterate `k`.
* `exists_mem_reachFrom_iff`: a vertex lies in some iterate exactly when the
  reflexive-transitive closure of the edge relation joins `s` to it.
-/

@[expose] public section

namespace MathlibExt.Complexity.Reachability

/-- Vertices reachable from `s` in at most `k` steps along `adj`: iterate `0` is `{s}`, and
iterate `k + 1` adds to iterate `k` the out-neighbours of its vertices. -/
def reachFrom {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) :
    ℕ → Finset (Fin n)
  | 0 => {s}
  | k + 1 =>
      let previous := reachFrom adj s k
      previous ∪ previous.biUnion fun u => Finset.univ.filter fun t => adj u t

@[simp] theorem reachFrom_zero {n : ℕ} (adj : Fin n → Fin n → Bool) (s : Fin n) :
    reachFrom adj s 0 = {s} := rfl

/-- One round of `reachFrom` keeps the previous iterate and adds its out-neighbours. -/
theorem mem_reachFrom_succ {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) (k : ℕ) :
    t ∈ reachFrom adj s (k + 1) ↔
      t ∈ reachFrom adj s k ∨ ∃ u ∈ reachFrom adj s k, adj u t = true := by
  simp only [reachFrom, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]

private theorem reflTransGen_of_mem_reachFrom {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s : Fin n) (k : ℕ) (t : Fin n) (h : t ∈ reachFrom adj s k) :
    Relation.ReflTransGen (fun a b => adj a b = true) s t := by
  induction k generalizing t with
  | zero =>
      rw [reachFrom_zero, Finset.mem_singleton] at h
      subst h
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      rcases (mem_reachFrom_succ adj s t k).mp h with h | ⟨u, hu, hadj⟩
      · exact ih t h
      · exact Relation.ReflTransGen.tail (ih u hu) hadj

private theorem exists_mem_reachFrom_of_reflTransGen {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s t : Fin n)
    (h : Relation.ReflTransGen (fun a b => adj a b = true) s t) :
    ∃ k, t ∈ reachFrom adj s k := by
  induction h with
  | refl => exact ⟨0, by rw [reachFrom_zero, Finset.mem_singleton]⟩
  | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, (mem_reachFrom_succ adj s _ k).mpr (Or.inr ⟨_, hk, hstep⟩)⟩

/-- A vertex lies in some iterate of `reachFrom adj s` exactly when the reflexive-transitive
closure of the edge relation joins `s` to it. -/
theorem exists_mem_reachFrom_iff {n : ℕ} (adj : Fin n → Fin n → Bool)
    (s t : Fin n) :
    (∃ k, t ∈ reachFrom adj s k)
      ↔ Relation.ReflTransGen (fun a b => adj a b = true) s t := by
  constructor
  · rintro ⟨k, hk⟩
    exact reflTransGen_of_mem_reachFrom adj s k t hk
  · intro h
    exact exists_mem_reachFrom_of_reflTransGen adj s t h

end MathlibExt.Complexity.Reachability

end
