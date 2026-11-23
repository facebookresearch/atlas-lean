/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Relation.FiniteReachability

/-!
# Bounded reachability in finite relations

For a decidable relation `r` on a finite type, `Relation.reachWithinFin r a k` is the finite set
of elements reachable from `a` in at most `k` `r`-steps. Each round adds the `r`-successors
(`Relation.postFin`, from `MathlibExt.Logic.Relation.FiniteReachability`) of the previous set,
which is computed once per round. An element lies in some round exactly when
`Relation.ReflTransGen r a` holds for it.

## Main results

* `Relation.mem_reachWithinFin_succ`: an element is in round `k + 1` exactly when it is in round
  `k` or is an `r`-successor of an element of round `k`.
* `Relation.exists_mem_reachWithinFin_iff`: an element lies in some round exactly when it is
  reachable from `a` in zero or more `r`-steps.
-/

@[expose] public section

namespace Relation

variable {α : Type*} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- The finite set of elements reachable from `a` in at most `k` `r`-steps: `{a}` after zero
rounds, and round `k + 1` adds to round `k` the `r`-successors of its elements. -/
def reachWithinFin (a : α) : ℕ → Finset α
  | 0 => {a}
  | k + 1 =>
      let previous := reachWithinFin a k
      previous ∪ postFin r previous

variable {r}

@[simp] theorem reachWithinFin_zero (a : α) : reachWithinFin r a 0 = {a} := rfl

/-- Round `k + 1` of `reachWithinFin` keeps round `k` and adds the `r`-successors of its
elements. -/
theorem mem_reachWithinFin_succ {a t : α} {k : ℕ} :
    t ∈ reachWithinFin r a (k + 1) ↔
      t ∈ reachWithinFin r a k ∨ ∃ z ∈ reachWithinFin r a k, r z t := by
  simp only [reachWithinFin, Finset.mem_union, mem_postFin]

private theorem reflTransGen_of_mem_reachWithinFin {a t : α} {k : ℕ}
    (h : t ∈ reachWithinFin r a k) : ReflTransGen r a t := by
  induction k generalizing t with
  | zero =>
      rw [reachWithinFin_zero, Finset.mem_singleton] at h
      subst h
      exact ReflTransGen.refl
  | succ k ih =>
      rcases mem_reachWithinFin_succ.mp h with h | ⟨z, hz, hzt⟩
      · exact ih h
      · exact (ih hz).tail hzt

private theorem exists_mem_reachWithinFin_of_reflTransGen {a t : α}
    (h : ReflTransGen r a t) : ∃ k, t ∈ reachWithinFin r a k := by
  induction h with
  | refl => exact ⟨0, by rw [reachWithinFin_zero, Finset.mem_singleton]⟩
  | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, mem_reachWithinFin_succ.mpr (Or.inr ⟨_, hk, hbc⟩)⟩

/-- An element lies in some round of `reachWithinFin r a` exactly when it is reachable from `a`
in zero or more `r`-steps. -/
theorem exists_mem_reachWithinFin_iff {a t : α} :
    (∃ k, t ∈ reachWithinFin r a k) ↔ ReflTransGen r a t :=
  ⟨fun ⟨_, hk⟩ => reflTransGen_of_mem_reachWithinFin hk,
    exists_mem_reachWithinFin_of_reflTransGen⟩

end Relation

end
