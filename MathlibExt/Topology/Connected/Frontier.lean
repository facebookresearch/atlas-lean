/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Connected.Basic

/-!
# Frontier-crossing lemma

ATLAS N385 prerequisite: a preconnected set meeting both a set and its
complement meets its frontier.
Source: ATLAS revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, file
`v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean`, lines 466--500, where
source `preconnected_frontier_inter` becomes public theorem
`IsPreconnected.inter_frontier_nonempty_of_inter_compl`.
Source-to-API map: source `preconnected_frontier_inter` maps to target
`IsPreconnected.inter_frontier_nonempty_of_inter_compl`.
This file is a supporting prerequisite stage and not the full N385 target.
-/

@[expose] public section

open Set Topology

variable {α : Type*} [TopologicalSpace α]

/-- **A preconnected set meets the frontier of every set it crosses.** Let $s$ be a
preconnected subset of a topological space $X$ and let $A \subseteq X$. If both $s \cap A$ and
$s \cap (X \setminus A)$ are nonempty, then $s$ meets the frontier
$\partial A = \overline{A} \setminus \operatorname{int} A$ of $A$, that is,
$s \cap \partial A$ is nonempty. -/
theorem IsPreconnected.inter_frontier_nonempty_of_inter_compl {s : Set α}
    (hs : IsPreconnected s) {A : Set α} (hA : (s ∩ A).Nonempty)
    (hAc : (s ∩ Aᶜ).Nonempty) : (s ∩ frontier A).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : s ⊆ interior A ∪ interior Aᶜ := by
    intro x hx
    by_contra hx_not
    rw [Set.mem_union] at hx_not
    push Not at hx_not
    have hfr : x ∈ frontier A := by
      simp only [frontier, Set.mem_sdiff]
      refine ⟨?_, hx_not.1⟩
      rw [mem_closure_iff]
      intro U hU hxU
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hx_not.2
      apply interior_maximal _ hU hxU
      intro y hy
      simp only [Set.mem_compl_iff]
      intro hyA
      exact absurd (show y ∈ U ∩ A from ⟨hy, hyA⟩) (by rw [hemp]; exact notMem_empty y)
    have : x ∈ s ∩ frontier A := ⟨hx, hfr⟩
    rw [hempty] at this
    exact notMem_empty x this
  have h1 : (s ∩ interior A).Nonempty := by
    obtain ⟨x, hxs, hxA⟩ := hA
    rcases hsub hxs with h | h
    · exact ⟨x, hxs, h⟩
    · exact absurd hxA (interior_subset h)
  have h2 : (s ∩ interior Aᶜ).Nonempty := by
    obtain ⟨x, hxs, hxAc⟩ := hAc
    rcases hsub hxs with h | h
    · exact absurd (interior_subset h) hxAc
    · exact ⟨x, hxs, h⟩
  obtain ⟨x, _, hx1, hx2⟩ := hs _ _ isOpen_interior isOpen_interior hsub h1 h2
  exact interior_subset hx2 (interior_subset hx1)

end
