/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The selection step of a Luby MIS round

In each round of Luby's maximal independent set algorithm every active vertex draws a
random priority, and the active vertices whose priority is smaller than that of every
active neighbor join the independent set. This file treats that selection step on a simple
graph `G` on `Fin n` for given priorities `prio : Fin n → ℕ`, with ties between equal
priorities broken by vertex index: vertices are compared by the key
`lubyKey prio v = prio v * n + v`.

## Main results

* `Cslib.Distributed.LubyMIS.lubyKey_lt_iff`: keys compare priorities first and then vertex
  indices.
* `Cslib.Distributed.LubyMIS.lubySelect`: the active vertices whose key is smaller than the
  key of every active neighbor.
* `Cslib.Distributed.LubyMIS.lubySelect_subset`: selected vertices are active.
* `Cslib.Distributed.LubyMIS.lubySelect_isIndepSet`: the selected set is an independent set
  of `G`.

Randomness, the removal of selected vertices and their neighbors, maximality of the final
set, and the expected number of rounds are not covered.

## References

* M. Luby, *A simple parallel algorithm for the maximal independent set problem*, SIAM
  Journal on Computing 15(4), 1986.
-/

@[expose] public section

namespace Cslib.Distributed.LubyMIS

variable {n : ℕ}

/-- The key of vertex `v`: its priority, with the vertex index as tie-breaker. Keys compare
lexicographically by `(prio v, v)` (`lubyKey_lt_iff`). -/
def lubyKey (prio : Fin n → ℕ) (v : Fin n) : ℕ :=
  prio v * n + v.val

/-- Keys compare priorities first and break ties between equal priorities by vertex
index. -/
theorem lubyKey_lt_iff (prio : Fin n → ℕ) (v u : Fin n) :
    lubyKey prio v < lubyKey prio u ↔ prio v < prio u ∨ (prio v = prio u ∧ v < u) := by
  unfold lubyKey
  rw [Fin.lt_def]
  have hv := v.isLt
  have hu := u.isLt
  constructor
  · intro h
    rcases lt_trichotomy (prio v) (prio u) with hlt | heq | hgt
    · exact Or.inl hlt
    · rw [heq] at h
      exact Or.inr ⟨heq, by omega⟩
    · have hle : (prio u + 1) * n ≤ prio v * n := Nat.mul_le_mul_right n hgt
      rw [Nat.add_mul, one_mul] at hle
      omega
  · rintro (hlt | ⟨heq, hlt⟩)
    · have hle : (prio v + 1) * n ≤ prio u * n := Nat.mul_le_mul_right n hlt
      rw [Nat.add_mul, one_mul] at hle
      omega
    · rw [heq]
      omega

/-- The selection step of one Luby round on `G`: the active vertices whose key is smaller
than the key of every active neighbor. -/
def lubySelect (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (prio : Fin n → ℕ)
    (active : Finset (Fin n)) : Finset (Fin n) :=
  active.filter (fun v => ∀ u ∈ G.neighborFinset v ∩ active,
    lubyKey prio v < lubyKey prio u)

/-- Selected vertices are active. -/
theorem lubySelect_subset (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (prio : Fin n → ℕ) (active : Finset (Fin n)) :
    lubySelect G prio active ⊆ active :=
  Finset.filter_subset _ _

/-- The selected set is an independent set of `G`: two adjacent selected vertices would
each have the smaller key. -/
theorem lubySelect_isIndepSet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (prio : Fin n → ℕ) (active : Finset (Fin n)) :
    G.IsIndepSet (lubySelect G prio active : Set (Fin n)) := by
  intro v hv u hu _ hadj
  simp only [lubySelect, Finset.coe_filter, Set.mem_ofPred_eq] at hv hu
  have h1 : lubyKey prio v < lubyKey prio u :=
    hv.2 u (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr hadj, hu.1⟩)
  have h2 : lubyKey prio u < lubyKey prio v :=
    hu.2 v (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr hadj.symm, hv.1⟩)
  exact lt_asymm h1 h2

end Cslib.Distributed.LubyMIS
