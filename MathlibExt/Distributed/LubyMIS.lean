/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert

/-!
# Luby MIS round

One round of Luby's randomized maximal independent set
algorithm: active vertices whose `(priority, id)` key is
strictly smallest among active neighbors are selected.
The selected set is independent. The expected-rounds
analysis is not included here.
-/

@[expose] public section

/-- Lexicographic `(priority, id)` key as a single natural:
`key v < key u` iff `prio v < prio u`, or equal priorities
and `v < u` (since `v.val < n`). -/
def lubyKey {n : ℕ} (prio : Fin n → ℕ) (v : Fin n) : ℕ :=
  prio v * n + v.val

/-- One Luby MIS round (core of DPA-23): among active
vertices, select those whose key is strictly smallest among
active neighbors. `adj` is the adjacency finset function of
an undirected graph given abstractly. -/
def lubySelect {n : ℕ} (prio : Fin n → ℕ) (adj : Fin n → Finset (Fin n))
    (active : Finset (Fin n)) : Finset (Fin n) :=
  active.filter (fun v => ∀ u ∈ adj v ∩ active,
    lubyKey prio v < lubyKey prio u)

/-- The selected set is independent: no two selected vertices
are adjacent (with respect to symmetric adjacency recorded
in `adj`; the hypothesis says adjacency is symmetric). -/
theorem lubySelect_independent {n : ℕ} (prio : Fin n → ℕ)
    (adj : Fin n → Finset (Fin n))
    (hadj : ∀ v u, u ∈ adj v → v ∈ adj u)
    (active : Finset (Fin n)) :
    ∀ v ∈ lubySelect prio adj active, ∀ u ∈ lubySelect prio adj active,
      u ∉ adj v := by
  intro v hv u hu huv
  simp only [lubySelect, Finset.mem_filter] at hv hu
  obtain ⟨hvActive, hvMin⟩ := hv
  obtain ⟨huActive, huMin⟩ := hu
  have hvu : u ∈ adj v ∩ active := Finset.mem_inter.mpr ⟨huv, huActive⟩
  have h1 : lubyKey prio v < lubyKey prio u := hvMin u hvu
  have hvu' : v ∈ adj u ∩ active :=
    Finset.mem_inter.mpr ⟨hadj v u huv, hvActive⟩
  have h2 : lubyKey prio u < lubyKey prio v := huMin v hvu'
  exact lt_asymm h1 h2

/-- Selected vertices are active. -/
theorem lubySelect_subset {n : ℕ} (prio : Fin n → ℕ)
    (adj : Fin n → Finset (Fin n)) (active : Finset (Fin n)) :
    lubySelect prio adj active ⊆ active := by
  unfold lubySelect
  exact Finset.filter_subset _ _

end
