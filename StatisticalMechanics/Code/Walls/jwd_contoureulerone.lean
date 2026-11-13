/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Lattice.Cyclomatic
import Code.Lattice.EulerFaces2
import Code.Lattice.JordanEulerSeparation
import Code.Lattice.GaussBonnet

open SimpleGraph

namespace StatMech.Walls

open StatMech.Lattice











noncomputable def contourEulerChar (p : ℕ) : ℕ := by
  classical
  exact if 3 ≤ p then cyclomaticNumber (cycleGraph p) else 0


















theorem jwd_cyclomaticNumber_eq_boundedRegionCount {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : G.Connected) :
    cyclomaticNumber G = jes_boundedRegionCount G := by
  unfold cyclomaticNumber jes_boundedRegionCount nullity
  have hc : Nat.card G.ConnectedComponent = 1 := card_components_eq_one_of_connected hG
  have he : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [hc, he, Nat.card_eq_fintype_card]







theorem jwd_cycleGraph_edgeSet_ncard (n : ℕ) :
    (cycleGraph (n + 3)).edgeSet.ncard = n + 3 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset, cycleGraph_card_edges]















theorem jwd_cycleGraph_boundedRegionCount_one (n : ℕ) :
    jes_boundedRegionCount (cycleGraph (n + 3)) = 1 := by
  apply jes_nullity_one_boundedRegionCount_one
  unfold nullity
  have hc : Nat.card (cycleGraph (n + 3)).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected cycleGraph_connected
  rw [hc, jwd_cycleGraph_edgeSet_ncard]
  simp [Nat.card_eq_fintype_card]












theorem jwd_cycleGraph_cyclomaticNumber_eq_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  rw [jwd_cyclomaticNumber_eq_boundedRegionCount cycleGraph_connected,
    jwd_cycleGraph_boundedRegionCount_one]
















theorem contourEulerChar_eq_one {p : ℕ} (hp : 3 ≤ p) : contourEulerChar p = 1 := by
  unfold contourEulerChar
  rw [if_pos hp]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  exact jwd_cycleGraph_cyclomaticNumber_eq_one n







theorem contourEulerChar_eq_lattice (p : ℕ) :
    contourEulerChar p = StatMech.Lattice.contourEulerChar p := by
  unfold contourEulerChar StatMech.Lattice.contourEulerChar
  by_cases hp : 3 ≤ p
  · rw [if_pos hp, dif_pos hp]
  · rw [if_neg hp, dif_neg hp]

end StatMech.Walls
