/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DlrSandwich

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.DlrSandwich`

On the triangle `⊤ : SimpleGraph (Fin 3)` at `p = 1/2`, `q = 2`, for the increasing event "the edge
`{0, 1}` is open":
* `bcProb_dlr_sandwich_top`: free `≤` boundary condition `C` `≤` fully wired, with `C` the single
  edge `{1, 2}`;
* `bcProb_dlr_sandwich` with the boundary `{1, 2}` wired: free `≤` `C` `≤` wired, for `C = ⊥`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.DlrSandwich

open _root_.StatMech _root_.StatMech.FK

/-- The event "the edge `{0, 1}` is open". -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 3))) := {ω | ω s(0, 1) = true}

/-- "The edge `{0, 1}` is open" is an increasing event. -/
theorem edgeOpen_isIncreasing : IsIncreasing edgeOpen := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- Free `≤` boundary condition `{1, 2}` `≤` fully wired.
example :
    (∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω * bcProb (⊤ : SimpleGraph (Fin 3)) ⊥ (1 / 2) 2 ω)
        ≤ ∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3)) (SimpleGraph.edge 1 2) (1 / 2) 2 ω
    ∧ (∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3)) (SimpleGraph.edge 1 2) (1 / 2) 2 ω)
        ≤ ∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3)) ⊤ (1 / 2) 2 ω :=
  bcProb_dlr_sandwich_top _ _ (by norm_num) (by norm_num) (by norm_num) edgeOpen_isIncreasing

-- The sandwich with the boundary `{1, 2}` wired and `C = ⊥`.
example :
    (∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω * bcProb (⊤ : SimpleGraph (Fin 3)) ⊥ (1 / 2) 2 ω)
        ≤ ∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3)) ⊥ (1 / 2) 2 ω
    ∧ (∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3)) ⊥ (1 / 2) 2 ω)
        ≤ ∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω
          * bcProb (⊤ : SimpleGraph (Fin 3))
            (Lattice.boundaryCliqueGraph (fun v : Fin 3 => v ≠ 0)) (1 / 2) 2 ω :=
  bcProb_dlr_sandwich _ (fun v : Fin 3 => v ≠ 0) ⊥ bot_le (by norm_num) (by norm_num)
    (by norm_num) edgeOpen_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.DlrSandwich
