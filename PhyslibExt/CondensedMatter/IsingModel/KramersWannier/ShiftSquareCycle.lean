/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip

/-!
# A unit-square cycle refuting the inside-region matching

The boundary of the unit cell `[0, 1] × [1, 2]`, traversed once, is a closed walk without repeated
edges whose edge set is not the boundary-edge set of its inside region `jec_leftRegion`.

## i. Overview

For the loop `ceo_shiftSquare` (from `(0, 1)` through `(1, 1)`, `(1, 2)`, `(0, 2)`), the edge
`(0, 1)`–`(1, 1)` is an edge of the loop. Both endpoints have ray count `0`, so the edge is not a
boundary edge of the inside region, and its crossing edge `rpc_crossEdge` is not traversed. This
refutes both `rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare` and `kwc_PrimalWalkLeftRegionMatch`.

All results here are unconditional. The two refutations are used to document the vacuity of
results in `DualWalkToPrimalWalk`, `BridgeGap`, `RayCrossFlip` and `CrossEdgeMatchingForms`.

## ii. Key results

- `StatMech.Walls.ceo_shiftSquare` : the unit-square loop at `(0, 1)`
- `StatMech.Walls.ceo_shiftSquare_residue_false` : refutation of `rpc_CrossEdgeOddIffOnWalk`
- `StatMech.Walls.ceo_primalWalkLeftRegionMatch_false` : refutation of
  `kwc_PrimalWalkLeftRegionMatch`

## iii. Table of contents

- A. The loop and its crossing edge
- B. Ray counts and the refutations

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open Set SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Walls
open StatMech.Lattice

/-! ## A. The loop and its crossing edge -/

/-- The boundary of the unit cell `[0, 1] × [1, 2]` as a closed lattice walk based at `(0, 1)`. -/
noncomputable def ceo_shiftSquare : (hypercubicLattice 2).Walk ![0, 1] ![0, 1] :=
  let s1 : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
    (jec_hsegRight 1 0 1).copy (by ext i; fin_cases i <;> simp) (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![1, 1] ![1, 2] :=
    (jec_vsegUp 1 1 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![1, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 1).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![0, 2] ![0, 1] :=
    ((jec_vsegUp 0 1 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append s4))

/-- The loop has no repeated edges. -/
lemma ceo_shiftSquare_edges_nodup : ceo_shiftSquare.edges.Nodup := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

/-- `(0, 1)` and `(1, 1)` are adjacent. -/
lemma ceo_uv_adj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

/-- The edge `(0, 1)`–`(1, 1)` is an edge of the loop. -/
lemma ceo_shiftSquare_edge_mem :
    s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

/-- The loop does not traverse the crossing edge of `(0, 1)`–`(1, 1)`. -/
lemma ceo_shiftSquare_crossEdge_count_zero :
    ceo_shiftSquare.edges.count (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2)) = 0 := by
  have hce : rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2)
      = rpc_hCrossEdge (![0, 1] : Site 2) := by
    rw [rpc_crossEdge]; rw [ite_eq_left]; simp
  rw [hce, rpc_hCrossEdge]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp, List.count]

/-- `rpc_CrossEdgeOddIffOnWalk` fails for the loop. -/
theorem ceo_shiftSquare_residue_false : ¬ rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare := by
  intro h
  have hodd := (h ceo_uv_adj).mpr ceo_shiftSquare_edge_mem
  rw [ceo_shiftSquare_crossEdge_count_zero] at hodd
  exact (Nat.not_odd_iff_even.mpr (by decide)) hodd

/-! ## B. Ray counts and the refutations -/

/-- Both endpoints of the edge `(0, 1)`–`(1, 1)` have ray count `0`. -/
lemma ceo_shiftSquare_rayCount_endpoints :
    jec_rayCount (![0, 1] : Site 2) ceo_shiftSquare = 0 ∧
      jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0 := by
  constructor <;>
    · unfold ceo_shiftSquare
      simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
        jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      norm_num

/-- The site `(1, 2)` has ray count `1`. -/
lemma ceo_shiftSquare_inside_odd :
    jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 := by
  unfold ceo_shiftSquare
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num

/-- The loop edge `(0, 1)`–`(1, 1)` is not a boundary edge of the inside region. -/
lemma ceo_shiftSquare_not_bdEdge :
    ¬ bdEdge (jec_leftRegion ceo_shiftSquare) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  obtain ⟨h01, h11⟩ := ceo_shiftSquare_rayCount_endpoints
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion, h01, h11]
  simp

/-- `kwc_PrimalWalkLeftRegionMatch` is false: the loop `ceo_shiftSquare` is a counterexample. -/
theorem ceo_primalWalkLeftRegionMatch_false : ¬ kwc_PrimalWalkLeftRegionMatch := by
  intro h
  have := (h ceo_shiftSquare ceo_uv_adj).mp (List.mem_toFinset.mpr ceo_shiftSquare_edge_mem)
  exact ceo_shiftSquare_not_bdEdge this

end Walls
end StatMech
