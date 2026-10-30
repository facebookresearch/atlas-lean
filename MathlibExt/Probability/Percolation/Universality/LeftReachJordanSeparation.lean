/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples

/-!
# Discrete Jordan separation for the left-reach set

Without an open horizontal crossing of `rect 0 n 0 n`, the left-reach set `bcd_leftReach ω n`
separates the left side from the right side: deleting its edge boundary disconnects them, every
lattice walk between them crosses the boundary an odd number of times, and its face-boundary graph
contains a cycle. Boundary edges with both endpoints in the square are closed.

These facts do not give the exhaustive half of the box-crossing dichotomy ("no horizontal
crossing implies a dual vertical crossing"): `jex_exhaustivity_of_barrier` assumes the dual
vertical crossing it concludes. The worked example
`bcc_wallCfg` on `rect 0 2 0 2` has no horizontal crossing, a separating left-reach set and a
face-boundary cycle, but no vertical crossing in the rotated dual `dualConfig` (`bcc_noV_wall`).

## Main results

* `StatMech.Universality.jex_barrier_edge_closed`: an in-square boundary edge of the left-reach
  set is closed.
* `StatMech.Universality.jex_edgeBoundary_nonempty`: without a horizontal crossing the left-reach
  set has nonempty edge boundary.
* `StatMech.Universality.jex_exists_dualCircuit`: without a horizontal crossing the face-boundary
  graph of the left-reach set contains a cycle.
-/

@[expose] public section

open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- A boundary edge of the left-reach set with both endpoints in the square is closed. -/
theorem jex_barrier_edge_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    ω s(p, q) = false := by
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈ bcd_leftReach ω n
  · exact bcd_leftReach_boundary_closed ω n hp hqbox hadj (hbd.mp hp)
  · have hq : q ∈ bcd_leftReach ω n := by
      by_contra hqn; exact hp (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    exact bcd_leftReach_boundary_closed ω n hq hpbox hadj.symm hp

/-- The quarter turn of an in-square boundary edge of the left-reach set is open in
`dualConfig ω`. -/
theorem jex_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q) (hbd : bdEdge (bcd_leftReach ω n) s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact jex_barrier_edge_closed ω n hadj hbd hpbox hqbox

/-- The row `y = c` gives a lattice path from `(0, c)` to `(m, c)`. -/
theorem jex_lattice_walk_row (c : ℤ) (m : ℕ) :
    (hypercubicLattice 2).Reachable (![0, c]) (![(m : ℤ), c]) := by
  have h := segment_connectedWithin (d := 2) (Set.univ) (0 : Fin 2) (![0, c]) m
    (fun t _ => Set.mem_univ _)
  have h2 : (hypercubicLattice 2).Reachable
      (Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (0 : ℤ)))
      (Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (m : ℤ))) := by
    obtain ⟨w⟩ := h
    exact ⟨w.map (Embedding.induce Set.univ).toHom⟩
  have e0 : Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (0 : ℤ)) = ![0, c] := by
    funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![0, c] : Site 2) 0 ((![0, c] : Site 2) 0 + (m : ℤ))
      = ![(m : ℤ), c] := by
    funext i; fin_cases i <;> simp [Function.update]
  rw [e0, em] at h2; exact h2

/-- Without a horizontal crossing (`n ≥ 0`), the left-reach set has nonempty edge boundary,
witnessed on any row `y = c` with `0 ≤ c ≤ n`. -/
theorem jex_edgeBoundary_nonempty (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    (edgeBoundary 2 (bcd_leftReach ω n)).Nonempty := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hxL : (![0, c] : Site 2) ∈ leftSide 0 (m : ℤ) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    refine ⟨by simp, ?_, by simpa using hc0, by simpa using hcn⟩
    simp only [Matrix.cons_val_zero]; exact hn
  have hyR : (![(m : ℤ), c] : Site 2) ∈ rightSide 0 (m : ℤ) 0 (m : ℤ) := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]
    refine ⟨?_, by simp, by simpa using hc0, by simpa using hcn⟩
    simp only [Matrix.cons_val_zero]; exact hn
  obtain ⟨w⟩ := jex_lattice_walk_row c m
  exact edgeBoundary_nonempty_of_walk (bcd_leftReach ω (m : ℤ)) w
    (dcw_leftSide_in_L ω (m : ℤ) hxL)
    (dcw_rightSide_notin_L ω (m : ℤ) hnoH hyR)

/-- Without a horizontal crossing (`n ≥ 0`), the face-boundary graph of the left-reach set
contains a cycle. The row parameter `c` is unused; `fdd_leftReach_dualCircuit` is the same
conclusion without it. -/
theorem jex_exists_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle := by
  obtain ⟨⟨a, b⟩, hab⟩ := jex_edgeBoundary_nonempty ω hn hnoH hc0 hcn
  exact exists_dualCircuit_of_finite_of_edgeBoundary (bcd_leftReach ω n)
    (bcd_leftReach_finite ω n) hab

/-- A face-boundary edge of the left-reach set whose separating edge `{p, q}` lies in the square
has its quarter turn open in `dualConfig ω`. -/
theorem jex_dualCircuit_edge_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (hadj : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    {p q : Site 2} (hpq : sharedPrimalEdge f g = s(p, q))
    (hpadj : (hypercubicLattice 2).Adj p q)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    dualConfig ω (crossEdge s(p, q)) = true := by
  have hbd : bdEdge (bcd_leftReach ω n) (sharedPrimalEdge f g) :=
    faceBoundaryGraph_sharedPrimalEdge_bdEdge _ hadj
  rw [hpq] at hbd
  exact jex_barrier_dual_open ω n hpadj hbd hpbox hqbox

/-- Trivial: given a dual vertical crossing, the disjunction holds by its right disjunct. This is
not the exhaustive half of the box-crossing dichotomy, whose content is producing the crossing
from `¬ HorizontalCrossing`. -/
theorem jex_exhaustivity_of_barrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : DualVerticalCrossing ω 0 n 0 n) :
    HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n :=
  Or.inr h

/-- For the wall configuration on `rect 0 2 0 2`, the left-reach set separates the left side from
the right side. -/
theorem jex_wall_separates {x y : Site 2}
    (hx : x ∈ leftSide 0 2 0 2) (hy : y ∈ rightSide 0 2 0 2) :
    ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y :=
  dcw_barrier_separates bcc_wallCfg 2 bcc_noH_wall hx hy

/-- For the wall configuration on `rect 0 2 0 2`, the face-boundary graph of the left-reach set
contains a cycle. -/
theorem jex_wall_dualCircuit :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Walk u u),
      cyc.IsCycle :=
  jex_exists_dualCircuit bcc_wallCfg (by norm_num) bcc_noH_wall (c := 0) (by norm_num)
    (by norm_num)

end Universality

end StatMech
