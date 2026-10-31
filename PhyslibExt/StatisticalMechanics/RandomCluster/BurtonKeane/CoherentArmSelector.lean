/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif

/-!
# Coherent arm selectors

A trifurcation has a private branch avoiding any other trifurcation; coherent arm selection is the
private-arm condition `daepf_PrivateArm`, which gives the trifurcation count.

## i. Overview

The three branches of a trifurcation `x` are disconnected after `x` is removed, so another site
meets at most one of them and two branches avoid it: `x` has a private branch avoiding any given
other trifurcation. Open walks avoiding `x` survive removal of `x`. The coherent selector condition
`daepf_PrivateArm ω n` (PrivateArmTwoTrif) asks for arm ends `b x` with infinite clusters outside
the trifurcation set, such that for connected trifurcations `x ≠ y`, `b x` is cut from `y` by
removing `x` while `b y` still reaches `y`. It gives the count bound; PrivateArmTwoTrif proves that
it holds with no trifurcation, one trifurcation, or two trifurcations with local ends.

The configuration-wide form of this condition, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`pap_not_forall_coherentSelector`). The Burton–Keane theorem that assumed it was removed as
vacuous.

## ii. Key results

- `pap_exists_private_branch` : a private branch at each trifurcation.

## iii. Table of contents

- A. Private branches
- B. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Private branches -/

lemma pap_exists_private_branch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (_ha3box : a₃ ∈ box d n)
    (hc1 : Connected d ω x a₁) (hc2 : Connected d ω x a₂) (_hc3 : Connected d ω x a₃)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (_hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ∃ a, a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSite x ω) a).Infinite ∧
      ¬ Connected d (removeSite x ω) a v := by
  rcases daep2_two_branches_avoid ω hd12 hd13 hd23 v with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₂, ha2box, hc2, hi2, h2⟩

lemma pap_adj_removeSite_of_avoid (ω : ConfigSpace (Sym2 (Site d))) {x u w : Site d}
    (hu : u ≠ x) (hw : w ≠ x) (hadj : (openSubgraph d ω).Adj u w) :
    (openSubgraph d (removeSite x ω)).Adj u w := by
  rw [openSubgraph_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  have hxnot : x ∉ s(u, w) := by
    rw [Sym2.mem_iff, not_or]; exact ⟨fun h => hu h.symm, fun h => hw h.symm⟩
  rw [removeSite_apply_of_notMem hxnot]; exact hadj.2

lemma pap_connected_removeSite_of_walk_avoid (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {u w : Site d} (p : (openSubgraph d ω).Walk u w) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) u w := by
  induction p with
  | nil => exact connected_rfl
  | @cons a b c hadj p' ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hx
    obtain ⟨hxa, hxrest⟩ := hx
    have hxb : x ≠ b := fun h => hxrest (h ▸ p'.start_mem_support)
    have hstep : (openSubgraph d (removeSite x ω)).Adj a b :=
      pap_adj_removeSite_of_avoid ω (Ne.symm hxa) (Ne.symm hxb) hadj
    exact (SimpleGraph.Adj.reachable hstep).trans (ih hxrest)

lemma pap_far_of_avoiding_path (ω : ConfigSpace (Sym2 (Site d))) {x y by_ : Site d}
    (p : (openSubgraph d ω).Walk by_ y) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) by_ y :=
  pap_connected_removeSite_of_walk_avoid ω x p hx

/-! ## B. Unsatisfiability of the configuration-wide conditions -/

/-- `daepf_PrivateArm` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma pap_not_forall_coherentSelector (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daepf_PrivateArm ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    daepf_Tcount_le_boundary_of_privateArm ω n hn (h ω n hn)

end Percolation

end StatMech
