/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
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

A trifurcation has a private branch avoiding any other trifurcation; coherent arm selectors are the
private-arm condition and give the trifurcation count.

## i. Overview

The three branches of a trifurcation `x` are disconnected after `x` is removed, so another site
meets at most one of them and two branches avoid it: `x` has a private branch avoiding any given
other trifurcation. Open walks avoiding `x` survive removal of `x`. `pap_CoherentSelector ω n` asks
for arm ends `b x` with infinite clusters outside the trifurcation set, such that for connected
trifurcations `x ≠ y`, `b x` is cut from `y` by removing `x` while `b y` still reaches `y`. It is
equivalent to the private-arm condition and gives the count bound. It holds with no trifurcation,
one trifurcation, or two trifurcations with local ends.

The configuration-wide form of this condition, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`pap_not_forall_coherentSelector`). The Burton–Keane theorem that assumed it was removed as
vacuous.

## ii. Key results

- `pap_exists_private_branch` : a private branch at each trifurcation.
- `pap_coherentSelector_iff_privateArm` : coherent selectors are the private-arm condition.

## iii. Table of contents

- A. Private branches
- B. Coherent selectors
- C. Unsatisfiability of the configuration-wide conditions

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

lemma pap_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  daepf_arm_class_unique ω hd12 hd13 hd23 v

lemma pap_two_branches_avoid_vertex (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) :=
  daep2_two_branches_avoid ω hd12 hd13 hd23 v

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
  rcases pap_two_branches_avoid_vertex ω hd12 hd13 hd23 v with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
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

/-! ## B. Coherent selectors -/

/-- Coherent arm selector for the box of radius `n`: arm ends `b x` with infinite clusters outside
the
trifurcation set such that, for connected trifurcations `x ≠ y`, removing `x` cuts `b x` from `y`
while `b y` still reaches `y`. -/
def pap_CoherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) y ∧
        Connected d (removeSite x ω) (b y) y)

lemma pap_privateArm_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : pap_CoherentSelector ω n) : daepf_PrivateArm ω n := h

lemma pap_coherentSelector_iff_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    pap_CoherentSelector ω n ↔ daepf_PrivateArm ω n := Iff.rfl

lemma pap_coherentSelector_of_twoTrif_local (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
    (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
    (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
    (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_twoTrif ω n b hx0y0 htwo hbx0 hby0
    hpriv_xy hfar_xy hpriv_yx hfar_yx

lemma pap_coherentSelector_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_noTrif ω n hno

lemma pap_coherentSelector_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

lemma pap_Tcount_le_boundary_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : pap_CoherentSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn (pap_privateArm_of_coherentSelector ω n h)

/-! ## C. Unsatisfiability of the configuration-wide conditions -/

/-- `pap_CoherentSelector` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma pap_not_forall_coherentSelector (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      pap_CoherentSelector ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    pap_Tcount_le_boundary_of_coherentSelector ω n hn (h ω n hn)

end Percolation

end StatMech
