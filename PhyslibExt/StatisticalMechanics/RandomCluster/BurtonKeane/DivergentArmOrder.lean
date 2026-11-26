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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel

/-!
# Tree selectors and divergent arm orders

Tree selectors are single-cut branch separation; rooted and divergent arm orders give tree selectors
and the trifurcation count.

## i. Overview

Tree selection is single-cut branch separation `daep2_SingleCutBranchSeparation ω n`
(SingleCutSeparation). An arm placement `fsp_ArmPlacement` puts `b x` and `b y` in arms at `x` that
are disconnected without `x`. The rooted arm order `fsp_RootedArmOrder` asks for such placements and
gives tree selectors. `fsp_armWitness ω x v` chooses the neighbour of `x` through which `v` is
reached. The divergent arm order `fsp_DivergentArmOrder` asks the arm witnesses of connected
trifurcations to lie in different arms and gives the rooted arm order. All give the count bound;
they hold with no trifurcation, one, or two.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes (`fsp_not_forall_treeSelector`,
`fsp_not_forall_rootedArmOrder`, `fsp_not_forall_divergentArmOrder`). The Burton–Keane theorems that
assumed them were removed as vacuous.

## ii. Key results

- `fsp_treeSelector_of_rootedArmOrder` : tree selectors from the rooted arm order.
- `fsp_rootedArmOrder_of_divergentArmOrder` : the rooted order from the divergent order.

## iii. Table of contents

- A. Arm placements and the rooted order
- B. Arm witnesses
- C. The divergent order
- D. The count
- E. Unsatisfiability of the configuration-wide conditions

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

/-! ## A. Arm placements and the rooted order -/

/-- `b x` and `b y` lie in arms at `x` through neighbours `a`, `c` that are disconnected after `x`
is
removed. -/
def fsp_ArmPlacement (ω : ConfigSpace (Sym2 (Site d))) (b : Site d → Site d) (x y : Site d) :
    Prop :=
  ∃ a c : Site d, ¬ Connected d (removeSite x ω) a c ∧
    bkfl_inArm ω x a (b x) ∧ bkfl_inArm ω x c (b y)

lemma fsp_singleCutSep_of_armPlacement (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d} (h : fsp_ArmPlacement ω b x y) :
    ¬ Connected d (removeSite x ω) (b x) (b y) := by
  obtain ⟨a, c, hdis, hbx, hby⟩ := h
  exact bkfl_arms_separate ω hdis hbx hby

/-- Rooted arm order: arm ends `b x` with arm placements for all connected trifurcations `x ≠ y`. -/
def fsp_RootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → fsp_ArmPlacement ω b x y)

lemma fsp_treeSelector_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_RootedArmOrder ω n) : daep2_SingleCutBranchSeparation ω n := by
  obtain ⟨b, hdata, hplace⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  exact fsp_singleCutSep_of_armPlacement ω b (hplace x hxbox htri y hybox htriy hxy hconn)

/-! ## B. Arm witnesses -/

lemma fsp_inSomeArm_of_connected (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    ∃ a, (openSubgraph d ω).Adj x a ∧ Connected d (removeSite x ω) a v := by
  obtain ⟨p, hp⟩ := hxv.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ a _ hadj q =>
    refine ⟨a, hadj, ?_⟩
    have hnodup := hp.support_nodup
    rw [Walk.support_cons] at hnodup
    have hxq : x ∉ q.support := (List.nodup_cons.mp hnodup).1
    exact pap_connected_removeSite_of_walk_avoid ω x q hxq

open Classical in
/-- A neighbour of `x` through which `v` is reached after `x` is removed, when `x` and `v` are
connected
and distinct; otherwise `x`. -/
noncomputable def fsp_armWitness (ω : ConfigSpace (Sym2 (Site d))) (x v : Site d) : Site d :=
  if h : Connected d ω x v ∧ x ≠ v then
    (fsp_inSomeArm_of_connected ω h.1 h.2).choose
  else x

lemma fsp_armWitness_inArm (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    Connected d (removeSite x ω) (fsp_armWitness ω x v) v := by
  classical
  rw [fsp_armWitness, dite_eq_left ⟨hxv, hne⟩]
  exact (fsp_inSomeArm_of_connected ω hxv hne).choose_spec.2

lemma fsp_armWitness_adj (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    (openSubgraph d ω).Adj x (fsp_armWitness ω x v) := by
  classical
  rw [fsp_armWitness, dite_eq_left ⟨hxv, hne⟩]
  exact (fsp_inSomeArm_of_connected ω hxv hne).choose_spec.1

/-- The arm witnesses of `u` and `v` at `x` are connected after `x` is removed. -/
def fsp_sameArm (ω : ConfigSpace (Sym2 (Site d))) (x u v : Site d) : Prop :=
  Connected d (removeSite x ω) (fsp_armWitness ω x u) (fsp_armWitness ω x v)

lemma fsp_sep_of_notSameArm (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d}
    (hxu : Connected d ω x u) (hneu : x ≠ u)
    (hxv : Connected d ω x v) (hnev : x ≠ v)
    (hdiv : ¬ fsp_sameArm ω x u v) :
    ¬ Connected d (removeSite x ω) u v := by
  intro huv
  exact hdiv ((fsp_armWitness_inArm ω hxu hneu).trans
    (huv.trans (fsp_armWitness_inArm ω hxv hnev).symm))

lemma fsp_armPlacement_of_divergentWitness (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y a c : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a c)
    (hbx : bkfl_inArm ω x a (b x)) (hby : bkfl_inArm ω x c (b y)) :
    fsp_ArmPlacement ω b x y := ⟨a, c, hdis, hbx, hby⟩

lemma fsp_inArm_of_witness (ω : ConfigSpace (Sym2 (Site d))) {x a v : Site d}
    (h : Connected d (removeSite x ω) a v) : bkfl_inArm ω x a v := h

/-! ## C. The divergent order -/

/-- Divergent arm order: arm ends `b x ≠ x` such that for connected trifurcations `x ≠ y`, `b x` and
`b y` are in different arms at `x`. -/
def fsp_DivergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ b x ≠ x ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → ¬ fsp_sameArm ω x (b x) (b y))

lemma fsp_armPlacement_of_divergence (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d}
    (hbxx : b x ≠ x) (hbyx : x ≠ b y)
    (hxbx : Connected d ω x (b x)) (hxby : Connected d ω x (b y))
    (hdiv : ¬ fsp_sameArm ω x (b x) (b y)) :
    fsp_ArmPlacement ω b x y := by
  refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y), hdiv, ?_, ?_⟩
  · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
  · exact fsp_armWitness_inArm ω hxby hbyx

lemma fsp_rootedArmOrder_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_DivergentArmOrder ω n) : fsp_RootedArmOrder ω n := by
  obtain ⟨b, hdata, hdiv⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    obtain ⟨hbox, _, hconn, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hconn, hinf⟩
  · intro x hxbox htri y hybox htriy hxy hconn
    obtain ⟨_, hbxx, hxbx, _⟩ := hdata x hxbox htri
    obtain ⟨_, hbyy, hyby, _⟩ := hdata y hybox htriy
    have hxby : Connected d ω x (b y) := hconn.trans hyby
    by_cases hcase : x = b y
    · refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y),
        hdiv x hxbox htri y hybox htriy hxy hconn, ?_, ?_⟩
      · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
      · have hwit : fsp_armWitness ω x (b y) = x := by
          rw [← hcase]; simp only [fsp_armWitness]
          rw [dite_eq_right (by rintro ⟨_, hne⟩; exact hne rfl)]
        change Connected d (removeSite x ω) (fsp_armWitness ω x (b y)) (b y)
        rw [hwit, ← hcase]
    · exact fsp_armPlacement_of_divergence ω b hbxx hcase hxbx hxby
        (hdiv x hxbox htri y hybox htriy hxy hconn)

lemma fsp_rootedArmOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fsp_RootedArmOrder ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma fsp_rootedArmOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy

lemma fsp_rootedArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hplace_xy : fsp_ArmPlacement ω b x₀ y₀)
    (hplace_yx : fsp_ArmPlacement ω b y₀ x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hplace_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hplace_yx
      · exact absurd rfl hxy

lemma fsp_divergentArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ b x₀ ≠ x₀ ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ b y₀ ≠ y₀ ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv_xy : ¬ fsp_sameArm ω x₀ (b x₀) (b y₀))
    (hdiv_yx : ¬ fsp_sameArm ω y₀ (b y₀) (b x₀)) :
    fsp_DivergentArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hdiv_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hdiv_yx
      · exact absurd rfl hxy

/-! ## D. The count -/

lemma fsp_Tcount_le_boundary_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_RootedArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_singleCut ω n hn (fsp_treeSelector_of_rootedArmOrder ω n h)

lemma fsp_Tcount_le_boundary_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_DivergentArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fsp_Tcount_le_boundary_of_rootedArmOrder ω n hn
    (fsp_rootedArmOrder_of_divergentArmOrder ω n h)

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `daep2_SingleCutBranchSeparation` for every configuration and every box of radius `n ≥ 1` is
impossible when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma fsp_not_forall_treeSelector (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daep2_SingleCutBranchSeparation ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    daep2_Tcount_le_boundary_of_singleCut ω n hn (h ω n hn)

/-- `fsp_RootedArmOrder` for every configuration and every box of radius `n ≥ 1` is impossible when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma fsp_not_forall_rootedArmOrder (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fsp_RootedArmOrder ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    fsp_Tcount_le_boundary_of_rootedArmOrder ω n hn (h ω n hn)

/-- `fsp_DivergentArmOrder` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma fsp_not_forall_divergentArmOrder (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fsp_DivergentArmOrder ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    fsp_Tcount_le_boundary_of_divergentArmOrder ω n hn (h ω n hn)

end Percolation

end StatMech
