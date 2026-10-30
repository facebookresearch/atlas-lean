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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootDepthWalk

/-!
# Arm funnel geometry and corrected parents

Funnel geometry and its neighbour form give the weakened cut geometry; the corrected parent geometry
gives parent funnelling directly; labelled claws and chains check consistency.

## i. Overview

An open edge not incident to `t` survives the removal of `t`, so an arm end joined to its
trifurcation by an open edge stays connected to it. The funnel geometry `bc46_ArmFunnelGeometry` and
its neighbour form `bc46_NeighborArmFunnel` give the weakened cut geometry
`bc40_ArmCutGeometryFixed'`. With the arm-depth parent, the corrected parent geometry
`bc46_CorrectedParentGeometry` gives parent funnelling directly. Labelled claws on `Fin 10` and
chains on `Fin 8` check which clauses are consistent.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`bc46_not_forall_armFunnelGeometry`, `bc46_not_forall_neighborArmFunnel`,
`bc46_not_forall_correctedParentGeometry`). The Burton–Keane theorems that assumed them were removed
as vacuous.

## ii. Key results

- `bc46_armCutGeometryFixed'_of_armFunnelGeometry` : the weakened cut geometry from funnel geometry.
- `bc46_parentFunneling_of_correctedParentGeometry` : parent funnelling from the corrected parent
  geometry.

## iii. Table of contents

- A. Surviving arm links
- B. Funnel geometry
- C. Corrected parent geometry
- D. Labelled examples
- E. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Surviving arm links -/

lemma bc46_openEdge_removeSite_of_ne (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : Site d} (htu : t ≠ u) (htv : t ≠ v) (h : IsOpenEdge d ω u v) :
    IsOpenEdge d (removeSite t ω) u v := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj, ?_⟩
  have hnotmem : t ∉ s(u, v) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨htu, htv⟩
  rw [removeSite_apply_of_notMem hnotmem]; exact hopen

lemma bc46_armLink_survives (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {x bx : Site d} (htx : t ≠ x) (htbx : t ≠ bx) (hedge : IsOpenEdge d ω x bx) :
    Connected d (removeSite t ω) x bx :=
  (bc46_openEdge_removeSite_of_ne t ω htx htbx hedge).connected

/-! ## B. Funnel geometry -/

/-- Funnel geometry: arm ends `b x` joined to `x` by an open edge, with infinite clusters after
removing
`x`, such that the ends of lower trifurcations reach each arm-adjacent parent after its child is
removed. -/
def bc46_ArmFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s →
        Connected d (removeSite t ω) x (b x)))

lemma bc46_armCutGeometryFixed'_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc40_ArmCutGeometryFixed' ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  refine ⟨b, hdata, ?_⟩
  intro t s htbox htri hadj
  obtain ⟨hloc, hself, hlink⟩ := hclauses t s htbox htri hadj
  refine ⟨hloc, hself, ?_⟩
  intro x hxt hxs
  exact (hlink x hxt hxs).symm.trans hxs

/-- Neighbour funnel: as `bc46_ArmFunnelGeometry`, with `b x = x` off the trifurcations and `b x` an
open neighbour of `x`. -/
def bc46_NeighborArmFunnel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, ¬ (x ∈ box d n ∧ IsTrifurcation d ω x) → b x = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ IsOpenEdge d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → x ≠ t →
        Connected d (removeSite t ω) x s → b x ≠ t))

lemma bc46_armFunnelGeometry_of_neighborArmFunnel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_NeighborArmFunnel ω n) : bc46_ArmFunnelGeometry ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  · intro t s htbox htri hadj
    obtain ⟨hloc, hself, hmiss⟩ := hclauses t s htbox htri hadj
    refine ⟨hloc, hself, ?_⟩
    intro x hxt hxs
    by_cases hxtri : x ∈ box d n ∧ IsTrifurcation d ω x
    · obtain ⟨_, hedge, _⟩ := hdata x hxtri.1 hxtri.2
      have hbxt : b x ≠ t := hmiss x hxtri.1 hxtri.2 hxt hxs
      exact bc46_armLink_survives t ω (Ne.symm hxt) (Ne.symm hbxt) hedge
    · rw [hid x hxtri]

lemma bc46_parentFunneling_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc37_ParentFunneling ω n :=
  bc45_parentFunneling_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)

lemma bc46_selfDownArm_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc36_SelfDownArm ω n :=
  bc45_selfDownArm_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)

/-! ## C. Corrected parent geometry -/

/-- Corrected parent geometry with respect to the arm-depth parent: the end of each trifurcation is
separated from its parent, while the ends of lower trifurcations reach the parent after the child is
removed. -/
def bc46_CorrectedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, ¬ (x ∈ box d n ∧ IsTrifurcation d ω x) → b x = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ IsOpenEdge d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → bc45_armDepthRank ω n x < bc45_armDepthRank ω n y →
      (¬ Connected d (removeSite y ω) (b y) (b (bc45_armForestPar ω n y))) ∧
      (¬ Connected d (removeSite y ω) (b y) (bc45_armForestPar ω n y)) ∧
      (x ≠ bc45_armForestPar ω n y → b x ≠ y))

lemma bc46_parentFunneling_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc37_ParentFunneling ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  have hdataC : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite := by
    intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  refine ⟨b, bc45_armDepthRank ω n, bc45_armForestPar ω n, hdataC,
    bc45_armDepthRank_injective ω n, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hparT, hpadj, hprank⟩ :=
    bc45_rooting_spec ω n x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hmiss⟩ := hclauses x hxbox htri y hybox htriy hxy hconn hlt
  refine ⟨hloc, hself, fun hxne => ?_⟩
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hrs : Connected d (removeSite y ω) x (bc45_armForestPar ω n y) :=
    bc45_rootWard_connected ω n hxT hyT hxy hconn hlt hpadj hparT hprank
  have hbxy : b x ≠ y := hmiss hxne
  obtain ⟨_, hedge, _⟩ := hdata x hxbox htri
  have hlink : Connected d (removeSite y ω) x (b x) :=
    bc46_armLink_survives y ω (Ne.symm hxy) (Ne.symm hbxy) hedge
  exact hlink.symm.trans hrs

lemma bc46_selfDownArm_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc46_parentFunneling_of_correctedParentGeometry ω n hgeo)

lemma bc46_correctedParentGeometry_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc46_CorrectedParentGeometry ω n := by
  refine ⟨id, fun _ _ => rfl, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

/-! ## D. Labelled examples -/

/-- Component labels for a claw on `Fin 10`. -/
def bc46_clawLab (c v : Fin 10) : Fin 10 :=
  if c = 0 then
    (if v = 0 then 0
     else if v = 1 ∨ v = 4 ∨ v = 5 then 1
     else if v = 2 ∨ v = 6 ∨ v = 7 then 2 else 3)
  else if c = 1 then
    (if v = 1 then 1 else if v = 4 then 4 else if v = 5 then 5 else 0)
  else if c = 2 then
    (if v = 2 then 2 else if v = 6 then 6 else if v = 7 then 7 else 0)
  else
    (if v = 3 then 3 else if v = 8 then 8 else if v = 9 then 9 else 0)

/-- Arm ends for the claw on `Fin 10`. -/
def bc46_clawB : Fin 10 → Fin 10 := ![5, 4, 6, 8, 4, 5, 6, 7, 8, 9]

lemma bc46_clawShadow_hubCut_fails :
    ¬ ((bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 (bc46_clawB 1)) ∧
       (bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 1)) := by
  intro ⟨hloc, _hself⟩; exact hloc (by decide)

lemma bc46_clawShadow_funnelAtParent_fails :
    (0 : Fin 10) ≠ 1 ∧
    bc46_clawLab 1 0 = bc46_clawLab 1 0 ∧
    bc46_clawLab 1 (bc46_clawB 0) ≠ bc46_clawLab 1 0 := by
  refine ⟨by decide, rfl, by decide⟩

lemma bc46_clawShadow_pipeline_clauses_ok :
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 (bc46_clawB 0)) ∧
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 0) ∧
    (∀ x : Fin 10, x ≠ 1 → x ≠ 0 → bc46_clawLab 1 x = bc46_clawLab 1 0 →
      bc46_clawLab 1 (bc46_clawB x) = bc46_clawLab 1 0) := by
  refine ⟨by decide, by decide, by decide⟩

lemma bc46_clawShadow_guard_nontrivial :
    (bc46_clawLab 1 2 = bc46_clawLab 1 0 ∧ bc46_clawLab 1 3 = bc46_clawLab 1 0) ∧
    (bc46_clawLab 1 4 ≠ bc46_clawLab 1 0 ∧ bc46_clawLab 1 5 ≠ bc46_clawLab 1 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

lemma bc46_clawShadow_correctedParentGeometry_ok :
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y (bc46_clawB 0)) ∧
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y 0)) ∧
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      ∀ x : Fin 10, x ≠ y → x ≠ 0 → bc46_clawLab y x = bc46_clawLab y 0 →
        bc46_clawLab y (bc46_clawB x) = bc46_clawLab y 0) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- Component labels for a chain on `Fin 8`. -/
def bc46_chainLab (c v : Fin 8) : Fin 8 :=
  if c = 0 then
    (if v = 0 then 0 else if v = 4 then 4 else 1)
  else if c = 1 then
    (if v = 1 then 1 else if v = 5 then 5 else if v = 0 ∨ v = 4 then 0 else 2)
  else if c = 2 then
    (if v = 2 then 2 else if v = 6 then 6 else if v = 3 ∨ v = 7 then 3 else 0)
  else
    (if v = 3 then 3 else if v = 7 then 7 else 0)

/-- Arm ends for the chain on `Fin 8`. -/
def bc46_chainB : Fin 8 → Fin 8 := ![4, 5, 6, 7, 4, 5, 6, 7]

lemma bc46_chainShadow_all_clauses_hold :
    ∀ t s : Fin 8, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨
        (t = 2 ∧ s = 1) ∨ (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2) →
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t (bc46_chainB s)) ∧
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t s) ∧
      (∀ x : Fin 8, x ≠ t → bc46_chainLab t x = bc46_chainLab t s →
        bc46_chainLab t (bc46_chainB x) = bc46_chainLab t s) := by
  decide

lemma bc46_chainShadow_guard_nontrivial :
    (bc46_chainLab 2 0 = bc46_chainLab 2 1 ∧ bc46_chainLab 2 5 = bc46_chainLab 2 1) ∧
    (bc46_chainLab 2 3 ≠ bc46_chainLab 2 1 ∧ bc46_chainLab 2 7 ≠ bc46_chainLab 2 1) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `bc46_ArmFunnelGeometry` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc46_not_forall_armFunnelGeometry (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc46_ArmFunnelGeometry ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc46_selfDownArm_of_armFunnelGeometry ω n (h ω n hn))

/-- `bc46_NeighborArmFunnel` for every configuration and every box of radius `n ≥ 1` is impossible
when
`d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc46_not_forall_neighborArmFunnel (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc46_NeighborArmFunnel ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc46_selfDownArm_of_armFunnelGeometry ω n
        (bc46_armFunnelGeometry_of_neighborArmFunnel ω n (h ω n hn)))

/-- `bc46_CorrectedParentGeometry` for every configuration and every box of radius `n ≥ 1` is
impossible
when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc46_not_forall_correctedParentGeometry (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc46_CorrectedParentGeometry ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc46_selfDownArm_of_correctedParentGeometry ω n (h ω n hn))

end StatMech.Walls
