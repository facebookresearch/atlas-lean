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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic

/-!
# The arm-adjacency graph spans

Cutting open walks at trifurcations shows that the arm-adjacency graph spans every cluster; the
original cut geometry fails, and a fixed version gives arm realisation and the count.

## i. Overview

A walk avoiding a finite set `S` transfers to the configuration with `S` removed
(`bc39_transferWalk`). Cutting an open walk between two connected trifurcations at the trifurcations
it meets gives arm-adjacent steps, so `bc38_ArmAdjSpanning` holds for every configuration
(`bc39_armAdjSpanning`). The cut geometry `bc38_ArmCutGeometry` fails whenever an arm-adjacent pair
exists. The fixed form `bc39_ArmCutGeometryFixed` exempts the two endpoints and gives arm
realisation and the trifurcation count bound.

The configuration-wide form of this condition, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`bc39_not_forall_cutGeometryFixed`). The Burton–Keane theorem that assumed it was removed as
vacuous.

## ii. Key results

- `bc39_armAdjSpanning` : the arm-adjacency graph spans every cluster.
- `bc39_armCutGeometry_false_of_armAdjacent` : the cut geometry fails for an arm-adjacent pair.
- `bc39_Tcount_le_boundary_of_cutGeometryFixed` : the count bound from the fixed cut geometry.

## iii. Table of contents

- A. Transferring walks
- B. Spanning
- C. The fixed cut geometry
- D. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Transferring walks -/

lemma bc39_openEdge_removeSites_of_notMem (S : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (hu : u ∉ S) (hv : v ∉ S)
    (h : (openSubgraph d ω).Adj u v) : (openSubgraph d (removeSites S ω)).Adj u v := by
  obtain ⟨hlat, hopen⟩ := h
  refine ⟨hlat, ?_⟩
  rw [removeSites, ite_eq_right]
  · exact hopen
  · rintro ⟨t, htS, hte⟩
    rw [Sym2.mem_iff] at hte
    rcases hte with rfl | rfl
    · exact hu htS
    · exact hv htS

/-- An open walk avoiding `S` as a walk in the configuration with `S` removed. -/
noncomputable def bc39_transferWalk (S : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {a b : Site d} (p : (openSubgraph d ω).Walk a b) (hp : ∀ v ∈ p.support, v ∉ S) :
    (openSubgraph d (removeSites S ω)).Walk a b := by
  refine p.transfer _ ?_
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hadj : (openSubgraph d ω).Adj u v := by
      rw [← SimpleGraph.mem_edgeSet]; exact p.edges_subset_edgeSet he
    exact bc39_openEdge_removeSites_of_notMem S ω (hp _ hu) (hp _ hv) hadj

lemma bc39_connected_removeSites_of_walk_avoids (S : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d} (p : (openSubgraph d ω).Walk a b)
    (hp : ∀ v ∈ p.support, v ∉ S) : Connected d (removeSites S ω) a b :=
  ⟨bc39_transferWalk S ω p hp⟩

/-! ## B. Spanning -/

lemma bc39_armAdj_edge_of_walk_avoids (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {a b : Site d}
    (hab : a ≠ b) (p : (openSubgraph d ω).Walk a b)
    (hint : ∀ v ∈ p.support, v ∈ tfc_trifFinset ω n → v = a ∨ v = b) :
    bc37_ArmAdjacent ω n a b := by
  refine ⟨hab, ⟨p⟩, ?_⟩
  unfold bc37_cutExcept
  apply bc39_connected_removeSites_of_walk_avoids _ ω p
  intro v hv hmem
  rw [Finset.mem_erase, Finset.mem_erase] at hmem
  obtain ⟨hvb, hva, hvT⟩ := hmem
  rcases hint v hv hvT with rfl | rfl
  · exact hva rfl
  · exact hvb rfl

lemma bc39_reach_of_walk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ (k : ℕ) {a b : Site d} (haT : a ∈ tfc_trifFinset ω n) (hbT : b ∈ tfc_trifFinset ω n)
      (p : (openSubgraph d ω).Walk a b), p.length ≤ k →
      (bc37_armAdjGraph ω n).Reachable ⟨a, haT⟩ ⟨b, hbT⟩ := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro a b haT hbT p hlen
    by_cases hab : a = b
    · subst hab
      exact SimpleGraph.Reachable.refl _
    · by_cases hint : ∀ v ∈ p.support, v ∈ tfc_trifFinset ω n → v = a ∨ v = b
      · have hadj : (bc37_armAdjGraph ω n).Adj ⟨a, haT⟩ ⟨b, hbT⟩ :=
          bc39_armAdj_edge_of_walk_avoids ω n hab p hint
        exact hadj.reachable
      · push Not at hint
        obtain ⟨c, hcsupp, hcT, hca, hcb⟩ := hint
        have hsum : (p.takeUntil c hcsupp).length + (p.dropUntil c hcsupp).length = p.length := by
          rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
        have htake_len : (p.takeUntil c hcsupp).length < k := by
          have hdrop_pos : 0 < (p.dropUntil c hcsupp).length := by
            rcases Nat.eq_zero_or_pos (p.dropUntil c hcsupp).length with h0 | hpos
            · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hcb
            · exact hpos
          omega
        have hdrop_len : (p.dropUntil c hcsupp).length < k := by
          have htake_pos : 0 < (p.takeUntil c hcsupp).length := by
            rcases Nat.eq_zero_or_pos (p.takeUntil c hcsupp).length with h0 | hpos
            · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hca.symm
            · exact hpos
          omega
        have r1 := IH _ htake_len haT hcT (p.takeUntil c hcsupp) (le_refl _)
        have r2 := IH _ hdrop_len hcT hbT (p.dropUntil c hcsupp) (le_refl _)
        exact r1.trans r2

lemma bc39_armAdjSpanning (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc38_ArmAdjSpanning ω n := by
  classical
  intro a b hconn
  obtain ⟨p⟩ := hconn
  exact bc39_reach_of_walk ω n p.length a.2 b.2 p (le_refl _)

/-! ## C. The fixed cut geometry -/

lemma bc39_armCutGeometry_false_of_armAdjacent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) : ¬ bc38_ArmCutGeometry ω n := by
  rintro ⟨b, _hdata, hclauses⟩
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  exact hself (hfun t hadj.1)

/-- Fixed arm cut geometry: as `bc38_ArmCutGeometry`, but the two endpoints of each arm-adjacent
pair
are exempt from the separation clause. -/
def bc39_ArmCutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s))

lemma bc39_armRealisation_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => hfun x hxne ?_⟩
  intro hxy'; subst hxy'; exact hxy rfl

lemma bc39_parentFunneling_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc39_armRealisation_of_cutGeometryFixed ω n hgeo)

lemma bc39_selfDownArm_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n (bc39_parentFunneling_of_cutGeometryFixed ω n hgeo)

lemma bc39_Tcount_le_boundary_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hgeo : bc39_ArmCutGeometryFixed ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc39_selfDownArm_of_cutGeometryFixed ω n hgeo)

lemma bc39_armCutGeometryFixed_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc39_ArmCutGeometryFixed ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)

lemma bc39_cutGeometryFixed_shadow_consistent (parNode bpar bself : ℕ)
    (hnode : parNode ≠ bself) (hbpar : bpar ≠ bself)
    (F : ℕ → Prop) (hF : ∀ w, F w → w ≠ bself) :
    ∃ up : ℕ → Prop,
      (¬ up bself ∧ up bpar) ∧
      (¬ up bself ∧ up parNode) ∧
      (∀ w, F w → up parNode ∧ up w) := by
  refine ⟨fun w => w ≠ bself, ⟨by simp, hbpar⟩, ⟨by simp, hnode⟩, ?_⟩
  intro w hw
  exact ⟨hnode, hF w hw⟩

lemma bc39_cutGeometryFixed_clauses_coexist (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (b : Site d → Site d) {t s : Site d} (_hadj : bc37_ArmAdjacent ω n t s)
    (hloc : ¬ Connected d (removeSite t ω) (b t) (b s))
    (hself : ¬ Connected d (removeSite t ω) (b t) s)
    (hfun : ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) :
    (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) :=
  ⟨hloc, hself, hfun⟩

/-! ## D. Unsatisfiability of the configuration-wide conditions -/

/-- `bc39_ArmCutGeometryFixed` for every configuration and every box of radius `n ≥ 1` is impossible
when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`, which
`tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc39_not_forall_cutGeometryFixed (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc39_ArmCutGeometryFixed ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc39_Tcount_le_boundary_of_cutGeometryFixed ω n hn (h ω n hn)

end StatMech.Walls
