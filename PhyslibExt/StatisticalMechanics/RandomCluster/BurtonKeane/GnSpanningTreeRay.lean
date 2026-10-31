/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest

/-!
# Rays in spanning trees of the coarse graph

Infinite components of a locally finite subgraph of the coarse graph contain rays that reach the
boundary, and arm subforest data bound the coarse count.

## i. Overview

The coarse graph `bgn_Gn ω L` is a subgraph of the lattice. In a locally finite subgraph `T`, an
infinite avoiding cluster contains an injective ray, which reaches the boundary of every box around
its start. Rays from distinct branches of a tree are disjoint and their union is acyclic, so arm
subforest data give the coarse counting bound and, for every configuration, uniqueness for Bernoulli
percolation. The example `bgn_W` has two hubs of degree three in every connected spanning subgraph.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bsg_GnTreeRay_reaches_boundary` : rays in infinite components reach the boundary
- `bsg_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

private lemma bsg_ediv_succ_bounds (q m : ℤ) (hq : 0 < q) :
    m / q ≤ (m + 1) / q ∧ (m + 1) / q ≤ m / q + 1 := by
  refine ⟨Int.ediv_le_ediv hq (by omega), ?_⟩
  have hstep : (m + 1) / q ≤ (m + 1 * q) / q :=
    Int.ediv_le_ediv hq (by nlinarith)
  rwa [Int.add_mul_ediv_right _ _ (by omega : q ≠ 0)] at hstep

private lemma bsg_idxCoord_shift_le (L : ℕ) (c s : ℤ) (hs : s = 1 ∨ s = -1) :
    ((c + L) / (2 * (L : ℤ) + 1) - (c + s + L) / (2 * (L : ℤ) + 1)).natAbs ≤ 1 := by
  have hq : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  rcases hs with rfl | rfl
  · have h := bsg_ediv_succ_bounds (2 * (L : ℤ) + 1) (c + L) hq
    have e1 : c + 1 + (L : ℤ) = (c + L) + 1 := by ring
    rw [e1]
    omega
  · have h := bsg_ediv_succ_bounds (2 * (L : ℤ) + 1) (c + (-1) + L) hq
    have e1 : (c + (-1) + L) + 1 = c + (L : ℤ) := by ring
    rw [e1] at h
    omega

lemma bsg_Gn_le_lattice (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    bgn_Gn ω L ≤ hypercubicLattice d := by
  intro j k hjk
  obtain ⟨hne, a, b, ha, hb, hab⟩ := hjk
  have hnn : NearestNeighbour d a b := (openSubgraph_adj ω a b).mp hab |>.1
  rw [nearestNeighbour_iff_shift] at hnn
  obtain ⟨t, s, hs, hbshift⟩ := hnn
  have hcoord : ∀ i, (j i - k i).natAbs ≤ (if i = t then 1 else 0) := by
    intro i
    by_cases hit : i = t
    · rw [ite_eq_left hit]
      have hbi : b i = a i + s := by
        rw [hbshift, hit, Lattice.shift, Function.update_self]
      have hji : j i = (a i + L) / (2 * (L : ℤ) + 1) := by rw [← ha]; rfl
      have hki : k i = (a i + s + L) / (2 * (L : ℤ) + 1) := by
        rw [← hb]; change (b i + L) / (2 * (L : ℤ) + 1) = _; rw [hbi]
      rw [hji, hki]
      exact bsg_idxCoord_shift_le L (a i) s hs
    · rw [ite_eq_right hit]
      have hbi : b i = a i := by rw [hbshift, Lattice.shift, Function.update_of_ne hit]
      have hji : j i = (a i + L) / (2 * (L : ℤ) + 1) := by rw [← ha]; rfl
      have hki : k i = (a i + L) / (2 * (L : ℤ) + 1) := by
        rw [← hb]; change (b i + L) / (2 * (L : ℤ) + 1) = _; rw [hbi]
      rw [hji, hki]; simp
  rw [hypercubicLattice_adj]
  set S := (∑ i, (j i - k i).natAbs) with hS
  have hsum_le : S ≤ 1 := by
    rw [hS]
    calc (∑ i, (j i - k i).natAbs) ≤ ∑ i, (if i = t then 1 else 0) :=
          Finset.sum_le_sum (fun i _ => hcoord i)
      _ = 1 := by simp
  have hsum_pos : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · exfalso
      apply hne
      funext i
      have hle : (j i - k i).natAbs ≤ S :=
        Finset.single_le_sum (f := fun i => (j i - k i).natAbs)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
      have : (j i - k i).natAbs = 0 := by omega
      omega
    · exact hpos
  omega

#check @bsg_Gn_le_lattice

lemma bsg_GnTreeRay_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hT : T ≤ bgn_Gn ω L)
    {w : Site d} {R : ℕ} (hR : 1 ≤ R) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_treeRay_reaches_boundary T (le_trans hT (bsg_Gn_le_lattice ω L)) hR hw hinf

lemma bsg_GnBranchRay_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (T : SimpleGraph (Site d)) [LocallyFinite T] (hT : T ≤ bgn_Gn ω L)
    {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) :=
  bri_branchRay_reaches_boundary T (le_trans hT (bsg_Gn_le_lattice ω L)) hR hwx hw hinf

lemma bsg_twoHub_witness :
    bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧
      bri_twoHub.degree 4 = 2 ∧
      (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) :=
  ⟨bri_twoHub_witness.1, bri_twoHub_witness.2.2.1, bri_twoHub_witness.2.2.2.1,
    bri_twoHub_witness.2.2.2.2.1, bri_twoHub_witness.2.2.2.2.2.2.2.2.2⟩

/-! ## B. Summary -/

lemma bsg_status :
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bgn_Gn ω L ≤ hypercubicLattice 2) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [LocallyFinite T],
      T ≤ bgn_Gn ω L → ∀ {w : Site 2} {R : ℕ}, 1 ≤ R → w ∈ box 2 R →
        (ray34_AvoidCluster T ∅ w).Infinite →
        ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
          (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected →
      3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω L; exact bsg_Gn_le_lattice ω L
  · intro ω L T _ hT w R hR hw hinf; exact bsg_GnTreeRay_reaches_boundary ω L T hT hR hw hinf
  · intro T _ hTH hTconn; exact bcv_bgnW_test hTH hTconn
  · intro V T hT ι Gs hGs; exact bri_union_le_acyclic hT Gs hGs
  · intro ω L R h; exact bca_datum_implies_count ω L R h
  · intro p hp1 hp0 hdata; exact bau_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls

#print axioms StatMech.Walls.bsg_Gn_le_lattice
#print axioms StatMech.Walls.bsg_GnTreeRay_reaches_boundary
#print axioms StatMech.Walls.bsg_status
