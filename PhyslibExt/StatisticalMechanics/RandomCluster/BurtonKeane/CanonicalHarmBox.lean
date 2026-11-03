/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.Group.Action.TypeTags
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Arms of canonical trifurcations and the next box

The arms of a trifurcation in a box start in the next box; requiring them to start in the box itself
fails for a trifurcation next to the boundary, but holds for trifurcations in the interior.

## i. Overview

An open neighbour of a site of the box of radius `n` lies in the box of radius `n + 1`, and an
infinite arm from there crosses the boundary of the next box. The stronger requirement that arms
start in the box itself fails: the shifted three-ray configuration `bwallConfig` has a trifurcation
at `(1, 0)` in the box of radius `1` with an arm at `(2, 0)` outside it (`bc53_harmbox_false`). It
holds when all trifurcations lie in the interior box of radius `n - 1`, which gives the count for
canonical interior trifurcations.

## ii. Key results

- `bc53_harmbox_false` : arms need not start in the box.
- `bc53_count_of_interior` : the count for canonical trifurcations in the interior.

## iii. Table of contents

- A. Arms and the next box
- B. A trifurcation at the boundary
- C. Interior trifurcations

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Arms and the next box -/

lemma bc53_canonicalArm_inbox {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a : Site d}
    (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d (n + 1) :=
  arc_neighbour_in_box_succ hx hadj.1

lemma bc53_canonicalArm_crosses_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x a : Site d) (hax : a ≠ x) (habox : a ∈ box d (n + 1))
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d (n + 1),
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support :=
  arc_infinite_cluster_reaches_boundary ω (n + 1) (by omega) x a hax habox hinf

lemma bc53_harmbox_succ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
        a ∈ box d (n + 1) := by
  intro x hx _ a hadj _
  exact bc53_canonicalArm_inbox hx hadj

namespace Bc53Witness

open StatMech.Percolation.CtcWitness

/-! ## B. A trifurcation at the boundary -/

lemma threeRay_canonical_origin :
    IsCanonicalTrifurcation 2 threeRayConfig (px 0) := by
  classical
  refine ⟨px 1, py 1, px (-1), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc : (px 1) 1 = (py 1) 1 := by rw [h]
      simp [px, py] at hc
    · intro h; have h0 : (1 : ℤ) = -1 := px_inj h; omega
    · intro h
      have hc : (py 1) 0 = (px (-1)) 0 := by rw [h]
      simp [px, py] at hc
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨px_adj 0, ?_⟩
      have := px_ray_open 0; simpa [px] using this
    · refine ⟨py_adj 0, ?_⟩
      have := py_ray_open 0 (le_refl 0); simpa [px, py] using this
    · refine ⟨?_, ?_⟩
      · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]
      · have := px_ray_open (-1)
        rw [show ((-1 : ℤ) + 1) = 0 by ring] at this
        rw [Sym2.eq_swap]; simpa [px] using this
  · exact ⟨cut_px_pos_infinite, cut_py_pos_infinite, cut_px_neg_infinite⟩
  · exact ⟨cut_disconnect_pos_py, cut_disconnect_pos_neg, fun h =>
      cut_disconnect_neg_py h.symm⟩

/-- The shift by `(1, 0)`. -/
noncomputable def g : Multiplicative (Site 2) := Multiplicative.ofAdd (![(1 : ℤ), 0] : Site 2)

/-- The three-ray configuration shifted by `(1, 0)`. -/
noncomputable def bwallConfig : ConfigSpace (Sym2 (Site 2)) := shift g threeRayConfig

lemma g_smul_px0 : (g • px 0) = (![(1 : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [g, px, smul_site_apply]

lemma g_smul_px1 : (g • px 1) = (![(2 : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [g, px, smul_site_apply]

lemma bwall_isTrifurcation : IsTrifurcation 2 bwallConfig (![(1 : ℤ), 0] : Site 2) := by
  rw [bwallConfig, ← g_smul_px0, isTrifurcation_shift]
  exact ctc2_isTrifurcation_of_canonical threeRay_canonical_origin

lemma bwall_hub_in_box : (![(1 : ℤ), 0] : Site 2) ∈ box 2 1 := by
  rw [mem_box]; intro i; fin_cases i <;> simp

lemma bwall_arm_adj :
    (openSubgraph 2 bwallConfig).Adj (![(1 : ℤ), 0] : Site 2) (![(2 : ℤ), 0] : Site 2) := by
  rw [bwallConfig, ← g_smul_px0, ← g_smul_px1, openSubgraph_adj_shift]
  refine ⟨px_adj 0, ?_⟩
  have := px_ray_open 0; simpa [px] using this

lemma bwall_arm_cut_infinite :
    (cluster 2 (removeSite (![(1 : ℤ), 0] : Site 2) bwallConfig) (![(2 : ℤ),
        0] : Site 2)).Infinite := by
  rw [bwallConfig, ← g_smul_px0, ← g_smul_px1, removeSite_shift, cluster_shift]
  exact (Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))).mpr cut_px_pos_infinite

lemma bwall_arm_outside_box : (![(2 : ℤ), 0] : Site 2) ∉ box 2 1 := by
  rw [mem_box]; simp only [not_forall, not_le]
  exact ⟨0, by simp⟩

end Bc53Witness

lemma bc53_harmbox_false :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
        ∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
          ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite →
            a ∈ box 2 n) := by
  intro h
  exact Bc53Witness.bwall_arm_outside_box
    (h Bc53Witness.bwallConfig 1 (![(1 : ℤ), 0] : Site 2) Bc53Witness.bwall_hub_in_box
      Bc53Witness.bwall_isTrifurcation (![(2 : ℤ), 0] : Site 2)
      Bc53Witness.bwall_arm_adj Bc53Witness.bwall_arm_cut_infinite)

/-! ## C. Interior trifurcations -/

lemma bc53_harmbox_of_interior (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n := by
  intro x hxbox htri a hadj _
  by_contra hanotbox
  exact (cfc_neighbour_outside_box_imp_boundary hn hxbox hadj.1 hanotbox)
    (hint x hxbox htri)

lemma bc53_count_of_interior (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  StatMech.Percolation.cfc_Tcount_le_boundary_of_canonical ω n hn hcanon (bc53_harmbox_of_interior
      ω n hn hint)

lemma bc53_status :
    (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
        ∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
          ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite →
            a ∈ box 2 n)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      ∀ x, x ∈ box d n → IsTrifurcation d ω x →
        ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
          a ∈ box d (n + 1)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) →
      (∀ x, x ∈ box d n → IsTrifurcation d ω x →
        ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) →
      Tcount d ω n ≤ boxSV_boundaryCard d n) :=
  ⟨bc53_harmbox_false, fun ω n => bc53_harmbox_succ ω n,
   fun ω n hn hcanon harmbox => StatMech.Percolation.cfc_Tcount_le_boundary_of_canonical ω n hn
       hcanon harmbox⟩

end StatMech.Walls
