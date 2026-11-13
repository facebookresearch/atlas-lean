/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Walls.bc52jordanbridge
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc53_canonicalArm_inbox {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a : Site d}
    (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d (n + 1) :=
  arc_neighbour_in_box_succ hx hadj.1






theorem bc53_canonicalArm_crosses_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x a : Site d) (hax : a ≠ x) (habox : a ∈ box d (n + 1))
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d (n + 1),
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support :=
  arc_infinite_cluster_reaches_boundary ω (n + 1) (by omega) x a hax habox hinf





theorem bc53_harmbox_succ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
        a ∈ box d (n + 1) := by
  intro x hx _ a hadj _
  exact bc53_canonicalArm_inbox hx hadj














namespace Bc53Witness

open StatMech.Percolation.CtcWitness






theorem threeRay_canonical_origin :
    IsCanonicalTrifurcation 2 threeRayConfig (px 0) := by
  classical
  refine ⟨px 1, py 1, px (-1), ?_, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc : (px 1) 1 = (py 1) 1 := by rw [h]
      simp [px, py] at hc
    · intro h; have h0 : (1 : ℤ) = -1 := px_inj h; omega
    · intro h
      have hc : (py 1) 0 = (px (-1)) 0 := by rw [h]
      simp [px, py] at hc
  · 
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨px_adj 0, ?_⟩
      have := px_ray_open 0; simpa [px] using this
    · refine ⟨py_adj 0, ?_⟩
      have := py_ray_open 0 (le_refl 0); simpa [py] using this
    · refine ⟨?_, ?_⟩
      · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]
      · have := px_ray_open (-1)
        rw [show ((-1 : ℤ) + 1) = 0 by ring] at this
        rw [Sym2.eq_swap]; simpa [px] using this
  · 
    exact ⟨cut_px_pos_infinite, cut_py_pos_infinite, cut_px_neg_infinite⟩
  · 
    exact ⟨cut_disconnect_pos_py, cut_disconnect_pos_neg, fun h =>
      cut_disconnect_neg_py h.symm⟩


noncomputable def g : Multiplicative (Site 2) := Multiplicative.ofAdd (![(1 : ℤ), 0] : Site 2)


noncomputable def bwallConfig : ConfigSpace (Sym2 (Site 2)) := shift g threeRayConfig


theorem g_smul_px0 : (g • px 0) = (![(1 : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [g, px, smul_site_apply]


theorem g_smul_px1 : (g • px 1) = (![(2 : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [g, px, smul_site_apply]




theorem bwall_isTrifurcation : IsTrifurcation 2 bwallConfig (![(1 : ℤ), 0] : Site 2) := by
  rw [bwallConfig, ← g_smul_px0, isTrifurcation_shift]
  exact ctc2_isTrifurcation_of_canonical threeRay_canonical_origin


theorem bwall_hub_in_box : (![(1 : ℤ), 0] : Site 2) ∈ box 2 1 := by
  rw [mem_box]; intro i; fin_cases i <;> simp


theorem bwall_arm_adj :
    (openSubgraph 2 bwallConfig).Adj (![(1 : ℤ), 0] : Site 2) (![(2 : ℤ), 0] : Site 2) := by
  rw [bwallConfig, ← g_smul_px0, ← g_smul_px1, openSubgraph_adj_shift]
  refine ⟨px_adj 0, ?_⟩
  have := px_ray_open 0; simpa [px] using this



theorem bwall_arm_cut_infinite :
    (cluster 2 (removeSite (![(1 : ℤ), 0] : Site 2) bwallConfig) (![(2 : ℤ), 0] : Site 2)).Infinite := by
  rw [bwallConfig, ← g_smul_px0, ← g_smul_px1, removeSite_shift, cluster_shift]
  exact (Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))).mpr cut_px_pos_infinite


theorem bwall_arm_outside_box : (![(2 : ℤ), 0] : Site 2) ∉ box 2 1 := by
  rw [mem_box]; simp only [not_forall, not_le]
  exact ⟨0, by simp⟩

end Bc53Witness








theorem bc53_harmbox_false :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
        ∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
          ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite →
            a ∈ box 2 n) := by
  intro h
  exact Bc53Witness.bwall_arm_outside_box
    (h Bc53Witness.bwallConfig 1 (![(1 : ℤ), 0] : Site 2) Bc53Witness.bwall_hub_in_box
      Bc53Witness.bwall_isTrifurcation (![(2 : ℤ), 0] : Site 2)
      Bc53Witness.bwall_arm_adj Bc53Witness.bwall_arm_cut_infinite)





















theorem bc53_harmbox_of_interior (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n := by
  intro x hxbox htri a hadj _
  by_contra hanotbox
  exact (cfc_neighbour_outside_box_imp_boundary hn hxbox hadj.1 hanotbox)
    (hint x hxbox htri)





theorem bc53_count_of_harmbox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc52_Tcount_le_boundary_of_canonical ω n hn hcanon harmbox






theorem bc53_count_of_interior (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (hint : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x ∈ box d (n - 1)) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc53_count_of_harmbox ω n hn hcanon (bc53_harmbox_of_interior ω n hn hint)
















theorem bc53_status :
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
   fun ω n hn hcanon harmbox => bc53_count_of_harmbox ω n hn hcanon harmbox⟩

end StatMech.Walls
