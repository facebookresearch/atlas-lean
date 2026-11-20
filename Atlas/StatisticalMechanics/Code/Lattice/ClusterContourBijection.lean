/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Ising.PeierlsClose
import Code.Lattice.PlanarTopology

open Set Finset

namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}





theorem ccb_adj_mem_box_succ {n : ℕ} {x y : Site d} (h : (hypercubicLattice d).Adj x y)
    (hx : x ∈ box d n) : y ∈ box d (n + 1) := by
  rw [mem_box]; intro i
  have h1 : (x i - y i).natAbs ≤ 1 := by
    rw [hypercubicLattice_adj] at h
    calc (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
          Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
            (by intros; positivity) (Finset.mem_univ i)
      _ = 1 := h
  have h2 : (x i).natAbs ≤ n := hx i
  omega




theorem ccb_boundary_step_mem_crossEdges {K : Finset (Site d)} {n : ℕ} {a b : Site d}
    (hadj : (hypercubicLattice d).Adj a b) (haK : a ∈ K) (hbK : b ∉ K) (hab : a ∈ box d n) :
    s(a, b) ∈ crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n) := by
  rw [crossEdges, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [bondFinsetTouch, Finset.mem_image]
    refine ⟨(a, b), ?_, rfl⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hadj, Or.inl hab⟩
    · rw [mem_boxFinset]; exact box_subset_succ d n hab
    · rw [mem_boxFinset]; exact ccb_adj_mem_box_succ hadj hab
  · rw [crosses_mk]; exact ⟨fun _ => hbK, fun _ => haK⟩






noncomputable def regionDel (d : ℕ) (F : Set (Sym2 (Site d))) : Set (Site d) :=
  {x | ((hypercubicLattice d).deleteEdges F).Reachable (origin d) x}





theorem ccb_walk_stays_in_K {K : Finset (Site d)} {n : ℕ}
    (hsub : (↑K : Set (Site d)) ⊆ box d n) :
    ∀ {a x : Site d},
      ((hypercubicLattice d).deleteEdges
          ↑(crossEdges (↑K) (bondFinsetTouch d n))).Walk a x →
      a ∈ K → x ∈ K := by
  intro a x w
  induction w with
  | nil => exact fun h => h
  | @cons a b c hab w ih =>
    intro haK
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hadj, hne⟩ := hab
    have hbK : b ∈ K := by
      by_contra hbK
      exact hne (by simpa using ccb_boundary_step_mem_crossEdges hadj haK hbK (hsub haK))
    exact ih hbK











theorem ccb_regionDel_crossEdges_eq {K : Finset (Site d)} {n : ℕ}
    (hconn : IsConnectedCluster K) (hsub : (↑K : Set (Site d)) ⊆ box d n) :
    regionDel d ↑(crossEdges (↑K) (bondFinsetTouch d n)) = (↑K : Set (Site d)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w⟩
    exact ccb_walk_stays_in_K hsub w hconn.1
  · intro x hx
    have hle : latticeOn (↑K : Set (Site d)) ≤
        (hypercubicLattice d).deleteEdges ↑(crossEdges (↑K) (bondFinsetTouch d n)) := by
      intro a b hab
      obtain ⟨hadj, haK, hbK⟩ := hab
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hadj, ?_⟩
      intro hmem
      rw [Finset.mem_coe, crossEdges, Finset.mem_filter, crosses_mk] at hmem
      exact (hmem.2.mp haK) hbK
    exact (hconn.2 x (by simpa using hx)).mono hle





theorem ccb_crossEdges_injOn {n : ℕ} :
    Set.InjOn (fun K : Finset (Site d) => crossEdges (↑K) (bondFinsetTouch d n))
      {K | IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n} := by
  intro K hK K' hK' heq
  simp only [Set.mem_setOf_eq] at hK hK'
  simp only [] at heq
  have e1 := ccb_regionDel_crossEdges_eq hK.1 hK.2
  have e2 := ccb_regionDel_crossEdges_eq hK'.1 hK'.2
  have hreg : regionDel d ↑(crossEdges (↑K) (bondFinsetTouch d n))
       = regionDel d ↑(crossEdges (↑K') (bondFinsetTouch d n)) := by rw [heq]
  rw [e1, e2] at hreg
  exact_mod_cast hreg





noncomputable def ccb_contourFiber (d n ℓ : ℕ) : Finset (Finset (Site d)) :=
  (connClusterFamily (d := d) n).filter
    (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)


theorem ccb_connClusterFamily_props {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ connClusterFamily (d := d) n) :
    IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n := by
  rw [pcc_mem_connClusterFamily] at hK
  exact ⟨hK.2, clusterFamily_subset_box hK.1⟩














def ccb_ContourEncodingExists (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d),
    anchors.card ≤ ℓ ∧
    ∃ enc : Finset (Site d) → Σ v : Site d, (hypercubicLattice d).Walk v v,
      (∀ K ∈ ccb_contourFiber d n ℓ, (enc K).1 ∈ anchors ∧ (enc K).2.length = ℓ) ∧
      Set.InjOn enc (↑(ccb_contourFiber d n ℓ))






theorem ccb_connectedContourCount_of_encoding {n : ℕ}
    (h : ∀ ℓ, ccb_ContourEncodingExists d n ℓ) :
    ConnectedContourCount d n := by
  intro ℓ
  obtain ⟨anchors, hcard, enc, hmaps, hinj⟩ := h ℓ
  have hcardfib : (ccb_contourFiber d n ℓ).card ≤
      (anchors.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card := by
    refine Finset.card_le_card_of_injOn (fun K => enc K) ?_ hinj
    intro K hK
    rw [Finset.mem_coe] at hK
    obtain ⟨hanc, hlen⟩ := hmaps K hK
    rw [Finset.mem_coe, Finset.mem_sigma]
    exact ⟨hanc, SimpleGraph.mem_finsetWalkLength_iff.mpr hlen⟩
  have hTcard := card_circuits_based_in_le_pow d anchors ℓ
  have hfinal : (ccb_contourFiber d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ :=
    le_trans hcardfib (le_trans hTcard (Nat.mul_le_mul_right _ hcard))
  change ((ccb_contourFiber d n ℓ).card : ℝ) ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ
  calc ((ccb_contourFiber d n ℓ).card : ℝ) ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by
        exact_mod_cast hfinal
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring









theorem ccb_contourEncodingExists_of_decode (n ℓ : ℕ)
    (anchors : Finset (Site d)) (hanc : anchors.card ≤ ℓ)
    (enc : Finset (Site d) → Σ v : Site d, (hypercubicLattice d).Walk v v)
    (hmaps : ∀ K ∈ ccb_contourFiber d n ℓ, (enc K).1 ∈ anchors ∧ (enc K).2.length = ℓ)
    (decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)))
    (hdec : ∀ K ∈ ccb_contourFiber d n ℓ,
      decode (enc K) = crossEdges (↑K) (bondFinsetTouch d n)) :
    ccb_ContourEncodingExists d n ℓ := by
  refine ⟨anchors, hanc, enc, hmaps, ?_⟩
  intro K hK K' hK' heq
  rw [Finset.mem_coe, ccb_contourFiber, Finset.mem_filter] at hK hK'
  have hbd : crossEdges (↑K) (bondFinsetTouch d n) = crossEdges (↑K') (bondFinsetTouch d n) := by
    rw [← hdec K (by rw [ccb_contourFiber, Finset.mem_filter]; exact hK),
        ← hdec K' (by rw [ccb_contourFiber, Finset.mem_filter]; exact hK'), heq]
  exact ccb_crossEdges_injOn (ccb_connClusterFamily_props hK.1)
    (ccb_connClusterFamily_props hK'.1) hbd












theorem ccb_peierls_long_range_order_of_encoding (hd : 2 ≤ d)
    (hEnc : ∀ (n ℓ : ℕ), ccb_ContourEncodingExists d n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      Ising.plusMeasure d n β 0 ≠ Ising.minusMeasure d n β 0 :=
  Ising.pcl_peierls_long_range_order_of_count hd
    (fun n => ccb_connectedContourCount_of_encoding (fun ℓ => hEnc n ℓ))

end Lattice

end StatMech
