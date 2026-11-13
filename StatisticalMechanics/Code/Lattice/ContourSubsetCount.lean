/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Lattice.ContourCountInjection
import Code.Lattice.PlanarTopology

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}





































def RealisedContourWalkEncoding (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d), anchors.card ≤ ℓ ∧
    ∃ (enc : Finset (Sym2 (Site d)) → Σ v : Site d, (hypercubicLattice d).Walk v v)
      (decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d))),
      ∀ F ∈ realisedContours d n ℓ,
        (enc F).1 ∈ anchors ∧ (enc F).2.length = ℓ ∧ decode (enc F) = F















theorem realisedContours_card_le_of_walkEncoding {n ℓ : ℕ}
    (h : RealisedContourWalkEncoding d n ℓ) :
    (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
  classical
  obtain ⟨anchors, hcard, enc, decode, hspec⟩ := h
  
  have hinto : (realisedContours d n ℓ).card ≤
      (anchors.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card := by
    refine Finset.card_le_card_of_injOn (fun F => enc F) ?_ ?_
    · intro F hF
      rw [Finset.mem_coe] at hF
      obtain ⟨hanc, hlen, _⟩ := hspec F hF
      simp only [Finset.mem_coe, Finset.mem_sigma]
      exact ⟨hanc, SimpleGraph.mem_finsetWalkLength_iff.mpr hlen⟩
    · 
      intro F hF F' hF' heq
      rw [Finset.mem_coe] at hF hF'
      simp only at heq
      have e1 : decode (enc F) = F := (hspec F hF).2.2
      have e2 : decode (enc F') = F' := (hspec F' hF').2.2
      rw [← e1, ← e2, heq]
  
  calc (realisedContours d n ℓ).card
      ≤ (anchors.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card := hinto
    _ ≤ anchors.card * (2 * d) ^ ℓ := card_circuits_based_in_le_pow d anchors ℓ
    _ ≤ ℓ * (2 * d) ^ ℓ := Nat.mul_le_mul_right _ hcard




theorem contourSubsetCountBound_of_walkEncoding {n ℓ : ℕ}
    (h : RealisedContourWalkEncoding d n ℓ) : ContourSubsetCountBound d n ℓ :=
  realisedContours_card_le_of_walkEncoding h












theorem connFamily_fixedLen_card_le_peierls_of_walkEncoding {n ℓ : ℕ}
    (h : RealisedContourWalkEncoding d n ℓ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ℓ * (2 * d) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls n ℓ (contourSubsetCountBound_of_walkEncoding h)















theorem connClusterFamily_nonempty (n : ℕ) :
    ({StatMech.Ising.origin d} : Finset (Site d)) ∈ connClusterFamily (d := d) n := by
  rw [StatMech.Ising.pcc_mem_connClusterFamily]
  refine ⟨?_, singleton_origin_isConnectedCluster⟩
  
  rw [StatMech.Ising.clusterFamily, Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  rw [StatMech.Ising.mem_boxFinset]
  exact StatMech.Ising.origin_mem_box n
















theorem realisedContourWalkEncoding_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : RealisedContourWalkEncoding d n ℓ := by
  refine ⟨∅, by simp, fun _ => ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩,
    fun _ => ∅, ?_⟩
  intro F hF
  rw [hempty] at hF
  simp at hF





theorem contourSubsetCountBound_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : ContourSubsetCountBound d n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_empty hempty)














theorem connectedContourCount_of_walkEncoding {n : ℕ}
    (h : ∀ ℓ, RealisedContourWalkEncoding d n ℓ) :
    StatMech.Ising.ConnectedContourCount d n := by
  intro ℓ
  have hnat := connFamily_fixedLen_card_le_peierls_of_walkEncoding (h ℓ)
  calc (((connClusterFamily (d := d) n).filter
          (fun (K : Finset (Site d)) =>
            contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card : ℝ)
      ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring










theorem peierls_long_range_order_of_walkEncoding (hd : 2 ≤ d)
    (h : ∀ (n ℓ : ℕ), RealisedContourWalkEncoding d n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure d n β 0 ≠ StatMech.Ising.minusMeasure d n β 0 :=
  StatMech.Ising.pcl_peierls_long_range_order_of_count hd
    (fun n => connectedContourCount_of_walkEncoding (fun ℓ => h n ℓ))

end Lattice

end StatMech
