/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Lattice.PeierlsAnchorEncode
import Code.Lattice.ContourCountInjection
import Code.Lattice.PlanarTopology

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}











noncomputable def pc1_axisWalks (d ℓ : ℕ) :
    Finset (Σ v : Site d, (hypercubicLattice d).Walk v v) :=
  (axisAnchorPool d ℓ).sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)





theorem pc1_axisWalks_card_le (d ℓ : ℕ) :
    (pc1_axisWalks d ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
  unfold pc1_axisWalks
  calc ((axisAnchorPool d ℓ).sigma
          (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card
      ≤ (axisAnchorPool d ℓ).card * (2 * d) ^ ℓ := card_circuits_based_in_le_pow d _ ℓ
    _ ≤ ℓ * (2 * d) ^ ℓ := Nat.mul_le_mul_right _ (axisAnchorPool_card_le d ℓ)














def pc1_ContourInjection (d n ℓ : ℕ) : Prop :=
  ∃ f : Finset (Sym2 (Site d)) → Σ v : Site d, (hypercubicLattice d).Walk v v,
    (∀ F ∈ realisedContours d n ℓ, f F ∈ pc1_axisWalks d ℓ) ∧
      Set.InjOn f (↑(realisedContours d n ℓ))





theorem pc1_realisedContours_card_le_of_injection {n ℓ : ℕ}
    (h : pc1_ContourInjection d n ℓ) :
    (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
  obtain ⟨f, hmaps, hinj⟩ := h
  calc (realisedContours d n ℓ).card
      ≤ (pc1_axisWalks d ℓ).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ ℓ * (2 * d) ^ ℓ := pc1_axisWalks_card_le d ℓ




theorem pc1_contourSubsetCountBound_of_injection {n ℓ : ℕ}
    (h : pc1_ContourInjection d n ℓ) : ContourSubsetCountBound d n ℓ :=
  pc1_realisedContours_card_le_of_injection h












theorem pc1_mem_axisAnchorPool {ℓ : ℕ} {v : Site d} (hv : v ∈ axisAnchorPool d ℓ) :
    ∃ j : ℕ, j < ℓ ∧ v = axisVertex d j := by
  simp only [axisAnchorPool, Finset.mem_image, Finset.mem_range] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  exact ⟨j, hj, rfl⟩






theorem pc1_injection_of_axisCircuit {n ℓ : ℕ}
    (h : AxisContourDualCircuit d n ℓ) : pc1_ContourInjection d n ℓ := by
  classical
  obtain ⟨decode, hcirc⟩ := h
  
  refine ⟨fun F =>
    if hF : F ∈ realisedContours d n ℓ
      then ⟨axisVertex d (hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩
      else ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩, ?_, ?_⟩
  · 
    intro F hF
    have hj := (hcirc F hF).choose_spec.1
    have hlen := (hcirc F hF).choose_spec.2.choose_spec.1
    simp only [dif_pos hF, pc1_axisWalks, Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · simp only [axisAnchorPool, Finset.mem_image, Finset.mem_range]
      exact ⟨(hcirc F hF).choose, hj, rfl⟩
    · exact SimpleGraph.mem_finsetWalkLength_iff.mpr hlen
  · 
    intro F hF F' hF' heq
    rw [Finset.mem_coe] at hF hF'
    have hdF : decode ⟨axisVertex d (hcirc F hF).choose,
        (hcirc F hF).choose_spec.2.choose⟩ = F := (hcirc F hF).choose_spec.2.choose_spec.2
    have hdF' : decode ⟨axisVertex d (hcirc F' hF').choose,
        (hcirc F' hF').choose_spec.2.choose⟩ = F' := (hcirc F' hF').choose_spec.2.choose_spec.2
    simp only [dif_pos hF, dif_pos hF'] at heq
    rw [← hdF, ← hdF', heq]






theorem pc1_axisCircuit_of_injection {n ℓ : ℕ}
    (h : pc1_ContourInjection d n ℓ) : AxisContourDualCircuit d n ℓ := by
  classical
  obtain ⟨f, hmaps, hinj⟩ := h
  
  refine ⟨fun w =>
    if hex : ∃ F ∈ realisedContours d n ℓ, f F = w then hex.choose else ∅, ?_⟩
  intro F hF
  
  have hdec : ∀ w : Σ v : Site d, (hypercubicLattice d).Walk v v, w = f F →
      (if hex : ∃ G ∈ realisedContours d n ℓ, f G = w then hex.choose else ∅) = F := by
    intro w hw
    have hex : ∃ G ∈ realisedContours d n ℓ, f G = w := ⟨F, hF, hw.symm⟩
    have hchoice : hex.choose ∈ realisedContours d n ℓ ∧ f hex.choose = w := hex.choose_spec
    have hFeq : hex.choose = F :=
      hinj (Finset.mem_coe.mpr hchoice.1) (Finset.mem_coe.mpr hF) (hchoice.2.trans hw)
    simp only [dif_pos hex]; exact hFeq
  
  have hmem := hmaps F hF
  rcases hp : f F with ⟨v, W⟩
  rw [hp] at hmem
  simp only [pc1_axisWalks, Finset.mem_sigma] at hmem
  obtain ⟨j, hj, hbase⟩ := pc1_mem_axisAnchorPool hmem.1
  have hlen : W.length = ℓ := SimpleGraph.mem_finsetWalkLength_iff.mp hmem.2
  subst hbase
  exact ⟨j, hj, W, hlen, hdec ⟨axisVertex d j, W⟩ hp.symm⟩






theorem pc1_axisContourDualCircuit_iff_injection {n ℓ : ℕ} :
    AxisContourDualCircuit d n ℓ ↔ pc1_ContourInjection d n ℓ :=
  ⟨pc1_injection_of_axisCircuit, pc1_axisCircuit_of_injection⟩














theorem pc1_connectedContourCount_of_injection {n : ℕ}
    (h : ∀ ℓ, pc1_ContourInjection d n ℓ) : ConnectedContourCount d n := by
  intro ℓ
  have hnat : ((connClusterFamily (d := d) n).filter
      (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ℓ * (2 * d) ^ ℓ :=
    connFamily_fixedLen_card_le_peierls n ℓ (pc1_contourSubsetCountBound_of_injection (h ℓ))
  calc (((connClusterFamily (d := d) n).filter
          (fun (K : Finset (Site d)) =>
            contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card : ℝ)
      ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring










theorem pc1_peierls_long_range_order_of_injection (hd : 2 ≤ d)
    (h : ∀ (n ℓ : ℕ), pc1_ContourInjection d n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure d n β 0 ≠ StatMech.Ising.minusMeasure d n β 0 :=
  StatMech.Ising.pcl_peierls_long_range_order_of_count hd
    (fun n => pc1_connectedContourCount_of_injection (fun ℓ => h n ℓ))













theorem pc1_contourInjection_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : pc1_ContourInjection d n ℓ := by
  refine ⟨fun _ => ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩, ?_, ?_⟩
  · intro F hF; rw [hempty] at hF; simp at hF
  · intro F hF; rw [Finset.mem_coe, hempty] at hF; simp at hF




theorem pc1_contourSubsetCountBound_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : ContourSubsetCountBound d n ℓ :=
  pc1_contourSubsetCountBound_of_injection (pc1_contourInjection_of_empty hempty)








theorem pc1_axisWalks_nonempty (hd : 1 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    (pc1_axisWalks d (2 * k)).Nonempty := by
  classical
  
  set c : Fin d := ⟨0, hd⟩ with hc
  set u : Site d := Function.update (StatMech.Ising.origin d) c 1 with hu
  have hadj : (hypercubicLattice d).Adj (StatMech.Ising.origin d) u := by
    rw [hypercubicLattice_adj]
    
    rw [Finset.sum_eq_single c]
    · rw [hu, Function.update_self, StatMech.Ising.origin]; norm_num
    · intro i _ hi
      rw [hu, Function.update_of_ne hi, StatMech.Ising.origin]; simp
    · intro h; exact absurd (Finset.mem_univ c) h
  
  have hwalk : ∀ m : ℕ, ∃ W : (hypercubicLattice d).Walk (StatMech.Ising.origin d)
      (StatMech.Ising.origin d), W.length = 2 * m := by
    intro m
    induction m with
    | zero => exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | succ p ih =>
      obtain ⟨W, hW⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hadj.symm W), ?_⟩
      simp only [SimpleGraph.Walk.length_cons, hW]; ring
  obtain ⟨W, hW⟩ := hwalk k
  refine ⟨⟨StatMech.Ising.origin d, W⟩, ?_⟩
  simp only [pc1_axisWalks, Finset.mem_sigma]
  refine ⟨?_, SimpleGraph.mem_finsetWalkLength_iff.mpr hW⟩
  
  rw [← axisVertex_zero_eq_origin]
  simp only [axisAnchorPool, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by omega, rfl⟩

end Lattice

end StatMech
