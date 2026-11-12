/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.Percolation.SubcriticalDecay
import Code.Percolation.DctDifferentialFull
import Code.Percolation.Theta

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Lattice
open StatMech.Percolation

variable {d : ℕ}



























theorem perco_ode_antitone (p₀ : ℝ) (hp₀ : 0 < p₀) (f : ℝ → ℝ)
    (hdiff : ∀ p ∈ Ico p₀ 1, DifferentiableAt ℝ f p)
    (hineq : ∀ p ∈ Ioo p₀ 1, (1 / (p * (1 - p))) * (1 - f p) ≤ deriv f p) :
    AntitoneOn (fun p => (1 - f p) * (p / (1 - p))) (Ico p₀ 1) := by
  set g : ℝ → ℝ := fun p => (1 - f p) * (p / (1 - p)) with hg
  have hsub : interior (Ico p₀ 1) = Ioo p₀ 1 := interior_Ico
  
  have hgderiv : ∀ p ∈ Ioo p₀ 1, deriv g p
      = (- deriv f p) * (p / (1 - p)) + (1 - f p) * (1 / (1 - p) ^ 2) := by
    intro p hp
    have hp0 : p ∈ Ico p₀ 1 := ⟨le_of_lt hp.1, hp.2⟩
    have hd := hdiff p hp0
    have h1mp : (1 - p) ≠ 0 := by have := hp.2; intro h; rw [sub_eq_zero] at h; linarith
    have hH : HasDerivAt g
        ((- deriv f p) * (p / (1 - p)) + (1 - f p) * (1 / (1 - p) ^ 2)) p := by
      have ha : HasDerivAt (fun p : ℝ => 1 - f p) (- deriv f p) p := by
        simpa using (hasDerivAt_const p (1 : ℝ)).sub hd.hasDerivAt
      have hb : HasDerivAt (fun p : ℝ => p / (1 - p)) (1 / (1 - p) ^ 2) p := by
        have hnum : HasDerivAt (fun p : ℝ => p) 1 p := hasDerivAt_id p
        have hden : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by
          simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
        have := hnum.div hden h1mp
        convert this using 1
        field_simp
        ring
      simpa using ha.mul hb
    exact hH.deriv
  
  have hgnonpos : ∀ p ∈ Ioo p₀ 1, deriv g p ≤ 0 := by
    intro p hp
    have hppos : 0 < p := lt_trans hp₀ hp.1
    have h1mp : 0 < 1 - p := by have := hp.2; linarith
    have hpne : p ≠ 0 := ne_of_gt hppos
    have h1mpne : (1 - p) ≠ 0 := ne_of_gt h1mp
    rw [hgderiv p hp]
    have key := hineq p hp
    have hfac : 0 < p / (1 - p) := div_pos hppos h1mp
    
    have step1 : (1 / (p * (1 - p))) * (1 - f p) * (p / (1 - p))
        ≤ deriv f p * (p / (1 - p)) :=
      mul_le_mul_of_nonneg_right key (le_of_lt hfac)
    have hsimp : (1 / (p * (1 - p))) * (1 - f p) * (p / (1 - p))
        = (1 - f p) * (1 / (1 - p) ^ 2) := by
      field_simp
    rw [hsimp] at step1
    nlinarith [step1]
  
  have hcont : ContinuousOn g (Ico p₀ 1) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.sub (fun p hp => (hdiff p hp).continuousAt.continuousWithinAt)
    · apply ContinuousOn.div continuousOn_id (continuousOn_const.sub continuousOn_id)
      intro p hp
      have hp2 := hp.2
      simp only [id_eq]
      intro h; rw [sub_eq_zero] at h; rw [← h] at hp2; exact lt_irrefl 1 hp2
  have hdon : DifferentiableOn ℝ g (interior (Ico p₀ 1)) := by
    rw [hsub]
    intro p hp
    have hp0 : p ∈ Ico p₀ 1 := ⟨le_of_lt hp.1, hp.2⟩
    have h1mp : (1 - p) ≠ 0 := by have := hp.2; intro h; rw [sub_eq_zero] at h; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    apply DifferentiableAt.mul
    · exact (differentiableAt_const 1).sub (hdiff p hp0)
    · exact DifferentiableAt.div differentiableAt_id
        ((differentiableAt_const 1).sub differentiableAt_id) h1mp
  apply antitoneOn_of_deriv_nonpos (convex_Ico p₀ 1) hcont hdon
  rw [hsub]
  exact hgnonpos

















theorem profile_ge_of_diffineq (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1) (f : ℝ → ℝ)
    (hdiff : ∀ p ∈ Ico p₀ 1, DifferentiableAt ℝ f p)
    (hineq : ∀ p ∈ Ioo p₀ 1, (1 / (p * (1 - p))) * (1 - f p) ≤ deriv f p)
    (hf0 : 0 ≤ f p₀)
    {p : ℝ} (hpp₀ : p₀ ≤ p) (hp1 : p < 1) :
    (p - p₀) / (p * (1 - p₀)) ≤ f p := by
  have hppos : 0 < p := lt_of_lt_of_le hp₀ hpp₀
  have h1mp₀ : 0 < 1 - p₀ := by linarith
  have h1mp : 0 < 1 - p := by linarith
  have hanti := perco_ode_antitone p₀ hp₀ f hdiff hineq
  
  have hmono : (1 - f p) * (p / (1 - p)) ≤ (1 - f p₀) * (p₀ / (1 - p₀)) :=
    hanti ⟨le_refl p₀, hp₀1⟩ ⟨hpp₀, hp1⟩ hpp₀
  
  have hgp₀ : (1 - f p₀) * (p₀ / (1 - p₀)) ≤ p₀ / (1 - p₀) := by
    have hfac : 0 ≤ p₀ / (1 - p₀) := le_of_lt (div_pos hp₀ h1mp₀)
    nlinarith [hfac, hf0]
  have hg : (1 - f p) * (p / (1 - p)) ≤ p₀ / (1 - p₀) := le_trans hmono hgp₀
  
  have hgcl : (1 - f p) * p * (1 - p₀) ≤ p₀ * (1 - p) := by
    have hpos1 : 0 < (1 - p) * (1 - p₀) := mul_pos h1mp h1mp₀
    have hmul := mul_le_mul_of_nonneg_right hg (le_of_lt hpos1)
    have hL : (1 - f p) * (p / (1 - p)) * ((1 - p) * (1 - p₀))
        = (1 - f p) * p * (1 - p₀) := by
      field_simp
    have hR : p₀ / (1 - p₀) * ((1 - p) * (1 - p₀)) = p₀ * (1 - p) := by
      field_simp
    rwa [hL, hR] at hmul
  
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < p * (1 - p₀))]
  nlinarith [hgcl, mul_pos hppos h1mp₀]












theorem percolationEvent_subset_crossingEvent (n : ℕ) :
    percolationEvent d ⊆ crossingEvent d n := by
  intro ω hω
  rw [mem_percolationEvent] at hω
  rw [mem_crossingEvent]
  have hfin : (box d (n - 1)).Finite := box_finite d (n - 1)
  have hnsub : ¬ (StatMech.Lattice.cluster d ω (origin d) ⊆ box d (n - 1)) :=
    fun hsub => hω (hfin.subset hsub)
  rw [Set.not_subset] at hnsub
  obtain ⟨v, hv, hvnot⟩ := hnsub
  exact ⟨v, hv, hvnot⟩




theorem theta_le_crossProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    theta d p hp ≤ crossProb d p hp n :=
  measureReal_mono (percolationEvent_subset_crossingEvent n)





























theorem item1_meanfield_lower_bound (p : ℝ≥0) (hp : p ≤ 1)
    (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1)
    (f : ℕ → ℝ → ℝ)
    (hfval : ∀ n, f n (p : ℝ) = crossProb d p hp n)
    (hdiff : ∀ n, ∀ q ∈ Ico p₀ 1, DifferentiableAt ℝ (f n) q)
    (hineq : ∀ n, ∀ q ∈ Ioo p₀ 1, (1 / (q * (1 - q))) * (1 - f n q) ≤ deriv (f n) q)
    (hf0 : ∀ n, 0 ≤ f n p₀)
    (hpp₀ : p₀ ≤ (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htends : Tendsto (fun n => crossProb d p hp n) atTop (𝓝 (theta d p hp))) :
    ((p : ℝ) - p₀) / ((p : ℝ) * (1 - p₀)) ≤ theta d p hp := by
  
  have hbound : ∀ n, ((p : ℝ) - p₀) / ((p : ℝ) * (1 - p₀)) ≤ crossProb d p hp n := by
    intro n
    have := profile_ge_of_diffineq p₀ hp₀ hp₀1 (f n) (hdiff n) (hineq n) (hf0 n) hpp₀ hp1
    rwa [hfval n] at this
  
  exact ge_of_tendsto htends (Eventually.of_forall hbound)





















theorem susceptibility_finite (chi Sval phival : ℝ)
    (hchi : 0 ≤ chi) (hphi1 : phival < 1)
    (hself : chi ≤ Sval + phival * chi) :
    0 ≤ chi ∧ chi ≤ Sval / (1 - phival) := by
  have h1mphi : 0 < 1 - phival := by linarith
  refine ⟨hchi, ?_⟩
  
  rw [le_div_iff₀ h1mphi]
  nlinarith [hself]














theorem subcritical_exp_decay (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hS0 : origin d ∈ S) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L)
    (hstep : ∀ k, crossProb d p hp ((k + 1) * L)
      ≤ phi d p hp S * crossProb d p hp (k * L)) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) :=
  StatMech.Percolation.subcritical_decay p hp S hS0 hphi L hL hstep













theorem pc_le_tildePc
    (hpos : ∀ t : ℝ≥0, tildePc d < t → ∀ ht : t ≤ 1, 0 < theta d t ht) :
    pc d ≤ tildePc d := by
  
  
  refine csSup_le' ?_
  intro t ht
  obtain ⟨ht1, htheta⟩ := ht
  by_contra hcon
  rw [not_le] at hcon
  
  have := hpos t hcon ht1
  rw [htheta] at this
  exact lt_irrefl 0 this











theorem tildePc_le_pc
    (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
    tildePc d ≤ pc d := by
  refine csSup_le' ?_
  intro t ht
  
  have ht1 : t ≤ 1 := ht.choose
  
  have hmem : t ∈ subcriticalSet d := ⟨ht1, hzero t ht ht1⟩
  have hbdd : BddAbove (subcriticalSet d) := ⟨1, fun x hx => hx.1⟩
  exact le_csSup hbdd hmem






theorem bc_eq
    (hpos : ∀ t : ℝ≥0, tildePc d < t → ∀ ht : t ≤ 1, 0 < theta d t ht)
    (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
    pc d = tildePc d :=
  le_antisymm (pc_le_tildePc hpos) (tildePc_le_pc hzero)

end Sharpness

end StatMech
