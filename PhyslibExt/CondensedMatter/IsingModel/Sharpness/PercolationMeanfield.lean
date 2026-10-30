/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SubcriticalDecay
public import MathlibExt.Probability.Percolation.ConnectionsInsideSet
public import MathlibExt.Probability.Percolation.Theta

/-!
# Mean-field lower bound and critical points for Bernoulli percolation

Integration of the Duminil-Copin–Tassion differential inequality, the mean-field lower bound `θ(p) ≥
(p - p̃_c)/(p(1 - p̃_c))`, and comparison of `p_c` with `p̃_c`.

## i. Overview

If `f' ≥ (1/(p(1 - p))) (1 - f)` on `(p₀, 1)` and `f(p₀) ≥ 0`, then `(1 - f(p)) p/(1 - p)` is
antitone, giving `f(p) ≥ (p - p₀)/(p(1 - p₀))`. Applied to the crossing probabilities of boxes and
passing to the limit gives the mean-field bound for `θ`.

`p_c ≤ p̃_c` follows from `θ > 0` above `p̃_c`, and `p̃_c ≤ p_c` from `θ = 0` on the set defining
`p̃_c`. See also `Percolation.pc_le_tildePc` and `Percolation.tildePc_le_pc` in
`MathlibExt.Probability.Percolation.Sharpness`, which prove the same comparisons from different
hypotheses.

## ii. Key results

- `profile_ge_of_diffineq` : integration of the differential inequality
- `item1_meanfield_lower_bound` : the mean-field lower bound for `θ`
- `pc_le_tildePc` : `p_c ≤ p̃_c`
- `tildePc_le_pc` : `p̃_c ≤ p_c`
- `bc_eq` : `p_c = p̃_c`

## iii. Table of contents

- A. The differential inequality
- B. The mean-field lower bound
- C. Critical points

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Lattice
open StatMech.Percolation

variable {d : ℕ}

/-! ## A. The differential inequality -/

lemma perco_ode_antitone (p₀ : ℝ) (hp₀ : 0 < p₀) (f : ℝ → ℝ)
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
        exact ((hasDerivAt_const p (1 : ℝ)).sub hd.hasDerivAt).congr_deriv (by simp)
      have hb : HasDerivAt (fun p : ℝ => p / (1 - p)) (1 / (1 - p) ^ 2) p := by
        have hnum : HasDerivAt (fun p : ℝ => p) 1 p := hasDerivAt_id p
        have hden : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by
          exact ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).congr_deriv (by simp)
        have := hnum.div hden h1mp
        convert this using 1
        field_simp
        ring
      exact ha.mul hb
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
      simp only [Pi.sub_apply, id_eq]
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

lemma profile_ge_of_diffineq (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₀1 : p₀ < 1) (f : ℝ → ℝ)
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

/-! ## B. The mean-field lower bound -/

lemma percolationEvent_subset_crossingEvent (n : ℕ) :
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

lemma theta_le_crossProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    theta d p hp ≤ crossProb d p hp n :=
  measureReal_mono (percolationEvent_subset_crossingEvent n)

/-- The mean-field lower bound `θ(p) ≥ (p - p₀)/(p(1 - p₀))` from the differential inequality for
crossing probabilities. Reference: H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of
the phase transition for Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016)
725–745. -/
lemma item1_meanfield_lower_bound (p : ℝ≥0) (hp : p ≤ 1)
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

/-! ## C. Critical points -/

lemma susceptibility_finite (chi Sval phival : ℝ)
    (hchi : 0 ≤ chi) (hphi1 : phival < 1)
    (hself : chi ≤ Sval + phival * chi) :
    0 ≤ chi ∧ chi ≤ Sval / (1 - phival) := by
  have h1mphi : 0 < 1 - phival := by linarith
  refine ⟨hchi, ?_⟩
  rw [le_div_iff₀ h1mphi]
  nlinarith [hself]

/-- `p_c ≤ p̃_c` when `θ` is positive above `p̃_c`. See also `Percolation.pc_le_tildePc`
(MathlibExt), stated with hypotheses on `θ(1)` and on `(p̃_c, 1)`. -/
lemma pc_le_tildePc
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

/-- `p̃_c ≤ p_c` when `θ` vanishes on the set defining `p̃_c`. See also `Percolation.tildePc_le_pc`
(MathlibExt), stated with exponential decay of crossing probabilities. -/
lemma tildePc_le_pc
    (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
    tildePc d ≤ pc d := by
  refine csSup_le' ?_
  intro t ht
  have ht1 : t ≤ 1 := ht.choose
  have hmem : t ∈ subcriticalSet d := ⟨ht1, hzero t ht ht1⟩
  have hbdd : BddAbove (subcriticalSet d) := ⟨1, fun x hx => hx.1⟩
  exact le_csSup hbdd hmem

lemma bc_eq
    (hpos : ∀ t : ℝ≥0, tildePc d < t → ∀ ht : t ≤ 1, 0 < theta d t ht)
    (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
    pc d = tildePc d :=
  le_antisymm (pc_le_tildePc hpos) (tildePc_le_pc hzero)

end Sharpness

end StatMech
