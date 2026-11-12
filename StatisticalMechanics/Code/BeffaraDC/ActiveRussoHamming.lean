/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib
import Code.FK.ActiveEdgeRussoP
import Code.BeffaraDC.RussoHamming

open scoped BigOperators

namespace StatMech.BeffaraDC

open Finset
open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem active_fkg_cov {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) {f g : ConfigSpace G.edgeSet → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    activeMean G (fun _ => p) q f * activeMean G (fun _ => p) q g ≤
      activeMean G (fun _ => p) q (fun ω => f ω * g ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h := fkg_inequality
    (fun ω => (activeProb_pos G (fun _ => hp) (fun _ => hp1) hq0 ω).le)
    (activeProb_sum_eq_one G (fun _ => hp) (fun _ => hp1) hq0)
    (activeProb_FKGLatticeCondition G (fun _ => hp) (fun _ => hp1) hq) hf hg
  simpa only [activeMean, mul_comm] using h

lemma activeMean_indicator_hamming_zero (p q : ℝ)
    (A : Set (ConfigSpace G.edgeSet)) :
    activeMean G (fun _ => p) q
      (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) = 0 := by
  unfold activeMean
  refine Finset.sum_eq_zero fun ω _ => ?_
  classical
  change (A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) *
    activeProb G (fun _ => p) q ω = 0
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h, hammingToSet_eq_zero_of_mem A h]
    simp
  · rw [Set.indicator_of_notMem h]
    simp

lemma activeCov_numOpen_eq_sum (p q : ℝ) (f : ConfigSpace G.edgeSet → ℝ) :
    activeCov G (fun _ => p) q f (fun ω => (numOpen ω : ℝ)) =
      ∑ e : G.edgeSet,
        activeCov G (fun _ => p) q f (OSSS.Lindeberg.coord e) := by
  have hfun : (fun ω : ConfigSpace G.edgeSet => (numOpen ω : ℝ)) =
      (fun ω => ∑ e : G.edgeSet, OSSS.Lindeberg.coord e ω) := by
    funext ω
    rw [numOpen_eq_sum]
    rfl
  rw [hfun, activeCov_sum_right]

theorem active_prob_mul_mean_hamming_le_cov {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    activeProbOf G (fun _ => p) q A *
        activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ))
      ≤ activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
          (fun ω => (numOpen ω : ℝ)) := by
  have hfkg := active_fkg_cov G hp hp1 hq hA.indicator_monotone
    (numOpen_add_hamming_mono A)
  have hNH : activeMean G (fun _ => p) q
      (fun ω => (numOpen ω : ℝ) + (hammingToSet A ω : ℝ)) =
      activeMean G (fun _ => p) q (fun ω => (numOpen ω : ℝ)) +
        activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ)) :=
    activeMean_add G _ _ _ _
  have hprod : activeMean G (fun _ => p) q
      (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
        ((numOpen ω : ℝ) + (hammingToSet A ω : ℝ))) =
      activeMean G (fun _ => p) q
          (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ)) +
        activeMean G (fun _ => p) q
          (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
            (hammingToSet A ω : ℝ)) := by
    rw [← activeMean_add G]
    congr 1
    funext ω
    ring
  rw [hNH, hprod, activeMean_indicator_hamming_zero] at hfkg
  unfold activeProbOf activeCov
  nlinarith [hfkg]


theorem active_russoHamming {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    4 * activeProbOf G (fun _ => p) q A *
        activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ))
      ≤ deriv (fun x => activeProbOf G (fun _ => x) q A) p := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hderiv := (hasDerivAt_activeProbOf_p G hp hp1 hq0 A).deriv
  have hcov := active_prob_mul_mean_hamming_le_cov G hp hp1 hq A hA
  rw [activeCov_numOpen_eq_sum] at hcov
  have hsum_nonneg : 0 ≤ ∑ e : G.edgeSet,
      activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
        (OSSS.Lindeberg.coord e) := hcov.trans' (mul_nonneg
          (by
            unfold activeProbOf activeMean
            exact Finset.sum_nonneg fun ω _ => mul_nonneg
              (by by_cases h : ω ∈ A <;> simp [Set.indicator, h])
              (activeProb_pos G (fun _ => hp) (fun _ => hp1) hq0 ω).le)
          (by
            unfold activeMean
            exact Finset.sum_nonneg fun ω _ => mul_nonneg (Nat.cast_nonneg _) (activeProb_pos G (fun _ => hp) (fun _ => hp1) hq0 ω).le))
  have hquarter : p * (1 - p) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  rw [hderiv]
  have hden : 0 < p * (1 - p) := mul_pos hp (by linarith)
  rw [le_div_iff₀ hden]
  calc
    (4 * activeProbOf G (fun _ => p) q A *
        activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ))) *
          (p * (1 - p))
      = 4 * (p * (1 - p)) *
          (activeProbOf G (fun _ => p) q A *
            activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ))) := by ring
    _ ≤ 4 * (p * (1 - p)) *
        (∑ e : G.edgeSet, activeCov G (fun _ => p) q
          (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) := by
      gcongr
    _ ≤ ∑ e : G.edgeSet, activeCov G (fun _ => p) q
          (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e) := by
      nlinarith

theorem active_fkg_anticorr {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) {f g : ConfigSpace G.edgeSet → ℝ}
    (hf : Antitone f) (hg : Monotone g) :
    activeMean G (fun _ => p) q (fun ω => f ω * g ω) ≤
      activeMean G (fun _ => p) q f * activeMean G (fun _ => p) q g := by
  have hneg : Monotone (fun ω => -f ω) := fun _ _ h => neg_le_neg (hf h)
  have h := active_fkg_cov G hp hp1 hq hneg hg
  have hmneg : activeMean G (fun _ => p) q (fun ω => -f ω) =
      -activeMean G (fun _ => p) q f := by
    simpa using activeMean_const_mul G (fun _ => p) q (-1) f
  have hpneg : activeMean G (fun _ => p) q (fun ω => (-f ω) * g ω) =
      -activeMean G (fun _ => p) q (fun ω => f ω * g ω) := by
    rw [show (fun ω => (-f ω) * g ω) =
      (fun ω => (-1 : ℝ) * (f ω * g ω)) by funext ω; ring]
    simpa using activeMean_const_mul G (fun _ => p) q (-1)
      (fun ω => f ω * g ω)
  rw [hmneg, hpneg] at h
  nlinarith

theorem activeMean_antitoneOn {p₁ p₂ q : ℝ} (hp₁ : 0 < p₁)
    (hp₂ : p₂ < 1) (hq : 1 ≤ q) {f : ConfigSpace G.edgeSet → ℝ}
    (hf : Antitone f) :
    AntitoneOn (fun p => activeMean G (fun _ => p) q f) (Set.Icc p₁ p₂) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdiff : DifferentiableOn ℝ (fun p => activeMean G (fun _ => p) q f)
      (Set.Icc p₁ p₂) := by
    intro p hp
    exact (hasDerivAt_activeMean_p G (hp₁.trans_le hp.1)
      (hp.2.trans_lt hp₂) hq0 f).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc p₁ p₂)
    hdiff.continuousOn (hdiff.mono interior_subset)
  intro p hp
  rw [interior_Icc, Set.mem_Ioo] at hp
  have hp0 : 0 < p := hp₁.trans hp.1
  have hp1 : p < 1 := hp.2.trans hp₂
  rw [(hasDerivAt_activeMean_p G hp0 hp1 hq0 f).deriv]
  have hac := active_fkg_anticorr G hp0 hp1 hq hf numOpen_mono
  have hcov : activeCov G (fun _ => p) q f (fun ω => (numOpen ω : ℝ)) ≤ 0 := by
    unfold activeCov
    linarith
  rw [activeCov_numOpen_eq_sum] at hcov
  exact div_nonpos_of_nonpos_of_nonneg hcov (mul_nonneg hp0.le (by linarith))

theorem active_gronwall (q : ℝ) (A : Set (ConfigSpace G.edgeSet))
    (c : ℝ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : p₂ < 1)
    (hq : 0 < q) (hp : p₁ ≤ p₂)
    (hdiff : ∀ p ∈ Set.Icc p₁ p₂,
      c * activeProbOf G (fun _ => p) q A ≤
        deriv (fun x => activeProbOf G (fun _ => x) q A) p) :
    activeProbOf G (fun _ => p₁) q A ≤
      activeProbOf G (fun _ => p₂) q A * Real.exp (-c * (p₂ - p₁)) := by
  let θ := fun p => activeProbOf G (fun _ => p) q A
  have hθdiff : DifferentiableOn ℝ θ (Set.Icc p₁ p₂) := by
    intro p hp'
    exact (hasDerivAt_activeProbOf_p G (hp₁.trans_le hp'.1)
      (hp'.2.trans_lt hp₂) hq A).differentiableAt.differentiableWithinAt
  let u := fun p => θ p * Real.exp (-c * p)
  have hexpdiff : Differentiable ℝ (fun p : ℝ => Real.exp (-c * p)) := by
    fun_prop
  have hu : MonotoneOn u (Set.Icc p₁ p₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p₁ p₂)
      (hθdiff.continuousOn.mul
        (Real.continuous_exp.comp (by continuity)).continuousOn)
      ((hθdiff.mul hexpdiff.differentiableOn).mono interior_subset)
    intro p hp'
    rw [interior_Icc, Set.mem_Ioo] at hp'
    have hp0 : 0 < p := hp₁.trans hp'.1
    have hp1 : p < 1 := hp'.2.trans hp₂
    have hθ := hasDerivAt_activeProbOf_p G hp0 hp1 hq A
    have hlin : HasDerivAt (fun x : ℝ => -c * x) (-c) p := by
      simpa using (hasDerivAt_id p).const_mul (-c)
    have hexp := (Real.hasDerivAt_exp _).comp p hlin
    have hdu := hθ.mul hexp
    rw [hdu.deriv]
    have hi := hdiff p ⟨hp'.1.le, hp'.2.le⟩
    rw [hθ.deriv] at hi
    have he : 0 < Real.exp (-c * p) := Real.exp_pos _
    simp only [Function.comp_apply]
    nlinarith
  have hle := hu (Set.left_mem_Icc.mpr hp) (Set.right_mem_Icc.mpr hp) hp
  change θ p₁ * Real.exp (-c * p₁) ≤ θ p₂ * Real.exp (-c * p₂) at hle
  have he1 : 0 < Real.exp (-c * p₁) := Real.exp_pos _
  rw [show -c * (p₂ - p₁) = (-c * p₂) - (-c * p₁) by ring,
    Real.exp_sub, mul_div_assoc', le_div_iff₀ he1]
  exact hle


theorem active_russoHammingIntegrated {p₁ p₂ q : ℝ} (hp₁ : 0 < p₁)
    (hp₁₂ : p₁ < p₂) (hp₂ : p₂ < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    activeProbOf G (fun _ => p₁) q A ≤
      activeProbOf G (fun _ => p₂) q A *
        Real.exp (-4 * (p₂ - p₁) *
          activeMean G (fun _ => p₂) q (fun ω => (hammingToSet A ω : ℝ))) := by
  let H₂ := activeMean G (fun _ => p₂) q (fun ω => (hammingToSet A ω : ℝ))
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hgr := active_gronwall G q A (4 * H₂) hp₁ hp₂ hq0 hp₁₂.le ?_
  · rw [show -4 * (p₂ - p₁) * H₂ = -(4 * H₂) * (p₂ - p₁) by ring]
    exact hgr
  · intro p hp
    have hp0 : 0 < p := hp₁.trans_le hp.1
    have hp1 : p < 1 := hp.2.trans_lt hp₂
    have hrh := active_russoHamming G hp0 hp1 hq A hA
    have hanti := activeMean_antitoneOn G hp₁ hp₂ hq
      (hammingToSet_real_antitone A hA)
    have hH : H₂ ≤ activeMean G (fun _ => p) q
        (fun ω => (hammingToSet A ω : ℝ)) :=
      hanti hp ⟨hp₁₂.le, le_rfl⟩ hp.2
    have hprob : 0 ≤ activeProbOf G (fun _ => p) q A := by
      unfold activeProbOf activeMean
      exact Finset.sum_nonneg fun ω _ => mul_nonneg
        (by by_cases h : ω ∈ A <;> simp [Set.indicator, h])
        (activeProb_pos G (fun _ => hp0) (fun _ => hp1) hq0 ω).le
    calc
      4 * H₂ * activeProbOf G (fun _ => p) q A =
          4 * activeProbOf G (fun _ => p) q A * H₂ := by ring
      _ ≤ 4 * activeProbOf G (fun _ => p) q A *
          activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ)) := by
        gcongr
      _ ≤ deriv (fun x => activeProbOf G (fun _ => x) q A) p := hrh

end StatMech.BeffaraDC
