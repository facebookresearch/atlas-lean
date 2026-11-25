/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.ForcedBurgersInitialValue
import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Uniform bounds for the forced Burgers construction

If the initial velocity is bounded in absolute value by `M` and the spatial
potential derivative is bounded by `A`, the actual constructed velocity is
bounded by `M + 2 * nu * A * t`. This is a conclusion, not an assumed growth
condition on the velocity. The proof compares the weighted heat profile with
both signs of its spatial derivative using the whole-line potential maximum
principle. Only the profile and its derivative need exponential growth.

The maximum-principle background is James Nolen, *Partial Differential Equations
and Diffusion Processes*, section 2.8,
https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The forcing convention is the Cole–Hopf identity of Gesztesy and Holden,
*The Cole–Hopf and Miura transformations revisited*, Lemmas 3.1–3.2,
https://arxiv.org/abs/solv-int/9812025.
-/

@[expose] public section

open Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel
open MathlibExt.Analysis.PDE.HeatWholeLine

namespace ColeHopf

private theorem growth_mul_time {u : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T C : ℝ}
    (hu : HasExpGrowthOnStrip u T) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc 0 T, |b t| ≤ C) :
    HasExpGrowthOnStrip (fun t x => b t * u t x) T := by
  obtain ⟨M,c,hM,hc,hu⟩ := hu
  refine ⟨C*M,c,mul_nonneg hC hM,hc,fun t ht x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (hb t ht) (hu t ht x) (abs_nonneg _) hC

/-- The actual forced Burgers velocity satisfies the uniform bound
`|u(t,x)| ≤ M + 2 * ν * A * t` throughout the closed strip, when `M` bounds the
initial velocity and `A` bounds the spatial potential derivative. No bound on
the constructed velocity or on the initial primitive is assumed. -/
theorem abs_forcedBurgersSolution_le
    {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T M A t : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀)
    (hM : 0 ≤ M) (hub : ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ C, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ C)
    (hA : 0 ≤ A) (hqb : ∀ s ∈ Icc 0 T, ∀ x, |deriv (q s) x| ≤ A)
    (ht : t ∈ Icc 0 T) (a x : ℝ) :
    |forcedBurgersSolution ν q u₀ a t x| ≤ M + 2 * ν * A * t := by
  let g := initialHeatProfile ν u₀ a
  let φ := potentialHeatSolution ν q g
  have hg : ContDiff ℝ 1 g := initialHeatProfile_contDiff hu ν a
  have hgg : HasExpGrowth g := initialHeatProfile_hasExpGrowth ⟨M,hub⟩ hν a
  have hgd : HasExpGrowth (deriv g) := initialHeatProfile_deriv_hasExpGrowth hu ⟨M,hub⟩ hν a
  have hqs (n : ℕ) (s : ℝ) : ContDiff ℝ n (q s) := by
    have hs : ContDiff ℝ ∞ (q s) := by
      simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
        hq.comp (contDiff_const.prodMk contDiff_id)
    exact hs.of_le (by simp)
  have hqc (k : ℕ) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2) (Icc 0 T ×ˢ univ) :=
    (hq.contDiff_iteratedDeriv_snd k).continuous.continuousOn
  have hqj (k : ℕ) : ∃ C, ∀ s ∈ Icc 0 T, ∀ y, |iteratedDeriv k (q s) y| ≤ C := by
    obtain ⟨C,hC⟩ := hb k
    refine ⟨C,fun s hs y => ?_⟩
    have he : |iteratedDeriv k (q s) y| ≤ ‖iteratedFDeriv ℝ k (Function.uncurry q) (s,y)‖ := by
      simpa only [Real.norm_eq_abs] using
        (hq.of_le (by simp : (k : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (s,y)
    exact he.trans (hC (s,y) ⟨hs,mem_univ y⟩)
  obtain ⟨Q,hQb⟩ := hqj 0
  simp only [iteratedDeriv_zero] at hQb
  have hQ : 0 ≤ Q := (abs_nonneg _).trans (hQb 0 ⟨le_rfl,hT⟩ 0)
  have hφc : ContinuousOn (Function.uncurry φ) (Icc 0 T ×ˢ univ) :=
    potentialHeatSolution_continuousOn hν.le hT hq.continuous.continuousOn hQ hQb hg.continuous hgg
  have hφdc : ContinuousOn (fun p : ℝ × ℝ => deriv (φ p.1) p.2) (Icc 0 T ×ˢ univ) :=
    potentialHeatSolution_deriv_continuousOn_of_contDiff hν hT hq.continuous.continuousOn
      hQ hQb hg hgg hgd
  have hφg : HasExpGrowthOnStrip φ T :=
    potentialHeatSolution_hasExpGrowthOnStrip hν.le hq.continuous.continuousOn hQ hQb
      hg.continuous hgg
  have hφdg : HasExpGrowthOnStrip (fun s y => deriv (φ s) y) T :=
    potentialHeatSolution_deriv_hasExpGrowthOnStrip_of_contDiff hν hT hq.continuous.continuousOn
      hQ hQb hg hgg hgd
  have hφs (s : ℝ) (hs : s ∈ Ioo 0 T) : ContDiff ℝ 3 (φ s) :=
    potentialHeatSolution_contDiff_space hν (fun r _ => hqs 3 r)
      (fun k _ => hqc k) (fun k _ => hqj k) hg.continuous hgg ⟨hs.1,hs.2.le⟩
  have hφp (s : ℝ) (hs : s ∈ Icc 0 T) (y : ℝ) : 0 < φ s y :=
    forcedBurgersProfile_pos hν hu ⟨M,hub⟩ hq hb hs a y
  have hφt (s : ℝ) (hs : s ∈ Ioo 0 T) (y : ℝ) :
      HasDerivAt (fun r => φ r y) (ν * iteratedDeriv 2 (φ s) y + q s y * φ s y) s := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      potentialHeatSolution_hasDerivAt_time_of_contDiff hν hq hb hg.continuous hgg hs y
  have hφdt (s : ℝ) (hs : s ∈ Ioo 0 T) (y : ℝ) :
      HasDerivAt (fun r => deriv (φ r) y)
        (ν * iteratedDeriv 3 (φ s) y + deriv (q s) y * φ s y + q s y * deriv (φ s) y) s := by
    have he := potentialHeatSolution_iteratedDeriv_hasDerivAt_time (n := 1) hν
      (fun r _ => hqs 3 r) (fun k _ => hqc k) (fun k _ => hqj k) hg.continuous hgg hs y
    have hp := deriv_fun_mul ((hqs 1 s).differentiable (by norm_num) y)
      ((hφs s hs).differentiable (by norm_num) y)
    simp only [iteratedDeriv_one, Nat.reduceAdd] at he
    change HasDerivAt (fun r => deriv (φ r) y)
      (ν * iteratedDeriv 3 (φ s) y + deriv (fun z => q s z * φ s z) y) s at he
    rw [hp] at he
    simpa only [add_assoc] using he
  let B := fun s => M + 2 * ν * A * s
  have hBc : Continuous B := by fun_prop
  have hB0 (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ B s := by
    have hs0 := hs.1
    dsimp [B]
    positivity
  have hBT (s : ℝ) (hs : s ∈ Icc 0 T) : |B s| ≤ B T := by
    rw [abs_of_nonneg (hB0 s hs)]
    dsimp [B]
    have hh := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 2*ν*A by positivity)
    linarith
  have hcmp (c : ℝ) (hc : |c| ≤ 2*ν) :
      c * deriv (φ t) x ≤ B t * φ t x := by
    apply le_of_potential_residual_le (u := fun s y => c * deriv (φ s) y)
      (v := fun s y => B s * φ s y)
      (ut := fun s y => c * (ν * iteratedDeriv 3 (φ s) y +
        deriv (q s) y * φ s y + q s y * deriv (φ s) y))
      (vt := fun s y => 2*ν*A * φ s y + B s * (ν * iteratedDeriv 2 (φ s) y + q s y * φ s y))
      (q := q) (K := Q) hν.le
      (continuousOn_const.mul hφdc) ((hBc.comp continuous_fst).continuousOn.mul hφc)
      (fun s hs y => contDiffAt_const.mul ((hφs s hs).deriv'.contDiffAt))
      (fun s hs y => contDiffAt_const.mul ((hφs s hs).of_le (by norm_num)).contDiffAt)
      (fun s hs y => (hφdt s hs y).const_mul c)
      (fun s hs y => ?_) (fun s hs y => ?_)
      (fun s hs y => (le_abs_self _).trans (hQb s ⟨hs.1.le,hs.2.le⟩ y))
      (growth_mul_time hφdg (abs_nonneg c) (fun _ _ => le_rfl))
      (growth_mul_time hφg (hB0 T ⟨hT,le_rfl⟩) hBT) (fun y => ?_) t ht x
    · have hB : HasDerivAt B (2*ν*A) s := by
        simpa only [mul_one, id_eq] using ((hasDerivAt_id s).const_mul (2*ν*A)).const_add M
      exact hB.mul (hφt s hs y)
    · have hcx : c * deriv (q s) y ≤ 2*ν*A :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul hc (hqb s ⟨hs.1.le,hs.2.le⟩ y) (abs_nonneg _) (by positivity))
      have hm := mul_le_mul_of_nonneg_right hcx (hφp s ⟨hs.1.le,hs.2.le⟩ y).le
      rw [iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
      rw [← iteratedDeriv_succ']
      nlinarith
    · have hinit : φ 0 = g := funext (potentialHeatSolution_initial ν q g)
      rw [hinit]
      have hd : 2*ν * deriv g y = -u₀ y * g y := by
        rw [(initialHeatProfile_hasDerivAt hu ν a y).deriv]
        field_simp [hν.ne']
        rfl
      have hgpos : 0 < g y := initialHeatProfile_pos ν u₀ a y
      have hab : |c * deriv g y| ≤ M * g y := calc
        |c * deriv g y| = |c| * |deriv g y| := abs_mul _ _
        _ ≤ (2*ν) * |deriv g y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = |2*ν * deriv g y| := by rw [abs_mul,abs_of_pos (by positivity : 0 < 2*ν)]
        _ = |u₀ y| * g y := by rw [hd,abs_mul,abs_neg,abs_of_pos hgpos]
        _ ≤ M * g y := mul_le_mul_of_nonneg_right (hub y) hgpos.le
      simpa [B] using (le_abs_self _).trans hab
  have hplus := hcmp (2*ν) (by rw [abs_of_pos (by positivity : 0 < 2*ν)])
  have hminus := hcmp (-(2*ν)) (by rw [abs_neg,abs_of_pos (by positivity : 0 < 2*ν)])
  have ha : |2*ν * deriv (φ t) x| ≤ B t * φ t x := abs_le.mpr ⟨by nlinarith, hplus⟩
  have hp := hφp t ht x
  change |-2 * ν * (deriv (φ t) x / φ t x)| ≤ B t
  rw [← mul_div_assoc, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  simpa only [neg_mul,abs_neg] using ha

/-- On a finite closed strip the actual forced Burgers velocity is uniformly
bounded; the bound is derived from the data and the spatial potential derivative. -/
theorem forcedBurgersSolution_boundedOnStrip
    {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ C, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ C) (a : ℝ) :
    ∃ C, ∀ t ∈ Icc 0 T, ∀ x, |forcedBurgersSolution ν q u₀ a t x| ≤ C := by
  obtain ⟨M,hM⟩ := hub
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨A,hA⟩ := hb 1
  have hqb (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) : |deriv (q t) x| ≤ A := by
    have he : |deriv (q t) x| ≤ ‖iteratedFDeriv ℝ 1 (Function.uncurry q) (t,x)‖ := by
      simpa only [iteratedDeriv_one,Real.norm_eq_abs] using
        (hq.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (t,x)
    exact he.trans (hA (t,x) ⟨ht,mem_univ x⟩)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hqb 0 ⟨le_rfl,hT⟩ 0)
  refine ⟨M+2*ν*A*T,fun t ht x => ?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2*ν*A by positivity)
  have hu := abs_forcedBurgersSolution_le hν hT hu hM0 hM hq hb hA0 hqb ht a x
  linarith

end ColeHopf
