/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.HeatWholeLine
public import MathlibExt.Analysis.PDE.PotentialHeatSmoothness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Whole-line comparison with a bounded-above potential

An exponential time factor and the positive-set heat maximum principle give
comparison for potential-heat residuals. Equations and actual derivatives are
required only at interior times; continuity supplies both time endpoints.
The fields have uniform exponential spatial growth and may change sign.

The maximum-principle background is Stanford Math 220B, *Heat Equation*,
Theorems 18 and 20, https://web.stanford.edu/class/math220b/handouts/heateqn.pdf,
and James Nolen, *Partial Differential Equations and Diffusion Processes*,
section 2.8, https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The weighted whole-line potential case is derived explicitly here.
-/

@[expose] public section

open Set Real
open scoped ContDiff

namespace MathlibExt.Analysis.PDE.HeatWholeLine

private theorem nonpos_of_potential_subsolution_closed {u ut q : ℝ → ℝ → ℝ}
    {ν T K : ℝ} (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ x,
      ut t x - ν * iteratedDeriv 2 (u t) x - q t x * u t x ≤ 0)
    (hq : ∀ t ∈ Ioc 0 T, ∀ x, q t x ≤ K)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ 0 := by
  let L := max K 0
  let w := fun t x => exp (-L * t) * u t x
  let wt := fun t x => exp (-L * t) * (ut t x - L * u t x)
  have hwc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn.mul hc
  have hwx (t : ℝ) (ht : t ∈ Ioc 0 T) (x : ℝ) : ContDiffAt ℝ 2 (w t) x :=
    contDiffAt_const.mul (hx t ht x)
  have hwt (t : ℝ) (htm : t ∈ Ioc 0 T) (x : ℝ) :
      HasDerivWithinAt (fun s => w s x) (wt t x) (Iic t) t := by
    convert (((hasDerivAt_id' t).const_mul (-L)).exp.hasDerivWithinAt.mul
      (ht t htm x)) using 1
    dsimp [w, wt]
    ring
  have hwsub (t : ℝ) (htm : t ∈ Ioc 0 T) (x : ℝ) (hp : 0 < w t x) :
      wt t x - ν * iteratedDeriv 2 (w t) x ≤ 0 := by
    have hu : 0 < u t x := (mul_pos_iff_of_pos_left (exp_pos _)).mp hp
    have hqL : q t x ≤ L := (hq t htm x).trans (le_max_left _ _)
    have hh : ut t x - ν * iteratedDeriv 2 (u t) x - L * u t x ≤ 0 := by
      nlinarith [hsub t htm x, mul_le_mul_of_nonneg_right hqL hu.le]
    change exp (-L * t) * (ut t x - L * u t x) -
      ν * iteratedDeriv 2 (fun y => exp (-L * t) • u t y) x ≤ 0
    rw [iteratedDeriv_fun_const_smul_field]
    simpa only [smul_eq_mul] using
      (show exp (-L * t) * (ut t x - L * u t x) -
        ν * (exp (-L * t) * iteratedDeriv 2 (u t) x) ≤ 0 by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (exp_pos (-L * t)).le hh])
  obtain ⟨M, c, hM, hc0, hg⟩ := hg
  have hwg : ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧
      ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ M * exp (c * |x|) := by
    refine ⟨M, c, hM, hc0, fun t ht x => ?_⟩
    have he : exp (-L * t) ≤ 1 := exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) ht.1)
    calc
      w t x ≤ exp (-L * t) * |u t x| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (exp_pos _).le
      _ ≤ exp (-L * t) * (M * exp (c * |x|)) :=
        mul_le_mul_of_nonneg_left (hg t ht x) (exp_pos _).le
      _ ≤ M * exp (c * |x|) := mul_le_of_le_one_left (by positivity) he
  have hw := nonpos_of_heat_subsolution_on_pos_of_le_exp hν hwc hwx hwt hwsub hwg
    (fun x => by simpa [w] using h₀ x)
  intro t ht x
  have hh := hw t ht x
  change exp (-L * t) * u t x ≤ 0 at hh
  exact nonpos_of_mul_nonpos_right hh (exp_pos _)

/-- A potential subsolution with a bounded-above potential and uniform exponential
strip growth is nonpositive when its initial data are. The equation and ordinary
time derivatives are required only on `(0,T)`; continuity supplies the terminal value. -/
theorem nonpos_of_potential_subsolution {u ut q : ℝ → ℝ → ℝ} {ν T K : ℝ}
    (hν : 0 ≤ ν) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (hsub : ∀ t ∈ Ioo 0 T, ∀ x,
      ut t x - ν * iteratedDeriv 2 (u t) x - q t x * u t x ≤ 0)
    (hq : ∀ t ∈ Ioo 0 T, ∀ x, q t x ≤ K)
    (hg : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x ≤ 0) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ 0 := by
  intro t htm x
  by_cases hT : 0 < T
  · have hle (s : ℝ) (hs : s ∈ Ico 0 T) : u s x ≤ 0 := by
      by_cases hs0 : s = 0
      · simpa [hs0] using h₀ x
      have hss : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hi {r : ℝ} (hr : r ∈ Ioc 0 s) : r ∈ Ioo 0 T := ⟨hr.1, hr.2.trans_lt hs.2⟩
      have hj {r : ℝ} (hr : r ∈ Icc 0 s) : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hs.2.le⟩
      obtain ⟨M, c, hM, hc0, hg⟩ := hg
      exact nonpos_of_potential_subsolution_closed hν
        (hc.mono (fun p hp => ⟨hj hp.1, hp.2⟩))
        (fun r hr => hx r (hi hr)) (fun r hr y => (ht r (hi hr) y).hasDerivWithinAt)
        (fun r hr => hsub r (hi hr)) (fun r hr => hq r (hi hr))
        ⟨M, c, hM, hc0, fun r hr => hg r (hj hr)⟩ h₀ s ⟨hss.le, le_rfl⟩ x
    have hcl : closure (Ico (0 : ℝ) T) = Icc 0 T := closure_Ico hT.ne
    have hct : ContinuousWithinAt (fun s => u s x) (closure (Ico 0 T)) t := by
      rw [hcl]
      exact (hc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, mem_univ x⟩)) t htm
    exact ContinuousWithinAt.closure_le (by simpa [hcl] using htm)
      (hct.mono subset_closure) continuousWithinAt_const hle
  · have ht0 : t = 0 := by linarith [htm.1, htm.2]
    simpa [ht0] using h₀ x

/-- Whole-line comparison for ordered potential-heat residuals and initial data.
The common potential is bounded above; both fields have uniform exponential growth.
Derivatives are required only at interior times, and source terms need not be equal. -/
theorem le_of_potential_residual_le {u v ut vt q : ℝ → ℝ → ℝ} {ν T K : ℝ} (hν : 0 ≤ ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hxu : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hxv : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (v t) x)
    (htu : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (htv : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => v s x) (vt t x) t)
    (hres : ∀ t ∈ Ioo 0 T, ∀ x,
      ut t x - ν * iteratedDeriv 2 (u t) x - q t x * u t x ≤
        vt t x - ν * iteratedDeriv 2 (v t) x - q t x * v t x)
    (hq : ∀ t ∈ Ioo 0 T, ∀ x, q t x ≤ K)
    (hgu : HasExpGrowthOnStrip u T) (hgv : HasExpGrowthOnStrip v T)
    (h₀ : ∀ x, u 0 x ≤ v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x ≤ v t x := by
  have hw := nonpos_of_potential_subsolution (u := fun t x => u t x - v t x)
    (ut := fun t x => ut t x - vt t x) (q := q) hν (hcu.sub hcv)
    (fun t ht x => (hxu t ht x).sub (hxv t ht x))
    (fun t ht x => (htu t ht x).sub (htv t ht x))
    (fun t ht x => by
      rw [iteratedDeriv_fun_sub (hxu t ht x) (hxv t ht x)]
      dsimp only
      nlinarith [hres t ht x]) hq (hgu.sub hgv) (fun x => sub_nonpos.mpr (h₀ x))
  exact fun t ht x => sub_nonpos.mp (hw t ht x)

/-- The whole-line potential-heat equation with a fixed source and initial data
has at most one classical solution in the uniform exponential-growth class.
No terminal derivative, source sign, or mild representation is assumed. -/
theorem eq_of_potential_equation {u v ut vt f q : ℝ → ℝ → ℝ} {ν T K : ℝ} (hν : 0 ≤ ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hxu : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hxv : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (v t) x)
    (htu : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (htv : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => v s x) (vt t x) t)
    (heu : ∀ t ∈ Ioo 0 T, ∀ x, ut t x - ν * iteratedDeriv 2 (u t) x - q t x * u t x = f t x)
    (hev : ∀ t ∈ Ioo 0 T, ∀ x, vt t x - ν * iteratedDeriv 2 (v t) x - q t x * v t x = f t x)
    (hq : ∀ t ∈ Ioo 0 T, ∀ x, q t x ≤ K)
    (hgu : HasExpGrowthOnStrip u T) (hgv : HasExpGrowthOnStrip v T)
    (h₀ : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x := by
  have huv := le_of_potential_residual_le hν hcu hcv hxu hxv htu htv
    (fun t ht x => (heu t ht x).trans (hev t ht x).symm |>.le) hq hgu hgv (fun x => (h₀ x).le)
  have hvu := le_of_potential_residual_le hν hcv hcu hxv hxu htv htu
    (fun t ht x => (hev t ht x).trans (heu t ht x).symm |>.le) hq hgv hgu (fun x => (h₀ x).ge)
  exact fun t ht x => le_antisymm (huv t ht x) (hvu t ht x)

end MathlibExt.Analysis.PDE.HeatWholeLine

namespace MathlibExt.Analysis.PDE.HeatKernel

open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatWholeLine

/-- Every classical solution with the same initial data and uniform exponential
growth equals the actual Volterra construction. Finite spatial C2 potential
regularity suffices, with no potential time derivative or initial-data derivative. -/
theorem eq_potentialHeatSolution_of_exp_growth
    {u ut q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioo 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (heq : ∀ t ∈ Ioo 0 T, ∀ x,
      ut t x = ν * iteratedDeriv 2 (u t) x + q t x * u t x)
    (hug : HasExpGrowthOnStrip u T) (h₀ : ∀ x, u 0 x = g x) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = potentialHeatSolution ν q g t x := by
  intro t htm x
  have hT : 0 ≤ T := htm.1.trans htm.2
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero, Function.uncurry_def] using hqc 0 (by omega)
  obtain ⟨Q, hQ⟩ := hqb 0 (by omega)
  simp only [iteratedDeriv_zero] at hQ
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans (hQ 0 ⟨le_rfl, hT⟩ 0)
  apply eq_of_potential_equation (q := q) (f := fun _ _ => 0)
    (v := potentialHeatSolution ν q g)
    (vt := fun t x => ν * iteratedDeriv 2 (potentialHeatSolution ν q g t) x +
      q t x * potentialHeatSolution ν q g t x) hν.le hc
    (potentialHeatSolution_continuousOn hν.le hT hq hQ0 hQ hg hgg) hx
    (fun s hs y => (potentialHeatSolution_contDiff_space (n := 2) hν hqs hqc hqb hg hgg
      ⟨hs.1, hs.2.le⟩).contDiffAt) ht
    (fun s hs y => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        potentialHeatSolution_hasDerivAt_time hν hqs hqc hqb hg hgg hs y)
    (fun s hs y => by rw [heq s hs y]; ring)
    (fun _ _ _ => by ring)
    (fun s hs y => (le_abs_self _).trans (hQ s ⟨hs.1.le, hs.2.le⟩ y)) hug
    (potentialHeatSolution_hasExpGrowthOnStrip hν.le hq hQ0 hQ hg hgg)
    (fun y => by simpa only [potentialHeatSolution_initial] using h₀ y) t htm x

end MathlibExt.Analysis.PDE.HeatKernel
