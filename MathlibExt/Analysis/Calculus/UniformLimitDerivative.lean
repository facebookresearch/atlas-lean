/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interchange of limits and derivatives on a closed interval

Mathlib's uniform-limit derivative theorem
(`hasDerivAt_of_tendstoUniformlyOn` in
`Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`) requires the set on
which the derivatives converge to be *open*: it concludes `HasDerivAt`
at interior points. It says nothing at the endpoints of a closed
interval, where the limit function need not be differentiable in the
full two-sided sense. This file adds the closed-interval version: if
`f n → g` pointwise on `[a, b]` and the derivatives `f' n` converge
uniformly on `[a, b]` to `g'`, then `g` has derivative `g' x` *within*
`[a, b]` at every `x ∈ [a, b]`, endpoints included, and `g'` is
continuous on `[a, b]`. The proof does not go through Mathlib's
open-set theorem; it uses the fundamental theorem of calculus, writing
the limit as `g x = g a + ∫ t in a..x, g' t` and differentiating the
integral within `[a, b]` (`integral_hasDerivWithinAt_right`).

## Main results

* `hasDerivWithinAt_of_tendstoUniformlyOn_Icc`: the closed-interval
  interchange of limits and derivatives.
* `hasDerivAt_of_tendstoUniformlyOn_Icc`: the interior corollary, where
  the within-derivative upgrades to an ordinary derivative.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, **Theorem (Interchange of
Limits and Derivatives)**, "Function Sequences section", and
`v1/Atlas/RealAnalysis/code/FunctionSequences/InterchangeLimits.lean`
(`uniform_limit_derivative`). The statement is the same as v1's, with
the binders renamed to Mathlib's `f` / `f'` / `g` / `g'` convention
(v1 calls the limit function `lim` and the limit derivative `g`).
-/

@[expose] public section

open Filter Topology Set MeasureTheory intervalIntegral

/-- **Interchange of limits and derivatives on a closed interval.** Let
`f n : ℝ → ℝ` be a sequence of functions on `[a, b]` such that each
`f n` is differentiable on `[a, b]` with derivative `f' n` continuous
on `[a, b]`. If `f' n → g'` uniformly on `[a, b]` and `f n x → g x`
pointwise on `[a, b]`, then the limit function `g` is differentiable
within `[a, b]` with derivative `g'`, including at the endpoints, and
`g'` is continuous on `[a, b]`. -/
theorem hasDerivWithinAt_of_tendstoUniformlyOn_Icc
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {f' : ℕ → ℝ → ℝ} {g' : ℝ → ℝ}
    {a b : ℝ} (hab : a < b)
    (hderiv : ∀ n, ∀ x ∈ Icc a b, HasDerivAt (f n) (f' n x) x)
    (hf'_cont : ∀ n, ContinuousOn (f' n) (Icc a b))
    (hf'_unif : TendstoUniformlyOn f' g' atTop (Icc a b))
    (hfg : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    (∀ x ∈ Icc a b, HasDerivWithinAt g (g' x) (Icc a b) x) ∧
      ContinuousOn g' (Icc a b) := by
  have hg'_cont : ContinuousOn g' (Icc a b) :=
    hf'_unif.continuousOn ((Eventually.of_forall hf'_cont).frequently)
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hint_n : ∀ n, ∀ x ∈ Icc a b, IntervalIntegrable (f' n) volume a x :=
    fun n x hx => ((hf'_cont n).mono (uIcc_subset_Icc ha_mem hx)).intervalIntegrable
  have hg'_int : ∀ x ∈ Icc a b, IntervalIntegrable g' volume a x :=
    fun x hx => (hg'_cont.mono (uIcc_subset_Icc ha_mem hx)).intervalIntegrable
  have hFTC : ∀ n, ∀ x ∈ Icc a b, f n x - f n a = ∫ t in a..x, f' n t := by
    intro n x hx
    have hderiv_uIcc : ∀ t ∈ uIcc a x, HasDerivAt (f n) (f' n t) t :=
      fun t ht => hderiv n t (uIcc_subset_Icc ha_mem hx ht)
    linarith [integral_eq_sub_of_hasDerivAt hderiv_uIcc (hint_n n x hx)]
  have hint_conv : ∀ x ∈ Icc a b,
      Tendsto (fun n => ∫ t in a..x, f' n t) atTop (nhds (∫ t in a..x, g' t)) := by
    intro x hx
    have hax : a ≤ x := hx.1
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hba_pos : (0 : ℝ) < b - a + 1 := by linarith
    have hunif := Metric.tendstoUniformlyOn_iff.mp hf'_unif
      (ε / (b - a + 1)) (div_pos hε hba_pos)
    rw [Filter.eventually_atTop] at hunif
    obtain ⟨N, hN⟩ := hunif
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← integral_sub (hint_n n x hx) (hg'_int x hx)]
    calc ‖∫ t in a..x, (f' n t - g' t)‖
        ≤ ∫ t in a..x, ‖f' n t - g' t‖ := norm_integral_le_integral_norm hax
      _ ≤ ∫ t in a..x, (ε / (b - a + 1)) := by
          apply integral_mono_on hax
          · exact (((hf'_cont n).sub hg'_cont).mono
              (uIcc_subset_Icc ha_mem hx)).norm.intervalIntegrable
          · exact _root_.intervalIntegrable_const
          · intro t ht
            have ht_mem : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hx.2⟩
            have h := hN n hn t ht_mem
            rw [Real.dist_eq] at h
            rw [norm_sub_rev]
            exact le_of_lt h
      _ = (x - a) * (ε / (b - a + 1)) := by
          simp [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ (b - a) * (ε / (b - a + 1)) := by
          apply mul_le_mul_of_nonneg_right
          · linarith [hx.2]
          · exact le_of_lt (div_pos hε hba_pos)
      _ < ε := by
          calc (b - a) * (ε / (b - a + 1))
              < (b - a + 1) * (ε / (b - a + 1)) := by
                apply mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hba_pos)
            _ = ε := by field_simp
  have hlim_eq : ∀ x ∈ Icc a b, g x - g a = ∫ t in a..x, g' t := by
    intro x hx
    have h1 : Tendsto (fun n => f n x - f n a) atTop (nhds (g x - g a)) :=
      (hfg x hx).sub (hfg a ha_mem)
    have h2 : (fun n => f n x - f n a) = (fun n => ∫ t in a..x, f' n t) :=
      funext (fun n => hFTC n x hx)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hint_conv x hx)
  refine ⟨fun x hx => ?_, hg'_cont⟩
  have hFTC2 : HasDerivWithinAt (fun u => ∫ t in a..u, g' t) (g' x) (Icc a b) x := by
    have : Fact (x ∈ Icc a b) := ⟨hx⟩
    exact integral_hasDerivWithinAt_right (hg'_int x hx)
      (hg'_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
      (hg'_cont.continuousWithinAt hx)
  have heq : ∀ u ∈ Icc a b, g u = g a + ∫ t in a..u, g' t := by
    intro u hu; linarith [hlim_eq u hu]
  have hFTC3 : HasDerivWithinAt (fun u => g a + ∫ t in a..u, g' t) (0 + g' x) (Icc a b) x :=
    (hasDerivWithinAt_const x (Icc a b) (g a)).add hFTC2
  rw [zero_add] at hFTC3
  exact hFTC3.congr (fun u hu => heq u hu) (heq x hx)

/-- Interior corollary: at `x ∈ (a, b)` the within-derivative upgrades
to an ordinary derivative. -/
theorem hasDerivAt_of_tendstoUniformlyOn_Icc
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {f' : ℕ → ℝ → ℝ} {g' : ℝ → ℝ}
    {a b : ℝ} (hab : a < b)
    (hderiv : ∀ n, ∀ x ∈ Icc a b, HasDerivAt (f n) (f' n x) x)
    (hf'_cont : ∀ n, ContinuousOn (f' n) (Icc a b))
    (hf'_unif : TendstoUniformlyOn f' g' atTop (Icc a b))
    (hfg : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x := by
  intro x hx
  exact (hasDerivWithinAt_of_tendstoUniformlyOn_Icc hab hderiv hf'_cont hf'_unif hfg).1
    x (Ioo_subset_Icc_self hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
