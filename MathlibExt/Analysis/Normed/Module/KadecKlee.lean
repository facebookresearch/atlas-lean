/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import MathlibExt.Analysis.Normed.Module.WeakConvergence
import Mathlib.Tactic.Linarith

/-!
# Kadec–Klee property in uniformly convex spaces

In a uniformly convex normed space, weak convergence together with
convergence of the norms implies convergence in norm: if `u n`
converges weakly to `x` and `‖u n‖ → ‖x‖`, then `u n → x` in norm.
This is the Kadec–Klee (or Radon–Riesz) property. The proof is the
standard one: pick a norming functional `f` for `x` by Hahn–Banach,
so `f (u n) → ‖x‖`; uniform convexity then forces the normalized
sequence `‖u n‖⁻¹ • u n` to converge in norm to `x / ‖x‖`, and
rescaling gives the result. No completeness hypothesis is needed.

This formulation uses real continuous linear functionals (`StrongDual ℝ E`)
and `toWeakSpace ℝ E`. The norming-functional squeeze uses the order on real
functional values. Mathlib's `UniformConvexSpace E` is a property of the
seminormed additive group and has no scalar-field parameter. Real inner product
spaces have the required instance (`InnerProductSpace.toUniformConvexSpace`),
so this includes the real inner-product case. The separate module
`MathlibExt.Analysis.InnerProductSpace.RadonRiesz` treats inner product spaces
with `RCLike` scalars. This file does not directly state a complex-dual formulation.

These results are new consequences of uniform convexity and Hahn–Banach.
The archived `v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`
provides related inner-product material, including continuity, Bessel's inequality
and Parseval's identity. Those targets supply context; they do not state the
uniformly convex Kadec–Klee theorem proved here. The weak-topology conversions
reuse `MathlibExt.Analysis.Normed.Module.WeakConvergence`.

## Main declarations

* `tendsto_of_forall_tendsto_and_tendsto_norm` : the main theorem, in
  the all-functionals form of weak convergence.
* `tendsto_of_tendsto_weakSpace_and_tendsto_norm` : the same theorem
  in Mathlib's `toWeakSpace` form.
* `tendsto_iff_forall_tendsto_and_tendsto_norm` : the iff form.
* `tendsto_iff_tendsto_weakSpace_and_tendsto_norm` : the iff form in
  `toWeakSpace` form.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.KadecKlee

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

-- The `UniformConvexSpace` instance is used only via typeclass search in the
-- proof of the unit-sphere case below, which the unused-variables linter
-- does not see; silence it for that one theorem.
set_option linter.unusedSectionVars false in
/-- The unit-sphere case of the Kadec–Klee property: weak convergence
plus convergence of the norms to `1` implies norm convergence, when
the limit has norm `1`. The normalized sequence is compared with `x`
by uniform convexity, and the error `|‖u n‖ - 1|` is controlled
separately. -/
private theorem tendsto_of_forall_tendsto_and_tendsto_norm_of_norm_eq_one
    {u : ℕ → E} {x : E} (hx : ‖x‖ = 1)
    (hweak : ∀ f : StrongDual ℝ E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 1)) :
    Tendsto u atTop (𝓝 x) := by
  obtain ⟨f, hf_norm, hf_x⟩ := exists_dual_vector ℝ x (by rw [hx]; norm_num)
  have hfx : f x = 1 := by simpa [hx] using hf_x
  -- The normalized sequence. At `u n = 0` it is `0` (since `0⁻¹ = 0` in
  -- `ℝ`); all the norm-`1` facts below are only needed where `u n ≠ 0`.
  set a : ℕ → E := fun n => (‖u n‖)⁻¹ • u n with ha_def
  have ha_norm_le : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    by_cases hn : u n = 0
    · simp [ha_def, hn]
    · have hnorm_ne : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
      rw [ha_def, norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hnorm_ne]
  have ha_norm : ∀ {n}, u n ≠ 0 → ‖a n‖ = 1 := by
    intro n hn
    have hnorm_ne : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
    rw [ha_def, norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hnorm_ne]
  -- Eventually `u n ≠ 0`, since `‖u n‖ → 1`.
  have hev : ∀ᶠ n in atTop, u n ≠ 0 := by
    have h := hnorm.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    filter_upwards [h] with n hn hzero
    rw [hzero, norm_zero] at hn
    exact absurd hn (by norm_num)
  -- The norming functional converges to `1` on the normalized sequence.
  have ha_weak : Tendsto (fun n => f (a n)) atTop (𝓝 1) := by
    have hprod : Tendsto (fun n => (‖u n‖)⁻¹ * f (u n)) atTop (𝓝 1) := by
      have h := (hnorm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).mul (hweak f)
      simpa [hfx] using h
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards [hev] with n hn
    rw [ha_def, map_smul, smul_eq_mul]
  -- The norms `‖a n + x‖` converge to `2`, by squeezing with `f`.
  have hsum : Tendsto (fun n => ‖a n + x‖) atTop (𝓝 2) := by
    have hf_sum : Tendsto (fun n => f (a n + x)) atTop (𝓝 2) := by
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have h := ha_weak.add h1
      have heq : (fun n => f (a n + x)) = fun n => f (a n) + f x := by
        funext n
        exact map_add f (a n) x
      rw [heq, hfx]
      simpa only [one_add_one_eq_two] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hf_sum tendsto_const_nhds
    · intro n
      calc f (a n + x) ≤ |f (a n + x)| := le_abs_self _
        _ = ‖f (a n + x)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖f‖ * ‖a n + x‖ := f.le_opNorm _
        _ = ‖a n + x‖ := by rw [hf_norm, one_mul]
    · intro n
      calc ‖a n + x‖ ≤ ‖a n‖ + ‖x‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by gcongr; exacts [ha_norm_le n, hx.le]
        _ = 2 := by norm_num
  -- Conclude by the `ε`–`δ` definition of convergence, via uniform convexity.
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ :=
    UniformConvexSpace.uniform_convex (E := E) (show (0 : ℝ) < ε / 2 by linarith)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hsum δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hnorm (ε / 2) (half_pos hε)
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp hnorm (1 / 2) (by norm_num)
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hsum_n : 2 - δ < ‖a n + x‖ := by
    have h := hN₁ n hn₁
    rw [Real.dist_eq] at h
    have h' := abs_lt.mp h
    linarith
  have hnorm_n : |‖u n‖ - 1| < ε / 2 := by
    have h := hN₂ n hn₂
    rwa [Real.dist_eq] at h
  have hpos_n : (1 / 2 : ℝ) < ‖u n‖ := by
    have h := hN₃ n hn₃
    rw [Real.dist_eq] at h
    have h' := abs_lt.mp h
    linarith
  have hu_ne : u n ≠ 0 := fun hzero => by
    rw [hzero, norm_zero] at hpos_n
    norm_num at hpos_n
  -- The normalized sequence is `ε / 2`-close to `x`, by uniform convexity.
  have hax : ‖a n - x‖ < ε / 2 := by
    by_contra hcon
    push Not at hcon
    have hle := huc (ha_norm hu_ne) hx hcon
    linarith
  have hun : u n = ‖u n‖ • a n := by
    have h1 : ‖u n‖ • a n = (‖u n‖ * ‖u n‖⁻¹) • u n := by
      rw [ha_def, smul_smul]
    rw [h1, mul_inv_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < ‖u n‖)), one_smul]
  rw [dist_eq_norm]
  have hsplit : u n - x = (‖u n‖ - 1) • a n + (a n - x) := by
    conv_lhs => rw [hun]
    rw [sub_smul, one_smul]
    abel
  rw [hsplit]
  calc ‖(‖u n‖ - 1) • a n + (a n - x)‖
      ≤ ‖(‖u n‖ - 1) • a n‖ + ‖a n - x‖ := norm_add_le _ _
    _ = |‖u n‖ - 1| + ‖a n - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, ha_norm hu_ne, mul_one]
    _ < ε / 2 + ε / 2 := by linarith [hnorm_n, hax]
    _ = ε := by ring

/-- **Kadec–Klee property, all-functionals form.** If `f (u n) → f x`
for every continuous linear functional `f` and `‖u n‖ → ‖x‖`, then
`u n → x` in norm. -/
theorem tendsto_of_forall_tendsto_and_tendsto_norm {u : ℕ → E} {x : E}
    (hweak : ∀ f : StrongDual ℝ E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [dist_eq_norm] using hnorm
  · set r : ℝ := ‖x‖ with hr_def
    have hr : 0 < r := norm_pos_iff.mpr hx0
    have hy : ‖r⁻¹ • x‖ = 1 := by
      rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hr.ne']
    have hweak_v : ∀ f : StrongDual ℝ E,
        Tendsto (fun n => f (r⁻¹ • u n)) atTop (𝓝 (f (r⁻¹ • x))) := by
      intro f
      have h := (hweak f).const_mul r⁻¹
      simpa [map_smul, smul_eq_mul] using h
    have hnorm_v : Tendsto (fun n => ‖r⁻¹ • u n‖) atTop (𝓝 1) := by
      have heq : (fun n => ‖r⁻¹ • u n‖) = fun n => r⁻¹ * ‖u n‖ := by
        funext n
        rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      rw [heq]
      have h := hnorm.const_mul r⁻¹
      simpa [inv_mul_cancel₀ hr.ne'] using h
    have hv := tendsto_of_forall_tendsto_and_tendsto_norm_of_norm_eq_one (E := E)
      hy hweak_v hnorm_v
    have h := hv.const_smul r
    simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h

/-- **Kadec–Klee property, `toWeakSpace` form.** -/
theorem tendsto_of_tendsto_weakSpace_and_tendsto_norm {u : ℕ → E} {x : E}
    (h : Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E x)))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖)) :
    Tendsto u atTop (𝓝 x) :=
  tendsto_of_forall_tendsto_and_tendsto_norm
    (MathlibExt.Analysis.Normed.Module.WeakConvergence.forall_tendsto_of_tendsto_weakSpace
      (𝕜 := ℝ) h) hnorm

/-- **Kadec–Klee iff, all-functionals form.** Norm convergence is
equivalent to weak convergence (in the all-functionals form) together
with convergence of the norms. -/
theorem tendsto_iff_forall_tendsto_and_tendsto_norm {u : ℕ → E} {x : E} :
    Tendsto u atTop (𝓝 x) ↔
      (∀ f : StrongDual ℝ E, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) ∧
        Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖) := by
  refine ⟨fun h => ⟨fun f => (f.continuous.tendsto x).comp h,
    (continuous_norm.tendsto x).comp h⟩, fun h => ?_⟩
  exact tendsto_of_forall_tendsto_and_tendsto_norm h.1 h.2

/-- **Kadec–Klee iff, `toWeakSpace` form.** -/
theorem tendsto_iff_tendsto_weakSpace_and_tendsto_norm {u : ℕ → E} {x : E} :
    Tendsto u atTop (𝓝 x) ↔
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop
        (𝓝 (toWeakSpace ℝ E x)) ∧
        Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖) := by
  refine ⟨fun h =>
    ⟨MathlibExt.Analysis.Normed.Module.WeakConvergence.tendsto_weakSpace_of_forall_tendsto
      (𝕜 := ℝ) (fun f => (f.continuous.tendsto x).comp h),
    (continuous_norm.tendsto x).comp h⟩, fun h => ?_⟩
  exact tendsto_of_tendsto_weakSpace_and_tendsto_norm h.1 h.2

end MathlibExt.Analysis.Normed.Module.KadecKlee
