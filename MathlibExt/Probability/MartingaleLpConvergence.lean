/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# `L^p` convergence of martingales

For `1 < p < ∞`, a martingale whose `L^p` norms are uniformly bounded
converges almost surely and in `L^p` to its limit process.

## Source

This formalizes the target "Theorem (`L^p` convergence theorem)"
(Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`:

* "If `X_n` is a martingale with `sup E|X_n|^p < ∞` where `p > 1` then
  `X_n → X` a.s. and in `L^p`."

The v1 formalization is
`v1/Atlas/TheoryOfProbability/code/MartingaleLpConvergence.lean`
(`martingale_Lp_convergence_ae`). It is stated there for submartingales,
with the key step `unifIntegrable_p_at_p_of_submartingale` left as a
`Sorry`: a submartingale with uniformly bounded `L^p` norms is claimed
to be uniformly integrable in `L^p`. That claim is false as stated:
on a probability space, the moving bumps
`f_n = n ^ (1 / p) * 1_{[0, 1 / n]}` have `L^p` norm `1` but are not
uniformly integrable in `L^p`. This file therefore proves the theorem
for martingales (as in the book), by a different route: an `L^p`-bounded
martingale is uniformly integrable in `L¹`, so Mathlib's `L¹` martingale
convergence theorem represents it as the conditional-expectation
martingale of its limit process, and `L^p` convergence of that
conditional-expectation martingale follows from a truncation argument.

## Main results

* `MeasureTheory.Martingale.tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd`:
  a martingale with uniformly bounded `L^p` norms, `1 < p < ∞`,
  converges a.e. to its limit process and converges to it in `L^p`.

## Proof outline

The `L¹` uniform integrability of an `L^p`-bounded family follows from
Hölder's inequality on restricted measures. For the `L^p` convergence
of a conditional-expectation martingale, truncate the limit `g` at
level `k`: the truncated martingales converge in `L^p` because their
terms are uniformly bounded (Vitali's theorem), and the truncation
error is controlled by the `L^p` contraction property of conditional
expectation.
-/

@[expose] public section

open scoped MeasureTheory NNReal ENNReal Topology
open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- If the `L^p` norms of `f n` on every restricted measure decay like
`C * μ s ^ r` for some `r > 0`, then `f` is uniformly integrable in `L^p`. -/
private lemma unifIntegrable_of_eLpNorm_restrict_le {p : ℝ≥0∞} {C : ℝ≥0} {r : ℝ}
    (hr : 0 < r) {f : ℕ → Ω → ℝ}
    (h : ∀ n (s : Set Ω), eLpNorm (f n) p (μ.restrict s) ≤ C * μ s ^ r) :
    UnifIntegrable f p μ := by
  rw [unifIntegrable_iff]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · refine ⟨1, one_pos, fun n s _ => ?_⟩
    rw [hεtop]
    exact le_top
  by_cases hC : C = 0
  · refine ⟨1, one_pos, fun n s _ => ?_⟩
    have h0 := h n s
    rw [hC] at h0
    have h0' : eLpNorm (f n) p (μ.restrict s) ≤ 0 := by simpa using h0
    exact h0'.trans zero_le
  · -- The constant `C + 1` is nonzero and finite.
    have hC1ne : (↑C + 1 : ℝ≥0∞) ≠ 0 := ne_of_gt (by positivity)
    have hC1top : (↑C + 1 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
    have hδpos : 0 < (ε / (↑C + 1)) ^ (1 / r) :=
      ENNReal.rpow_pos_of_nonneg (ENNReal.div_pos hε.ne' hC1top)
        (div_nonneg zero_le_one hr.le)
    have hδtop : (ε / (↑C + 1)) ≠ ⊤ := ENNReal.div_ne_top hεtop hC1ne
    have hrpow : ((ε / (↑C + 1)) ^ (1 / r)) ^ r = ε / (↑C + 1) := by
      have h := ENNReal.rpow_mul (ε / (↑C + 1)) (1 / r) r
      rw [div_mul_cancel₀ (1 : ℝ) hr.ne', ENNReal.rpow_one] at h
      exact h.symm
    set δ : ℝ≥0∞ := (ε / (↑C + 1)) ^ (1 / r) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact ENNReal.rpow_pos_of_nonneg (ENNReal.div_pos hε.ne' hC1top)
        (div_nonneg zero_le_one hr.le)
    have hδr : δ ^ r = ε / (↑C + 1) := by
      rw [hδdef]
      exact hrpow
    refine ⟨δ, hδpos, fun n s hs => ?_⟩
    calc eLpNorm (f n) p (μ.restrict s) ≤ ↑C * μ s ^ r := h n s
      _ ≤ ↑C * δ ^ r :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hs hr.le) zero_le
      _ = ↑C * (ε / (↑C + 1)) := by rw [hδr]
      _ ≤ ε := by
        calc ↑C * (ε / (↑C + 1)) ≤ (↑C + 1) * (ε / (↑C + 1)) := by
              gcongr
              exact le_add_of_nonneg_right zero_le_one
          _ = ε := by
            rw [← mul_div_assoc, mul_comm ((↑C + 1 : ℝ≥0∞)) ε]
            exact ENNReal.mul_div_cancel_right hC1ne hC1top

/-- An `L^p`-bounded family, `1 < p < ∞`, is uniformly integrable in `L¹`.
This is the corrected form of the `L^p` uniform-integrability step: the
bound gives uniform integrability in the strictly smaller exponent `1`,
not in `L^p` itself. -/
private lemma uniformIntegrable_one_of_eLpNorm_bdd {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ⊤)
    {f : ℕ → Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {R : ℝ≥0} (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    UniformIntegrable f 1 μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := hp.le
  refine ⟨?_, R, fun n => (eLpNorm_le_eLpNorm_of_exponent_le hp1).trans (hbdd n)⟩
  refine unifIntegrable_of_eLpNorm_restrict_le (p := 1) (C := R)
    (r := 1 - 1 / p.toReal) ?_ ?_
  · have h1p : (1 : ℝ) < p.toReal := by
      have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).mpr hp
      rwa [ENNReal.toReal_one] at h
    have hp_pos : 0 < p.toReal := by linarith
    exact sub_pos.mpr ((div_lt_one hp_pos).mpr h1p)
  · intro n s
    calc eLpNorm (f n) 1 (μ.restrict s)
        ≤ eLpNorm (f n) p (μ.restrict s) *
            (μ.restrict s) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1
            ((hf n).mono_measure Measure.restrict_le_self)
      _ = eLpNorm (f n) p (μ.restrict s) * μ s ^ (1 - 1 / p.toReal) := by
        simp only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
      _ ≤ ↑R * μ s ^ (1 - 1 / p.toReal) := by
        gcongr
        exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hbdd n)

omit [IsProbabilityMeasure μ] in
/-- The conditional-expectation martingale of an almost-everywhere bounded
function converges to it in `L^p`, for `1 ≤ p < ∞`. This is the bounded
case of `L^p` convergence of conditional expectations, proved with
Vitali's theorem: the conditional expectations are uniformly integrable
in `L^p` because they are uniformly bounded. -/
private lemma tendsto_eLpNorm_condExp_of_ae_bound [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ⊤)
    {g : Ω → ℝ} (hg_int : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) {C : ℝ} (hC : 0 ≤ C)
    (hg_bdd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - g) p μ) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hg_memLp : MemLp g p μ := by
    have hbdd : eLpNorm g p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C :=
      eLpNorm_le_of_ae_bound hg_int.aestronglyMeasurable hg_bdd
    exact lt_of_le_of_lt hbdd (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top μ Set.univ))
      ENNReal.ofReal_lt_top)
  have hcond_bdd : ∀ n, ∀ᵐ ω ∂μ, ‖μ[g | ℱ n] ω‖ ≤ C :=
    fun n => ae_bdd_norm_condExp_of_ae_bdd_norm hg_bdd
  have hUI : UnifIntegrable (fun n => μ[g | ℱ n]) p μ := by
    refine unifIntegrable_of_eLpNorm_restrict_le (p := p) (C := ⟨C, hC⟩)
      (r := 1 / p.toReal) ?_ ?_
    · have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
      positivity
    · intro n s
      have hbound : ∀ᵐ ω ∂(μ.restrict s), ‖μ[g | ℱ n] ω‖ ≤ C :=
        ae_restrict_of_ae (hcond_bdd n)
      have h1 : eLpNorm (μ[g | ℱ n]) p (μ.restrict s) ≤
          (μ.restrict s) Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C :=
        eLpNorm_le_of_ae_bound
          ((stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable.mono_measure
            Measure.restrict_le_self) hbound
      rw [Measure.restrict_apply_univ, inv_eq_one_div, mul_comm,
        ENNReal.ofReal_eq_coe_nnreal hC] at h1
      exact h1
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop (𝓝 (g ω)) := by
    have h : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop
        (𝓝 ((μ[g | ⨆ n, ℱ n]) ω)) :=
      tendsto_ae_condExp g
    have hle : ⨆ n, ℱ n ≤ m0 := iSup_le fun n => ℱ.le n
    have hcond : μ[g | ⨆ n, ℱ n] = g := condExp_of_stronglyMeasurable hle hgmeas hg_int
    simpa [hcond] using h
  exact tendsto_Lp_finite_of_tendsto_ae hp hp_top
    (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
    hg_memLp hUI hae

omit [IsProbabilityMeasure μ] in
/-- Truncation of `g` at level `k`: `g` cut off to `0` outside `{‖g‖ ≤ k}`. -/
private noncomputable def truncAt (g : Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => if ‖g ω‖ ≤ (k : ℝ) then g ω else 0

omit [IsProbabilityMeasure μ] in
/-- Truncation at level `k` converges to `g` in `L^p`, for `1 ≤ p < ∞`. -/
private lemma tendsto_eLpNorm_trunc_sub_of_memLp [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ⊤)
    {g : Ω → ℝ} (hg : MemLp g p μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun k : ℕ => eLpNorm (truncAt g k - g) p μ) atTop (𝓝 0) := by
  have htrunc_meas : ∀ k, StronglyMeasurable[⨆ n, ℱ n] (truncAt g k) := by
    intro k
    have hmeas : StronglyMeasurable[⨆ n, ℱ n]
        (fun ω => if ‖g ω‖ ≤ (k : ℝ) then g ω else 0) := by
      refine hgmeas.ite ?_ stronglyMeasurable_zero
      have hpre : MeasurableSet[⨆ n, ℱ n] (g ⁻¹' Metric.closedBall (0 : ℝ) (k : ℝ)) :=
        hgmeas.measurable measurableSet_closedBall
      have hset : g ⁻¹' Metric.closedBall (0 : ℝ) (k : ℝ) = {ω | ‖g ω‖ ≤ (k : ℝ)} := by
        ext ω
        simp [Metric.mem_closedBall, dist_zero_right]
      rw [hset] at hpre
      exact hpre
    exact hmeas
  have htrunc_ae : ∀ k, AEStronglyMeasurable (truncAt g k) μ := fun k =>
    ((htrunc_meas k).mono (iSup_le fun n => ℱ.le n)).aestronglyMeasurable
  have htrunc_le : ∀ k ω, ‖truncAt g k ω‖ ≤ ‖g ω‖ := by
    intro k ω
    by_cases h : ‖g ω‖ ≤ (k : ℝ)
    · have h1 : truncAt g k ω = g ω := by simp only [truncAt, ite_eq_left h]
      rw [h1]
    · have h0 : truncAt g k ω = 0 := by simp only [truncAt, ite_eq_right h]
      rw [h0, norm_zero]
      exact norm_nonneg _
  have hUI : UnifIntegrable (fun k => truncAt g k - g) p μ := by
    have hUI2 : UnifIntegrable (fun _ : ℕ => fun ω => 2 * g ω) p μ :=
      unifIntegrable_const hp hp_top (hg.const_mul 2)
    refine hUI2.ae_mono (fun k => (htrunc_ae k).sub hg.aestronglyMeasurable) (fun k => ?_)
    filter_upwards with ω
    calc ‖(truncAt g k - g) ω‖ₑ ≤ ‖truncAt g k ω‖ₑ + ‖g ω‖ₑ := by
          rw [Pi.sub_apply]
          calc ‖truncAt g k ω - g ω‖ₑ ≤ ‖truncAt g k ω‖ₑ + ‖-g ω‖ₑ := enorm_add_le _ _
            _ = ‖truncAt g k ω‖ₑ + ‖g ω‖ₑ := by rw [enorm_neg]
      _ ≤ ‖g ω‖ₑ + ‖g ω‖ₑ := by
        gcongr
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using htrunc_le k ω)
      _ = ‖(2 : ℝ) * g ω‖ₑ := by
        rw [enorm_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.enorm_natCast]
        exact_mod_cast (two_mul (‖g ω‖ₑ)).symm
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun k => (truncAt g k - g) ω) atTop (𝓝 0) := by
    filter_upwards with ω
    have hev : ∀ᶠ k in atTop, truncAt g k ω = g ω := by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖g ω‖
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hle : ‖g ω‖ ≤ (k : ℝ) := hN.le.trans hk'
      simp only [truncAt, ite_eq_left hle]
    exact tendsto_const_nhds.congr'
      (hev.mono fun k hk => by simp [Pi.sub_apply, hk])
  have hzero : MemLp (0 : Ω → ℝ) p μ := by
    have h := hg.sub hg
    rwa [sub_self] at h
  simpa using tendsto_Lp_finite_of_tendsto_ae (f := fun k => truncAt g k - g)
    (g := (0 : Ω → ℝ)) hp hp_top
    (fun k => (htrunc_ae k).sub hg.aestronglyMeasurable) hzero hUI hae

omit [IsProbabilityMeasure μ] in
/-- The conditional-expectation martingale of an `L^p` function converges
to it in `L^p`, for `1 ≤ p < ∞`. The proof truncates `g` at level `k`,
uses the bounded case for each truncation, and controls the truncation
error by the `L^p` contraction property of conditional expectation. -/
private lemma tendsto_eLpNorm_condExp_of_memLp [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ⊤)
    {g : Ω → ℝ} (hg : MemLp g p μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - g) p μ) atTop (𝓝 0) := by
  have hg_int : Integrable g μ := hg.integrable hp
  have htrunc_meas : ∀ k, StronglyMeasurable[⨆ n, ℱ n] (truncAt g k) := by
    intro k
    have hmeas : StronglyMeasurable[⨆ n, ℱ n]
        (fun ω => if ‖g ω‖ ≤ (k : ℝ) then g ω else 0) := by
      refine hgmeas.ite ?_ stronglyMeasurable_zero
      have hpre : MeasurableSet[⨆ n, ℱ n] (g ⁻¹' Metric.closedBall (0 : ℝ) (k : ℝ)) :=
        hgmeas.measurable measurableSet_closedBall
      have hset : g ⁻¹' Metric.closedBall (0 : ℝ) (k : ℝ) = {ω | ‖g ω‖ ≤ (k : ℝ)} := by
        ext ω
        simp [Metric.mem_closedBall, dist_zero_right]
      rw [hset] at hpre
      exact hpre
    exact hmeas
  have htrunc_ae : ∀ k, AEStronglyMeasurable (truncAt g k) μ := fun k =>
    ((htrunc_meas k).mono (iSup_le fun n => ℱ.le n)).aestronglyMeasurable
  have htrunc_bdd : ∀ k, ∀ᵐ ω ∂μ, ‖truncAt g k ω‖ ≤ (k : ℝ) := by
    intro k
    filter_upwards with ω
    by_cases h : ‖g ω‖ ≤ (k : ℝ)
    · have h1 : truncAt g k ω = g ω := by simp only [truncAt, ite_eq_left h]
      rw [h1]
      exact h
    · have h0 : truncAt g k ω = 0 := by simp only [truncAt, ite_eq_right h]
      rw [h0, norm_zero]
      exact Nat.cast_nonneg k
  have htrunc_int : ∀ k, Integrable (truncAt g k) μ := fun k =>
    Integrable.of_bound (htrunc_ae k) (k : ℝ) (htrunc_bdd k)
  have htrunc : Tendsto (fun k => eLpNorm (truncAt g k - g) p μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_trunc_sub_of_memLp hp hp_top hg hgmeas
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  obtain ⟨k, hk⟩ :=
    ((ENNReal.tendsto_nhds_zero.mp htrunc) (ε / 3) hε3).exists
  have hconv_k : Tendsto (fun n => eLpNorm (μ[truncAt g k | ℱ n] - truncAt g k) p μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_condExp_of_ae_bound hp hp_top (htrunc_int k) (htrunc_meas k)
      (Nat.cast_nonneg k) (htrunc_bdd k)
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp hconv_k) (ε / 3) hε3)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hsub : μ[g | ℱ n] - μ[truncAt g k | ℱ n] =ᵐ[μ] μ[g - truncAt g k | ℱ n] :=
    (condExp_sub hg_int (htrunc_int k) _).symm
  have hfirst : eLpNorm (μ[g | ℱ n] - μ[truncAt g k | ℱ n]) p μ ≤ ε / 3 := by
    rw [eLpNorm_congr_ae hsub]
    refine (eLpNorm_condExp_le_eLpNorm _ hp).trans ?_
    have hneg : (g - truncAt g k) = -(truncAt g k - g) := by
      ext ω
      simp [Pi.sub_apply, Pi.neg_apply]
    rw [hneg, eLpNorm_neg]
    exact hk
  have heq : (μ[g | ℱ n] - g) =
      ((μ[g | ℱ n] - μ[truncAt g k | ℱ n]) + (μ[truncAt g k | ℱ n] - truncAt g k) +
        (truncAt g k - g)) := by
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq]
  calc eLpNorm ((μ[g | ℱ n] - μ[truncAt g k | ℱ n]) + (μ[truncAt g k | ℱ n] - truncAt g k) +
          (truncAt g k - g)) p μ
      ≤ eLpNorm ((μ[g | ℱ n] - μ[truncAt g k | ℱ n]) + (μ[truncAt g k | ℱ n] - truncAt g k)) p μ +
          eLpNorm (truncAt g k - g) p μ :=
        eLpNorm_add_le hp
    _ ≤ (eLpNorm (μ[g | ℱ n] - μ[truncAt g k | ℱ n]) p μ +
          eLpNorm (μ[truncAt g k | ℱ n] - truncAt g k) p μ) + eLpNorm (truncAt g k - g) p μ :=
        add_le_add_left (eLpNorm_add_le hp) _
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add (add_le_add hfirst (hN n hn)) hk
    _ = ε := ENNReal.add_thirds ε

/-- **The `L^p` martingale convergence theorem.** If `f` is a martingale
with uniformly bounded `L^p` norms for some `1 < p < ∞`, then `f`
converges almost surely to its limit process, and the convergence holds
in `L^p`. -/
theorem Martingale.tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd {p : ℝ≥0∞} {R : ℝ≥0}
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hmart : Martingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω))) ∧
      Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) p μ) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := hp.le
  have hf_ae : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hmart.submartingale.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
  have hR1 : ∀ n, eLpNorm (f n) 1 μ ≤ R := fun n =>
    (eLpNorm_le_eLpNorm_of_exponent_le hp1).trans (hbdd n)
  have hUI1 : UniformIntegrable f 1 μ :=
    uniformIntegrable_one_of_eLpNorm_bdd hp hp_top hf_ae hbdd
  have hae := hmart.submartingale.ae_tendsto_limitProcess hR1
  have hX_memLp : MemLp (ℱ.limitProcess f μ) p μ :=
    hmart.submartingale.memLp_limitProcess hbdd
  have hX_meas : StronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess f μ) :=
    Filtration.stronglyMeasurable_limitProcess
  have hrepr : ∀ n, f n =ᵐ[μ] μ[ℱ.limitProcess f μ | ℱ n] := fun n =>
    hmart.ae_eq_condExp_limitProcess hUI1 n
  refine ⟨hae, ?_⟩
  have hconv := tendsto_eLpNorm_condExp_of_memLp hp1 hp_top hX_memLp hX_meas
  refine hconv.congr (fun n => eLpNorm_congr_ae ?_)
  filter_upwards [hrepr n] with ω hω
  simp [Pi.sub_apply, hω]

end MeasureTheory
