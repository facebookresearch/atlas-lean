/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Independence.Integration

/-!
# Kolmogorov's three-series theorem (sufficiency direction)

If `X₁, X₂, …` are independent real random variables and, for some `A > 0`,
with truncations `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}`, the three series
(1) `∑ₙ P(|Xₙ| > A)`,
(2) `∑ₙ E[Yₙ]`, and
(3) `∑ₙ Var(Yₙ)`
all converge, then `∑ₙ Xₙ` converges almost surely.

## Source

This formalizes the sufficiency direction of the target
"Theorem (Kolmogorov three-series theorem)" (Lecture 10,
Kolmogorov three-series theorem) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "Let `X₁, X₂, …` be
independent and fix `A > 0`. Write `Yᵢ = Xᵢ 1_{(|Xᵢ| ≤ A)}`. Then
`∑ Xᵢ` converges a.s. if and only if (1) `∑ P(|Xₙ| > A)` converges,
(2) `∑ E Yₙ` converges, (3) `∑ Var(Yₙ) < ∞`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean`
(`kolmogorov_three_series_theorem`) together with the helper file
`v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean`
(`ae_tendsto_sum_of_indep_centered_L1bdd`,
`eLpNorm_one_le_sqrt_integral_sq`).

## Scope

Only the sufficiency direction (conditions imply a.s. convergence) is
proved here. The necessity direction is **not** ported: in v1 it rests
on `summable_mean_and_variance_of_ae_tendsto_ax`, which is left
unproved in v1 (a symmetrization argument for the necessity of the
mean and variance series). Porting the necessity direction would
require proving that unproved v1 statement from scratch, which is
out of scope for this slice.

## Relation to Mathlib

Mathlib has no three-series theorem (searched for `three_series`,
`ThreeSeries`, and `three-series` in Mathlib and MathlibExt: no hits).
It does have the ingredients used here: the first Borel–Cantelli
lemma, `L¹`-bounded martingale convergence, and the variance of a sum
of independent variables.

## Main results

* `ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd`: partial
  sums of independent centered integrable variables with uniformly
  `L¹`-bounded partial sums converge almost surely (via martingale
  convergence for the partial-sum martingale).
* `ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_centered_of_indep_summableVar`:
  if the variances of the truncations are summable, the partial sums
  of the centered truncations converge a.s.
* `ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_truncated_of_conditions`:
  if the mean and variance series of the truncations are summable,
  the partial sums of the truncations converge a.s.
* `ProbabilityTheory.KolmogorovThreeSeries.kolmogorov_three_series_sufficiency`:
  the three-series sufficiency direction.

## Proof outline

Truncate, center, and apply martingale convergence: for the centered
truncations `Zₙ = Yₙ - E[Yₙ]`, independence kills the cross terms in
`E[(∑_{k ≤ n} Zₖ)²]`, so the variances add and the `L¹` norms of the
partial sums are bounded by `√(∑ Var(Yₙ))`. The partial sums of the
`Zₙ` form a martingale for the natural filtration, hence converge
a.s. by `L¹`-bounded martingale convergence. Adding back the
convergent mean series gives a.s. convergence of the truncated sums,
and the first Borel–Cantelli lemma says truncation eventually stops
changing anything a.s., so the original series converges a.s. too.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal
open scoped NNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- On a probability space, the `L¹` norm is dominated by the `L²` norm:
`‖f‖₁ ≤ ‖f‖₂`. -/
private lemma eLpNorm_one_le_two {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    [IsProbabilityMeasure μ] :
    eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf
  simp only [measure_univ, one_rpow, mul_one] at h
  exact h

/-- If `∫ ‖f‖² dμ ≤ C` for an `L²` function on a probability space, then
`‖f‖₁ ≤ √C`. -/
private lemma eLpNorm_one_le_sqrt_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) {C : ℝ}
    (h_int_sq : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ ≤ C) [IsProbabilityMeasure μ] :
    eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := eLpNorm_one_le_two hf.aestronglyMeasurable
  have h2 : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply ENNReal.ofReal_le_ofReal
    simp only [ENNReal.toReal_ofNat]
    rw [Real.sqrt_eq_rpow]
    show (∫ (a : Ω), ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ ≤ C ^ ((1 : ℝ) / 2)
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 from by norm_num]
    exact Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) h_int_sq (by norm_num)
  exact h1.trans h2

/-- Key step toward the Kolmogorov three-series theorem: if the `Zₙ` are
independent centered (mean zero) integrable random variables whose
partial sums `Sₙ = ∑_{k ≤ n} Zₖ` are uniformly bounded in `L¹`, then
`Sₙ` converges almost surely. This is proved by realizing `Sₙ` as a
martingale and applying the `L¹`-bounded martingale convergence
theorem. -/
theorem ae_tendsto_sum_of_indep_centered_L1bdd {Z : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ)
    (hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0)
    (hZ_int : ∀ n, Integrable (Z n) μ)
    {R : NNReal}
    (hZ_L1_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ range (n + 1), Z k ω) atTop (nhds c) := by
  set ℱ := Filtration.natural (β := fun _ : ℕ => ℝ) Z hZ_sm
  have sum_eq : ∀ n, (fun ω => ∑ k ∈ range (n + 1), Z k ω) = ∑ k ∈ range (n + 1), Z k := by
    intro n; ext ω; simp [Finset.sum_apply]
  have hS_int : ∀ n, Integrable (fun ω => ∑ k ∈ range (n + 1), Z k ω) μ := fun n =>
    integrable_finsetSum _ (fun k _ => hZ_int k)
  have hS_sm_m : ∀ n, StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ range (n + 1), Z k ω) := by
    intro n; rw [sum_eq]
    exact stronglyMeasurable_sum _ (fun k hk => by
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      exact (Filtration.stronglyAdapted_natural hZ_sm k).mono (ℱ.mono hkn))
  have hS_mart : Martingale (fun n ω => ∑ k ∈ range (n + 1), Z k ω) ℱ μ := by
    apply martingale_nat (fun n => hS_sm_m n) hS_int
    intro i
    have heq_add : (fun ω => ∑ k ∈ range (i + 2), Z k ω) =
        (fun ω => ∑ k ∈ range (i + 1), Z k ω) + Z (i + 1) := by
      ext ω; simp [sum_range_succ, Pi.add_apply]
    rw [heq_add]
    have hce := condExp_add (hS_int i) (hZ_int (i + 1)) (ℱ i : MeasurableSpace Ω)
    have hSi_ce : μ[fun ω => ∑ k ∈ range (i + 1), Z k ω | (ℱ i : MeasurableSpace Ω)] =
        fun ω => ∑ k ∈ range (i + 1), Z k ω :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hS_sm_m i) (hS_int i)
    have hZi1_ce : μ[Z (i + 1) | (ℱ i : MeasurableSpace Ω)] =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h := hZ_indep.condExp_natural_ae_eq_of_lt hZ_sm (show i < i + 1 by omega)
      simpa [hZ_mean (i + 1)] using h
    filter_upwards [hce, hZi1_ce] with ω hω1 hω3
    simp only [Pi.add_apply] at hω1
    rw [hSi_ce] at hω1
    linarith
  exact hS_mart.submartingale.exists_ae_tendsto_of_bdd (R := R) hZ_L1_bdd

end ProbabilityTheory

namespace ProbabilityTheory.KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The truncation `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` of the random variable `Xₙ` at
threshold `A`, i.e. `Yₙ(ω) = Xₙ(ω)` when `|Xₙ(ω)| ≤ A` and `0` otherwise.
This is the key construction in the Kolmogorov three-series theorem. -/
noncomputable def truncatedRV (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X n ω * Set.indicator {ω | |X n ω| ≤ A} 1 ω

/-- If the truncated variables have summable variances, then almost surely
the partial sums of the centered truncations converge:
`∑ (Yᵢ - E[Yᵢ])` converges a.s. -/
theorem ae_tendsto_centered_of_indep_summableVar [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, (truncatedRV X A i ω -
        ∫ ω', (X i ω') * Set.indicator {ω' | |X i ω'| ≤ A} 1 ω' ∂μ)) atTop (nhds c) := by
  open Finset ENNReal in
  have hmeas_trunc : Measurable (fun x : ℝ => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x) :=
    measurable_id.mul (Measurable.indicator measurable_one
      (measurableSet_le measurable_norm measurable_const))
  set m : ℕ → ℝ := fun n => ∫ ω', truncatedRV X A n ω' ∂μ
  set Z : ℕ → Ω → ℝ := fun n ω => truncatedRV X A n ω - m n
  have htrunc_norm : ∀ n ω, ‖truncatedRV X A n ω‖ ≤ A := by
    intro n ω; rw [Real.norm_eq_abs]; unfold truncatedRV
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    split_ifs with h
    · simp only [mul_one]; exact h
    · simp only [mul_zero, abs_zero]; exact hA.le
  have hZ_sm : ∀ n, StronglyMeasurable (Z n) := fun n =>
    (((hX_meas n).mul (measurable_one.indicator
      (measurableSet_le (hX_meas n).norm measurable_const))).sub measurable_const).stronglyMeasurable
  have hZ_bdd : ∀ n ω, ‖Z n ω‖ ≤ 2 * A := by
    intro n ω
    have h1 : ‖truncatedRV X A n ω‖ ≤ A := htrunc_norm n ω
    have h2 : ‖m n‖ ≤ A :=
      calc ‖m n‖ = ‖∫ ω', truncatedRV X A n ω' ∂μ‖ := rfl
        _ ≤ ∫ ω', ‖truncatedRV X A n ω'‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ _, A ∂μ := integral_mono_of_nonneg (ae_of_all μ (fun _ => norm_nonneg _))
            (integrable_const A) (ae_of_all μ (fun ω' => htrunc_norm n ω'))
        _ = A := by simp
    calc ‖Z n ω‖ = ‖truncatedRV X A n ω - m n‖ := rfl
      _ ≤ ‖truncatedRV X A n ω‖ + ‖m n‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add h1 h2
      _ = 2 * A := by ring
  have hZ_int : ∀ n, Integrable (Z n) μ := fun n =>
    (memLp_top_of_bound (hZ_sm n).aestronglyMeasurable (2 * A)
      (ae_of_all μ (hZ_bdd n))).integrable le_top
  have hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0 := by
    intro n
    have hint : Integrable (truncatedRV X A n) μ :=
      (memLp_top_of_bound ((hX_meas n).mul (measurable_one.indicator
        (measurableSet_le (hX_meas n).norm measurable_const))).aestronglyMeasurable A
        (ae_of_all μ (htrunc_norm n))).integrable le_top
    simp only [Z]
    rw [integral_sub hint (integrable_const _)]
    simp [m]
  have hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ := by
    have heq : Z = fun n => (fun x => x * Set.indicator {y : ℝ | |y| ≤ A} 1 x - m n) ∘ (X n) := by
      ext n ω
      simp only [Z, truncatedRV, Function.comp, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    rw [heq]
    exact hX_indep.comp _ (fun n => hmeas_trunc.sub measurable_const)
  have hZ_memLp : ∀ n, MemLp (Z n) 2 μ := fun n =>
    (memLp_top_of_bound (hZ_sm n).aestronglyMeasurable (2 * A)
      (ae_of_all μ (hZ_bdd n))).mono_exponent le_top
  have hVar_eq : ∀ n, variance (Z n) μ =
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ := by
    intro n
    have hasm : AEStronglyMeasurable (truncatedRV X A n) μ :=
      ((hX_meas n).mul (measurable_one.indicator
        (measurableSet_le (hX_meas n).norm measurable_const))).aestronglyMeasurable
    show variance (fun ω => truncatedRV X A n ω - m n) μ = _
    have heq : (fun ω => truncatedRV X A n ω - m n) =
        (fun ω => truncatedRV X A n ω + (-(m n))) := by
      ext; ring
    rw [heq, variance_add_const hasm]
    rfl
  set C := ∑' n, variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ
  have hC_nn : 0 ≤ C := tsum_nonneg (fun n => variance_nonneg _ _)
  have hR_bound : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤
      ENNReal.ofReal (Real.sqrt C) := by
    intro n
    have hS_sm : StronglyMeasurable (fun ω => ∑ k ∈ range (n + 1), Z k ω) := by
      have h := stronglyMeasurable_sum (range (n + 1)) (fun k _ => hZ_sm k)
      convert h using 1; ext ω; simp [Finset.sum_apply]
    have hS_memLp : MemLp (fun ω => ∑ k ∈ range (n + 1), Z k ω) 2 μ := by
      have hbdd : ∀ ω, ‖∑ k ∈ range (n + 1), Z k ω‖ ≤ (n + 1) * (2 * A) := by
        intro ω
        calc ‖∑ k ∈ range (n + 1), Z k ω‖ ≤ ∑ k ∈ range (n + 1), ‖Z k ω‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ range (n + 1), (2 * A) := Finset.sum_le_sum (fun k _ => hZ_bdd k ω)
          _ = (n + 1) * (2 * A) := by simp [mul_comm]
      exact (memLp_top_of_bound hS_sm.aestronglyMeasurable
        ((n + 1) * (2 * A)) (ae_of_all μ hbdd)).mono_exponent le_top
    have h_int_bound : ∫ x, ‖(fun ω => ∑ k ∈ range (n + 1), Z k ω) x‖ ^ (2 : ℝ) ∂μ ≤ C := by
      have hconv : (fun x => ‖(fun ω => ∑ k ∈ range (n + 1), Z k ω) x‖ ^ (2 : ℝ)) =
          fun x => ((∑ k ∈ range (n + 1), Z k x)) ^ 2 := by
        ext x
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast, sq, sq,
            Real.norm_eq_abs, abs_mul_abs_self]
      rw [hconv]
      have hmean_sum : ∫ ω, (∑ k ∈ range (n + 1), Z k ω) ∂μ = 0 := by
        rw [integral_finsetSum _ (fun k _ => hZ_int k)]
        exact Finset.sum_eq_zero (fun k _ => hZ_mean k)
      have haem : AEMeasurable (fun ω => ∑ k ∈ range (n + 1), Z k ω) μ :=
        hS_sm.aestronglyMeasurable.aemeasurable
      rw [← variance_of_integral_eq_zero haem hmean_sum]
      have hpw : Set.Pairwise (↑(range (n + 1))) (fun i j => (Z i) ⟂ᵢ[μ] (Z j)) :=
        fun i _ j _ hij => hZ_indep.indepFun hij
      rw [show (fun ω => ∑ k ∈ range (n + 1), Z k ω) = ∑ k ∈ range (n + 1), Z k from by
        ext ω; simp [Finset.sum_apply]]
      rw [IndepFun.variance_sum (fun k _ => hZ_memLp k) hpw]
      calc ∑ k ∈ range (n + 1), variance (Z k) μ
          = ∑ k ∈ range (n + 1),
              variance (fun ω => (X k ω) * Set.indicator {ω | |X k ω| ≤ A} 1 ω) μ :=
            Finset.sum_congr rfl (fun k _ => hVar_eq k)
        _ ≤ C := h3.sum_le_tsum _ (fun k _ => variance_nonneg _ _)
    exact ProbabilityTheory.eLpNorm_one_le_sqrt_integral_sq hS_memLp h_int_bound
  have hR_nn : (0 : ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg _
  obtain ⟨R, hR⟩ : ∃ R : NNReal, (R : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt C) :=
    ⟨⟨Real.sqrt C, hR_nn⟩, (ENNReal.ofReal_eq_coe_nnreal hR_nn).symm⟩
  have hR_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R := by
    intro n
    rw [hR]
    exact hR_bound n
  have h := ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd hZ_sm hZ_indep
    hZ_mean hZ_int hR_bdd
  filter_upwards [h] with ω ⟨c, hc⟩
  exact ⟨c, (Filter.tendsto_add_atTop_iff_nat 1).mp hc⟩

/-- If `∑ₙ P{|Xₙ| > A} < ∞`, then by the first Borel–Cantelli lemma, almost
surely the truncation eventually coincides with `Xₙ`. -/
theorem ae_eventually_truncation_eq [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {A : ℝ}
    (h1 : (∑' n, μ {ω | A < |X n ω|}) < ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, X n ω = truncatedRV X A n ω := by
  have h1' : (∑' n, μ {ω | A < |X n ω|}) ≠ ⊤ := h1.ne
  have hbc := ae_eventually_notMem h1'
  filter_upwards [hbc] with ω hω
  exact hω.mono fun n hn => by
    simp only [truncatedRV, Set.indicator_apply, Set.mem_ofPred_eq]
    have hle : |X n ω| ≤ A := not_lt.mp hn
    simp [hle, mul_one]

/-- If two sequences `f, g` of random variables agree eventually (almost
surely) and the partial sums of `f` converge almost surely, then the
partial sums of `g` also converge almost surely (to a possibly different
limit). -/
theorem ae_tendsto_of_ae_eventually_eq_and_ae_tendsto
    {f g : ℕ → Ω → ℝ}
    (hfg : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, f n ω = g n ω)
    (hf : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => f i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => g i ω)) atTop (nhds (S ω)) := by
  obtain ⟨Sf, hSf⟩ := hf
  have key : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, g i ω) atTop (nhds L) := by
    filter_upwards [hfg, hSf] with ω hev htend
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    set C := (∑ i ∈ Finset.range N, g i ω) - (∑ i ∈ Finset.range N, f i ω)
    refine ⟨C + Sf ω, ?_⟩
    have heq : ∀ n, N ≤ n →
        (∑ i ∈ Finset.range n, g i ω) = C + (∑ i ∈ Finset.range n, f i ω) := by
      intro n hn
      have : ∑ i ∈ Finset.Ico N n, g i ω = ∑ i ∈ Finset.Ico N n, f i ω := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hN i (Finset.mem_Ico.mp hi).1).symm
      rw [← Finset.sum_range_add_sum_Ico hn (f := fun i => g i ω),
          ← Finset.sum_range_add_sum_Ico hn (f := fun i => f i ω)]
      linarith
    exact (tendsto_const_nhds.add htend).congr'
      (eventually_atTop.mpr ⟨N, fun n hn => (heq n hn).symm⟩)
  classical
  exact ⟨fun ω => if h : ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n, g i ω)
      atTop (nhds L) then h.choose else 0,
    key.mono fun ω hω => by simp only; rw [dite_eq_left hω]; exact hω.choose_spec⟩

/-- If the means and variances of the truncations are summable then the
partial sums of the truncations `∑ Yᵢ` converge almost surely. This
combines the centered convergence result with the (deterministic)
convergence of the mean series. -/
theorem ae_tendsto_truncated_of_conditions [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (h2 : Summable fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncatedRV X A i ω)) atTop (nhds (S ω)) := by
  set m : ℕ → ℝ := fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ
  have h_mean_conv : Tendsto (fun n => ∑ i ∈ Finset.range n, m i) atTop
      (nhds (∑' i, m i)) := h2.hasSum.tendsto_sum_nat
  have h_centered : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, (truncatedRV X A i ω - m i)) atTop (nhds c) :=
    ae_tendsto_centered_of_indep_summableVar hX_meas hX_indep hA h3
  have key : ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun n =>
      ∑ i ∈ Finset.range n, truncatedRV X A i ω) atTop (nhds L) := by
    filter_upwards [h_centered] with ω ⟨c, hc⟩
    refine ⟨c + ∑' i, m i, ?_⟩
    have heq : ∀ n, ∑ i ∈ Finset.range n, truncatedRV X A i ω =
        (∑ i ∈ Finset.range n, (truncatedRV X A i ω - m i)) +
        (∑ i ∈ Finset.range n, m i) := by
      intro n
      simp only [Finset.sum_sub_distrib]
      ring
    exact (hc.add h_mean_conv).congr (fun n => (heq n).symm)
  classical
  exact ⟨fun ω => if h : ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n,
      truncatedRV X A i ω) atTop (nhds L) then h.choose else 0,
    key.mono fun ω hω => by simp only; rw [dite_eq_left hω]; exact hω.choose_spec⟩

/-- **Kolmogorov's three-series theorem (sufficiency direction).** Let
`X₁, X₂, …` be independent random variables and fix `A > 0`. Write
`Yᵢ = Xᵢ · 1_{|Xᵢ| ≤ A}` for the truncations. If the three series
(1) `∑ₙ P{|Xₙ| > A}`,
(2) `∑ₙ E[Yₙ]`, and
(3) `∑ₙ Var(Yₙ)`
all converge, then `∑ Xₙ` converges almost surely. -/
theorem kolmogorov_three_series_sufficiency
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun (m := fun _ => inferInstance) X μ)
    (A : ℝ) (hA : A > 0)
    (h1 : (∑' n, μ {ω | |X n ω| > A}) < ⊤)
    (h2 : Summable fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω))
      Filter.atTop (nhds (S ω)) := by
  have h1' : (∑' n, μ {ω | A < |X n ω|}) < ⊤ := h1
  have hev := ae_eventually_truncation_eq h1'
  have hY_tend := ae_tendsto_truncated_of_conditions hX_meas hX_indep hA h2 h3
  have hev' : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, truncatedRV X A n ω = X n ω := by
    filter_upwards [hev] with ω hω
    exact hω.mono (fun n hn => hn.symm)
  exact ae_tendsto_of_ae_eventually_eq_and_ae_tendsto hev' hY_tend

end ProbabilityTheory.KolmogorovThreeSeries

end
