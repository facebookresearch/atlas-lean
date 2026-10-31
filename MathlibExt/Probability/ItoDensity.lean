/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegral
public import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Density of elementary integrands among progressive integrands

Every progressive process `H` with `E ∫_0^t H_u² du < ∞` is the `L²(P ⊗ du)`-limit on
`(0, t] × Ω` of elementary (simple predictable) integrands, so it is Itô-approximable and the Itô
isometry and the martingale property of `MathlibExt.Probability.ItoIntegral` apply to it
(Karatzas–Shreve 1991, Lemma 3.2.4 and Proposition 3.2.6).

The approximation follows Karatzas–Shreve. First `H` is truncated at level `M` (Mathlib's
`ProbabilityTheory.truncation`, which keeps the values in `(-M, M]` and sets the others to `0`);
the truncations converge to `H` by dominated convergence. Then the truncated process is replaced
on each interval `(t_k, t_{k+1}]` of the uniform partition `t_k = k t / (n + 1)` of `[0, t]` by its
average over the previous interval `[t_{k-1}, t_k]` (and by `0` on the first interval). Because
the process is progressive, the average is `F t_k`-measurable, so this is an elementary
integrand; the averages converge to the truncated process for almost every time by the Lebesgue
differentiation theorem, and in `L²(P ⊗ du)` by bounded convergence. Karatzas–Shreve average
over a sliding window `[u - 1/m, u]` and then discretize the resulting continuous process; the
delayed averages used here do both steps at once.

## Main definitions

* `ProbabilityTheory.delayedAverage hH M t n`: the elementary integrand equal on
  `(t_k, t_{k+1}]` to the average of the truncation of `H` at level `M` over `[t_{k-1}, t_k]`.

## Main results

* `MeasureTheory.LocallyIntegrable.ae_tendsto_average_Icc`: Lebesgue differentiation along
  shrinking intervals that need not contain the point, provided the point stays within a fixed
  multiple of the length from the interval.
* `ProbabilityTheory.IsProgressive.measurable_toNNReal`: a progressive process is jointly
  measurable.
* `ProbabilityTheory.IsProgressive.measurable_average_Icc`: averages over `[a, b]` of a
  progressive process are `F T`-measurable for `b ≤ T`.
* `ProbabilityTheory.tendsto_integrandDist_delayedAverage`,
  `ProbabilityTheory.tendsto_integrandDist_truncation`: the two approximation steps.
* `ProbabilityTheory.isItoApproximable_of_isProgressive`: **density of elementary integrands**.
* `ProbabilityTheory.lintegral_itoIntegral_sq_of_isProgressive`: the **Itô isometry** for
  progressive integrands.
* `ProbabilityTheory.martingale_itoIntegral_of_isProgressive`: the Itô integral of a progressive
  integrand is an `F`-martingale.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 3.2 (Lemma 3.2.4, Proposition 3.2.6, Proposition 3.2.10).
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal ProbabilityTheory

/-- **Lebesgue differentiation along shrinking off-center intervals.** For a locally integrable
`f : ℝ → ℝ`, for almost every `u`, the averages of `f` over intervals `[a n, b n]` converge to
`f u` whenever the lengths `b n - a n > 0` tend to `0` and the distance from `u` to the midpoint
of `[a n, b n]` is at most twice the length. -/
theorem MeasureTheory.LocallyIntegrable.ae_tendsto_average_Icc {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ u, ∀ a b : ℕ → ℝ, (∀ᶠ n in atTop, a n < b n) →
      (∀ᶠ n in atTop, |u - (a n + b n) / 2| ≤ 2 * (b n - a n)) →
      Tendsto (fun n ↦ b n - a n) atTop (𝓝 0) →
      Tendsto (fun n ↦ ⨍ x in Set.Icc (a n) (b n), f x) atTop (𝓝 (f u)) := by
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 4).ae_tendsto_average
    hf] with u hu
  intro a b hab hdist hlen
  refine hu.comp ((VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, fun ε hε ↦ ?_⟩)
  · filter_upwards [hab, hdist] with n h1 h2
    rw [Real.Icc_eq_closedBall]
    refine IsUnifLocDoublingMeasure.closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
    rw [Real.dist_eq]
    linarith
  · have h3 : Tendsto (fun n ↦ (5 / 2) * (b n - a n)) atTop (𝓝 0) := by
      simpa using hlen.const_mul (5 / 2)
    filter_upwards [hab, hdist, h3.eventually (gt_mem_nhds hε)] with n h1 h2 h4
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq]
    rw [abs_le] at h2 ⊢
    constructor <;> nlinarith [hx.1, hx.2]

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A progressive process is jointly measurable in `(u, ω)` (reading `u : ℝ` through
`Real.toNNReal`). -/
theorem IsProgressive.measurable_toNNReal {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) : Measurable fun p : ℝ × Ω ↦ H p.1.toNNReal p.2 := by
  have hN : ∀ N : ℕ, Measurable fun p : ℝ × Ω ↦ H (min p.1.toNNReal N) p.2 := by
    intro N
    have h1 := hH (N : ℝ≥0)
    have hle : (inferInstance : MeasurableSpace (Set.Iic (N : ℝ≥0))).prod (F N) ≤
        (inferInstance : MeasurableSpace (Set.Iic (N : ℝ≥0))).prod mΩ :=
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le _))
    have h2 : Measurable fun p : Set.Iic (N : ℝ≥0) × Ω ↦ H p.1 p.2 := h1.mono hle le_rfl
    have h3 : Measurable fun p : ℝ × Ω ↦
        ((⟨min p.1.toNNReal N, min_le_right _ _⟩ : Set.Iic (N : ℝ≥0)), p.2) :=
      ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk.prodMk
        measurable_snd
    exact h2.comp h3
  refine measurable_of_tendsto_metrizable hN (tendsto_pi_nhds.2 fun p ↦ ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈(p.1.toNNReal : ℝ≥0)⌉₊) fun N hN ↦ ?_
  rw [min_eq_left]
  exact (Nat.le_ceil _).trans (by exact_mod_cast hN)

/-- Truncating a progressive process at level `M` (Mathlib's `ProbabilityTheory.truncation`,
which keeps the values in `(-M, M]` and sets the others to `0`) gives a progressive process. -/
theorem IsProgressive.truncation {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) (M : ℝ) : IsProgressive F (fun u ↦ truncation (H u) M) := by
  intro T
  exact (measurable_id.indicator measurableSet_Ioc).comp (hH T)

/-- For a progressive `H` and `b ≤ T`, the average of `u ↦ H u ω` over `[a, b]` is
`F T`-measurable in `ω`. -/
theorem IsProgressive.measurable_average_Icc {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) {a b : ℝ} {T : ℝ≥0} (hbT : b ≤ T) :
    Measurable[F T] fun ω ↦ ⨍ s in Set.Icc a b, H s.toNNReal ω := by
  let := F T
  have hg : Measurable fun p : ℝ × Ω ↦ H (min p.1.toNNReal T) p.2 := by
    have h3 : Measurable fun p : ℝ × Ω ↦
        ((⟨min p.1.toNNReal T, min_le_right _ _⟩ : Set.Iic T), p.2) :=
      ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk.prodMk
        measurable_snd
    exact (hH T).comp h3
  have hint := (hg.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Set.Icc a b))
    (f := fun s ω ↦ H (min s.toNNReal T) ω)).measurable
  have heq : (fun ω ↦ ⨍ s in Set.Icc a b, H s.toNNReal ω) =
      fun ω ↦ (volume.real (Set.Icc a b))⁻¹ • ∫ s in Set.Icc a b, H (min s.toNNReal T) ω := by
    funext ω
    rw [setAverage_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun s hs ↦ ?_
    rw [min_eq_left]
    exact Real.toNNReal_le_iff_le_coe.2 (hs.2.trans hbT)
  rw [heq]
  simp only [smul_eq_mul]
  exact hint.const_mul _

/-- The average of a function bounded by `C` over `[a, b]` is bounded by `C`. -/
private theorem abs_average_Icc_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (a b : ℝ) :
    |⨍ x in Set.Icc a b, f x| ≤ C := by
  rw [setAverage_eq, smul_eq_mul, abs_mul]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a)
  rcases eq_or_ne (volume.real (Set.Icc a b)) 0 with h0 | h0
  · simp [h0, hC0]
  have hpos : 0 < volume.real (Set.Icc a b) := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
  have hint : |∫ x in Set.Icc a b, f x| ≤ C * volume.real (Set.Icc a b) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc a b) (f := f)
      (C := C) measure_Icc_lt_top (fun x _ ↦ by rw [Real.norm_eq_abs]; exact hC x)
    rwa [Real.norm_eq_abs] at this
  rw [abs_inv, abs_of_pos hpos]
  calc (volume.real (Set.Icc a b))⁻¹ * |∫ x in Set.Icc a b, f x|
      ≤ (volume.real (Set.Icc a b))⁻¹ * (C * volume.real (Set.Icc a b)) := by gcongr
    _ = C := by field_simp

/-- The **delayed-average approximation** of a progressive process `H` on `[0, t]`, truncated at
level `M`, with `n + 1` intervals: on `(t_k, t_{k+1}]`, with `t_k = k t / (n + 1)`, it equals the
average of `truncation (H ·) M` over `[t_{k-1}, t_k]` for `k ≥ 1`, and `0` for `k = 0`. For
`M ≤ 0` the truncation, and hence the approximation, is `0`. -/
noncomputable def delayedAverage {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) (M : ℝ) (t : ℝ≥0) (n : ℕ) : ElementaryIntegrand F where
  n := n + 1
  time := fun i ↦ t * ((i : ℝ≥0) / (n + 1))
  monotone_time := fun i j hij ↦ by
    dsimp only
    gcongr
    exact_mod_cast hij
  coeff := fun i ω ↦ if (i : ℕ) = 0 then 0 else
    ⨍ s in Set.Icc ((t : ℝ) * (((i : ℕ) : ℝ) - 1) / (n + 1)) ((t : ℝ) * ((i : ℕ) : ℝ) / (n + 1)),
      truncation (H s.toNNReal) M ω
  measurable_coeff := fun i ↦ by
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ↓reduceIte]
      exact measurable_const
    · simp only [hi, ↓reduceIte]
      refine IsProgressive.measurable_average_Icc (IsProgressive.truncation hH M) ?_
      simp [mul_div_assoc]
  bound := |M|
  abs_coeff_le := fun i ω ↦ by
    split_ifs
    · simp
    · exact abs_average_Icc_le (fun x ↦ abs_truncation_le_bound _ M ω) _ _

/-- The index `k` of the partition interval `(k t / (n + 1), (k + 1) t / (n + 1)]` containing
`u`. -/
private noncomputable def gridIndex (t : ℝ≥0) (n : ℕ) (u : ℝ) : ℕ :=
  ⌈u * (n + 1) / t⌉₊ - 1

private theorem gridIndex_spec {t : ℝ≥0} (ht : 0 < t) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) t) :
    gridIndex t n u < n + 1 ∧ (t : ℝ) * (gridIndex t n u : ℝ) / (n + 1) < u ∧
      u ≤ (t : ℝ) * ((gridIndex t n u : ℝ) + 1) / (n + 1) := by
  have ht' : (0 : ℝ) < t := ht
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set x := u * (n + 1) / t with hx
  have hx0 : 0 < x := by rw [hx]; have := hu.1; positivity
  have hxN : x ≤ (n : ℝ) + 1 := by
    rw [hx, div_le_iff₀ ht']
    nlinarith [hu.2]
  have hc1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  have hcast : ((gridIndex t n u : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
    rw [gridIndex, ← hx, Nat.cast_sub hc1, Nat.cast_one]
  refine ⟨?_, ?_, ?_⟩
  · have : ⌈x⌉₊ ≤ n + 1 := Nat.ceil_le.2 (by exact_mod_cast hxN)
    unfold gridIndex
    rw [← hx]
    omega
  · rw [hcast, div_lt_iff₀ hN]
    have h1 := Nat.ceil_lt_add_one hx0.le
    have h2 : x * t = u * (n + 1) := by rw [hx]; field_simp
    nlinarith
  · rw [hcast, le_div_iff₀ hN, sub_add_cancel]
    have h1 := Nat.le_ceil x
    have h2 : x * t = u * (n + 1) := by rw [hx]; field_simp
    nlinarith

/-- On `(0, t]` the delayed-average approximation equals the coefficient of the interval
containing `u`. -/
private theorem toProcess_delayedAverage {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsProgressive F H) (M : ℝ) {t : ℝ≥0} (ht : 0 < t) (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) t) (ω : Ω) :
    (delayedAverage hH M t n).toProcess u.toNNReal ω =
      (delayedAverage hH M t n).coeff ⟨gridIndex t n u, (gridIndex_spec ht n hu).1⟩ ω := by
  obtain ⟨-, h1, h2⟩ := gridIndex_spec ht n hu
  refine ElementaryIntegrand.toProcess_eq_of_mem _ ⟨?_, ?_⟩ ω
  · rw [Real.lt_toNNReal_iff_coe_lt]
    simpa [delayedAverage, mul_div_assoc] using h1
  · rw [Real.toNNReal_le_iff_le_coe]
    simpa [delayedAverage, mul_div_assoc] using h2

/-- **Convergence of the delayed averages.** For a progressive `H` and a finite measure `P`, the
delayed-average approximations of the truncation of `H` at level `M` converge to it in
`L²(P ⊗ du)` on `(0, t] × Ω` as the mesh `t / (n + 1)` tends to `0` (Karatzas–Shreve 1991, proof of
Lemma 3.2.4(b)). -/
theorem tendsto_integrandDist_delayedAverage {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (M : ℝ) (t : ℝ≥0) :
    Tendsto (fun n ↦ integrandDist P (delayedAverage hH M t n).toProcess
      (fun u ↦ truncation (H u) M) t) atTop (𝓝 0) := by
  rcases eq_zero_or_pos t with ht | ht
  · subst ht
    simp [integrandDist]
  have ht' : (0 : ℝ) < t := ht
  have hHm := IsProgressive.measurable_toNNReal hH
  have hTm : Measurable fun p : ℝ × Ω ↦ truncation (H p.1.toNNReal) M p.2 :=
    (measurable_id.indicator measurableSet_Ioc).comp hHm
  -- the bound on `(0, t]`
  have hbd : ∀ n ω u, u ∈ Set.Ioc (0 : ℝ) t →
      ‖(delayedAverage hH M t n).toProcess u.toNNReal ω - truncation (H u.toNNReal) M ω‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 * |M|) ^ 2) := by
    intro n ω u hu
    rw [toProcess_delayedAverage hH M ht n hu ω, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) ?_ 2)
    refine (abs_sub _ _).trans ?_
    have h1 := (delayedAverage hH M t n).abs_coeff_le
      ⟨gridIndex t n u, (gridIndex_spec ht n hu).1⟩ ω
    have h2 := abs_truncation_le_bound (H u.toNNReal) M ω
    change _ ≤ |M| at h1
    linarith
  -- pointwise convergence on `(0, t]`
  have hconv : ∀ ω, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      Tendsto (fun n ↦ (delayedAverage hH M t n).toProcess u.toNNReal ω) atTop
        (𝓝 (truncation (H u.toNNReal) M ω)) := by
    intro ω
    set f : ℝ → ℝ := fun s ↦ truncation (H s.toNNReal) M ω with hf
    have hfm : Measurable f := hTm.comp (measurable_id.prodMk measurable_const)
    have hfli : LocallyIntegrable f volume := by
      refine (locallyIntegrable_iff).2 fun k hk ↦ ?_
      exact Measure.integrableOn_of_bounded hk.measure_lt_top.ne hfm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun s ↦ by
          rw [Real.norm_eq_abs]; exact abs_truncation_le_bound _ M ω)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hfli.ae_tendsto_average_Icc] with u hu hLDT
    set k : ℕ → ℕ := fun n ↦ gridIndex t n u with hk
    have hlen : ∀ n : ℕ, (t : ℝ) * (k n : ℝ) / (n + 1) - (t : ℝ) * ((k n : ℝ) - 1) / (n + 1) =
        (t : ℝ) / (n + 1) := by
      intro n; field_simp; ring
    have hlim := hLDT (fun n ↦ (t : ℝ) * ((k n : ℝ) - 1) / (n + 1))
      (fun n ↦ (t : ℝ) * (k n : ℝ) / (n + 1))
      (Filter.Eventually.of_forall fun n ↦ by
        have := hlen n
        have : (0 : ℝ) < (t : ℝ) / (n + 1) := by positivity
        linarith)
      (Filter.Eventually.of_forall fun n ↦ by
        obtain ⟨-, h1, h2⟩ := gridIndex_spec ht n hu
        rw [hlen n]
        have e1 : (t : ℝ) * ((k n : ℝ) + 1) / (n + 1) =
            (t : ℝ) * (k n : ℝ) / (n + 1) + (t : ℝ) / (n + 1) := by ring
        have e2 : ((t : ℝ) * ((k n : ℝ) - 1) / (n + 1) + (t : ℝ) * (k n : ℝ) / (n + 1)) / 2 =
            (t : ℝ) * (k n : ℝ) / (n + 1) - (t : ℝ) / (n + 1) / 2 := by ring
        rw [e2, abs_le]
        have : (0 : ℝ) < (t : ℝ) / (n + 1) := by positivity
        constructor <;> linarith)
      (by
        simp_rw [hlen]
        exact tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    refine hlim.congr' ?_
    -- eventually the interval containing `u` is not the first one
    obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) / u)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [toProcess_delayedAverage hH M ht n hu ω]
    have hk1 : k n ≠ 0 := by
      intro h0
      obtain ⟨-, -, h2⟩ := gridIndex_spec ht n hu
      have h0' : (gridIndex t n u : ℝ) = 0 := by simp only [hk] at h0; exact_mod_cast h0
      rw [h0', zero_add, mul_one, le_div_iff₀ (by positivity)] at h2
      have hu0 := hu.1
      have : (t : ℝ) / u < n + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_iff₀ hu0] at this
      linarith
    simp only [delayedAverage]
    split_ifs with h
    · exact absurd h hk1
    · rfl
  -- inner convergence
  have hinner : ∀ ω, Tendsto (fun n ↦ ∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(delayedAverage hH M t n).toProcess u.toNNReal ω - truncation (H u.toNNReal) M ω‖ₑ ^ 2)
      atTop (𝓝 0) := by
    intro ω
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _u in Set.Ioc (0 : ℝ) t, 0 := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ ENNReal.ofReal ((2 * |M|) ^ 2))
      (fun n ↦ ?_) (fun n ↦ ?_) ?_ ?_
    · exact ((((delayedAverage hH M t n).measurable_toProcess.sub hTm).comp
        (measurable_id.prodMk measurable_const)).enorm).pow_const 2
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu using hbd n ω u hu
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
    · filter_upwards [hconv ω] with u hu
      have := ENNReal.Tendsto.pow (n := 2) ((continuous_enorm.tendsto _).comp (hu.sub_const
        (truncation (H u.toNNReal) M ω)))
      simpa using this
  -- outer convergence
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _ω, 0 ∂P := by simp
  unfold integrandDist
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence
    (fun _ ↦ ENNReal.ofReal ((2 * |M|) ^ 2) * volume (Set.Ioc (0 : ℝ) t)) (fun n ↦ ?_)
    (fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_) ?_ (Filter.Eventually.of_forall hinner)
  · exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
      (f := fun p : Ω × ℝ ↦ ‖(delayedAverage hH M t n).toProcess p.2.toNNReal p.1 -
        truncation (H p.2.toNNReal) M p.1‖ₑ ^ 2)
      (((((delayedAverage hH M t n).measurable_toProcess.sub hTm).comp
        measurable_swap).enorm).pow_const 2)
  · calc _ ≤ ∫⁻ _u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((2 * |M|) ^ 2) :=
          setLIntegral_mono_ae measurable_const.aemeasurable
            (Filter.Eventually.of_forall fun u hu ↦ hbd n ω u hu)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
      (measure_ne_top P _)

/-- **Truncation.** For a jointly measurable `H` with `E ∫_0^t H_u² du < ∞`, the truncations of
`H` at levels `M → ∞` converge to `H` in `L²(P ⊗ du)` on `(0, t] × Ω`
(Karatzas–Shreve 1991, proof of Lemma 3.2.4(c)). -/
theorem tendsto_integrandDist_truncation {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (hHm : Measurable fun p : ℝ × Ω ↦ H p.1.toNNReal p.2) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    Tendsto (fun M : ℕ ↦ integrandDist P (fun u ↦ truncation (H u) M) H t) atTop (𝓝 0) := by
  have hpt : ∀ (M x : ℝ), ‖Set.indicator (Set.Ioc (-M) M) id x - x‖ₑ ^ 2 ≤ ‖x‖ₑ ^ 2 := by
    intro M x
    by_cases hx : x ∈ Set.Ioc (-M) M
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hlim : ∀ x : ℝ, Tendsto (fun M : ℕ ↦ ‖Set.indicator (Set.Ioc (-(M : ℝ)) M) id x - x‖ₑ ^ 2)
      atTop (𝓝 0) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt |x|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    have hxM : |x| < (M : ℝ) := hN.trans_le (by exact_mod_cast hM)
    have := truncation_eq_self (f := id) (x := x) hxM
    simp only [truncation, Function.comp_apply, id] at this
    simp [this]
  set G : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2 with hG
  have hGm : Measurable G := Measurable.lintegral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) t)) (f := fun p : Ω × ℝ ↦ ‖H p.2.toNNReal p.1‖ₑ ^ 2)
    ((hHm.comp measurable_swap).enorm.pow_const 2)
  have hGfin : ∀ᵐ ω ∂P, G ω ≠ ∞ := (ae_lt_top hGm hH2).mono fun _ h ↦ h.ne
  have hTm : ∀ M : ℝ, Measurable fun p : ℝ × Ω ↦ truncation (H p.1.toNNReal) M p.2 :=
    fun M ↦ (measurable_id.indicator measurableSet_Ioc).comp hHm
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _ω, 0 ∂P := by simp
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence G (fun M ↦ ?_) (fun M ↦ ?_) hH2 ?_
  · exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
      (f := fun p : Ω × ℝ ↦ ‖truncation (H p.2.toNNReal) M p.1 - H p.2.toNNReal p.1‖ₑ ^ 2)
      ((((hTm M).sub hHm).comp measurable_swap).enorm.pow_const 2)
  · exact Filter.Eventually.of_forall fun ω ↦ lintegral_mono fun u ↦ hpt M _
  · filter_upwards [hGfin] with ω hω
    have h0' : (0 : ℝ≥0∞) = ∫⁻ _u in Set.Ioc (0 : ℝ) t, 0 := by simp
    rw [h0']
    refine tendsto_lintegral_of_dominated_convergence (fun u ↦ ‖H u.toNNReal ω‖ₑ ^ 2)
      (fun M ↦ ?_) (fun M ↦ Filter.Eventually.of_forall fun u ↦ hpt M _) hω
      (Filter.Eventually.of_forall fun u ↦ hlim _)
    exact (((hTm M).sub hHm).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2

/-- **Density of elementary integrands.** A progressive integrand `H` with
`E ∫_0^t H_u² du < ∞` is the `L²(P ⊗ du)`-limit on `(0, t] × Ω` of elementary integrands
(Karatzas–Shreve 1991, Lemma 3.2.4 and Proposition 3.2.6). -/
theorem isItoApproximable_of_isProgressive {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    IsItoApproximable P F H t := by
  have hHm := IsProgressive.measurable_toNNReal hH
  have hTm : ∀ M : ℝ, Measurable fun p : ℝ × Ω ↦ truncation (H p.1.toNNReal) M p.2 :=
    fun M ↦ (measurable_id.indicator measurableSet_Ioc).comp hHm
  have hcomm : ∀ X Y : ℝ≥0 → Ω → ℝ, integrandDist P X Y t = integrandDist P Y X t := by
    intro X Y
    simp_rw [integrandDist, enorm_sub_rev]
  have hex : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ElementaryIntegrand F,
      integrandDist P K.toProcess H t < ε := by
    intro ε hε
    have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
    obtain ⟨M, hM⟩ :=
      ((tendsto_integrandDist_truncation hHm t hH2).eventually (gt_mem_nhds hε4)).exists
    obtain ⟨n, hn⟩ := ((tendsto_integrandDist_delayedAverage (P := P) hH (M : ℝ) t).eventually
      (gt_mem_nhds hε4)).exists
    refine ⟨delayedAverage hH (M : ℝ) t n, ?_⟩
    calc integrandDist P (delayedAverage hH (M : ℝ) t n).toProcess H t
        ≤ 2 * integrandDist P (delayedAverage hH (M : ℝ) t n).toProcess
            (fun u ↦ truncation (H u) M) t +
          2 * integrandDist P H (fun u ↦ truncation (H u) M) t :=
          integrandDist_le (delayedAverage hH (M : ℝ) t n).measurable_toProcess hHm (hTm M) t
      _ < 2 * (ε / 4) + 2 * (ε / 4) := by
          rw [hcomm H]
          exact ENNReal.add_lt_add
            ((ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).2 hn)
            ((ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).2 hM)
      _ = ε := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num]
          exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  choose K hK using fun n : ℕ ↦
    hex ((n : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  exact ⟨hHm, K, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ bot_le) fun n ↦ (hK n).le⟩

/-- **Itô isometry for progressive integrands.** For a pre-Brownian motion `B` adapted to `F`
with increments independent of the past and an `F`-progressive integrand `H` with
`E ∫_0^t H_u² du < ∞`, `E[(∫_0^t H dB)²] = E ∫_0^t H_u² du` (Karatzas–Shreve 1991,
Section 3.2). -/
theorem lintegral_itoIntegral_sq_of_isProgressive {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) (t : ℝ≥0)
    (hH2 : ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∫⁻ ω, ‖itoIntegral P F B H t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact lintegral_itoIntegral_sq hB hBF hInd (isItoApproximable_of_isProgressive hH t hH2)

/-- **Martingale property for progressive integrands.** For a pre-Brownian motion `B` adapted
to `F` with increments independent of the past and an `F`-progressive integrand `H` with
`E ∫_0^t H_u² du < ∞` for every `t`, the Itô integral `t ↦ ∫_0^t H dB` is an `F`-martingale
(Karatzas–Shreve 1991, Proposition 3.2.10). -/
theorem martingale_itoIntegral_of_isProgressive {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    Martingale (itoIntegral P F B H) F P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact martingale_itoIntegral hB hBF hInd fun t ↦ isItoApproximable_of_isProgressive hH t (hH2 t)

end ProbabilityTheory
