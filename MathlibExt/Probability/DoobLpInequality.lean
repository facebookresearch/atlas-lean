/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Doob's L² maximal inequality

For a square-integrable martingale `f`, the expected square of the running
maximum `max_{k ≤ n} |f k|` is at most four times the expected square of the
final value `f n`. The constant `4 = (2/(2-1))²` is the `p = 2` case of
Doob's `Lᵖ` maximal inequality; Mathlib currently only has the weak-type
(`L¹`) maximal inequality `MeasureTheory.maximal_ineq`, whose documentation
notes the `Lᵖ` inequality as a corollary to be proved.

The proof follows the classical argument: apply the weak-type maximal
inequality to the nonnegative submartingale `|f|`, integrate the resulting
tail bound by the layer-cake formula, swap the two integrals by Tonelli's
theorem, and close with Cauchy–Schwarz.

## Source

This formalizes the target "Square integrable martingale maximal inequality"
(Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`, whose v1
formalization `v1/Atlas/TheoryOfProbability/code/SqMartingaleMaximal.lean`
states `E[sup_m |X_m|²] ≤ 4 E[A_∞]` with `A` the predictable quadratic
variation. That statement is false as written: for the constant martingale
`X_m = c ≠ 0`, the predictable quadratic variation is identically `0` while
`E[sup_m |X_m|²] = c² > 0`. The gap is the missing initial term
`E[X_0²]`: for a martingale, `E[X_n²] = E[X_0²] + E[A_n]`. The versions
below therefore state the unconditional bound in terms of `E[X_n²]`, and
recover the book's `A`-form under the (book-implicit) extra hypothesis
`X_0 = 0` almost everywhere.

## Main results

* `MeasureTheory.Martingale.doob_sq_maximal_ineq`: finite-horizon bound
  `∫ (max_{k ≤ n} |f k|)² ≤ 4 ∫ (f n)²`.
* `MeasureTheory.predictableQuadraticVariation`: the predictable quadratic
  variation `A_n = ∑_{k < n} E[(f_{k+1} - f_k)² | ℱ_k]`, the predictable part
  of `f²` in Doob's decomposition.
* `MeasureTheory.Martingale.integral_predictableQuadraticVariation`:
  `∫ A_n = ∫ (f n)² - ∫ (f 0)²`.
* `MeasureTheory.Martingale.doob_sq_maximal_ineq_predictableQuadraticVariation`:
  finite-horizon bound in terms of `A_n` when `f 0 = 0` a.e.
* `MeasureTheory.Martingale.doob_sq_maximal_ineq_iSup`: infinite-horizon
  bound `∫⁻ sup_n |f n|² ≤ 4 ∫⁻ sup_n A_n` when `f 0 = 0` a.e.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

/-- The running maximum `max_{k ≤ n} |f k|` is measurable. -/
private theorem measurable_runningMax (hmart : Martingale f ℱ μ) (n : ℕ) :
    Measurable (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) := by
  apply Finset.measurable_range_sup''
  intro k _
  have hmeas : Measurable (f k) :=
    (hmart.stronglyMeasurable k).mono (ℱ.le k) |>.measurable
  simpa [Real.norm_eq_abs] using hmeas.norm

/-- The running maximum `max_{k ≤ n} |f k|` is nonnegative. -/
private theorem runningMax_nonneg (n : ℕ) :
    ∀ ω, 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω| := by
  intro ω
  exact le_trans (abs_nonneg (f 0 ω))
    (Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- The running maximum of a square-integrable martingale is square-integrable,
since it is bounded by the sum of the `|f k|`. -/
private theorem memLp_runningMax (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ)
    (n : ℕ) :
    MemLp (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) 2 μ := by
  have hle : ∀ᵐ ω ∂μ, ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |f k ω|‖ ≤ ∑ k ∈ Finset.range (n + 1), |f k ω| := by
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (runningMax_nonneg n ω)]
    exact Finset.sup'_le Finset.nonempty_range_add_one (fun k => |f k ω|)
      fun k hk =>
      Finset.single_le_sum (s := Finset.range (n + 1)) (f := fun i => |f i ω|)
        (fun i _ => abs_nonneg _) hk
  have hmeas : AEStronglyMeasurable (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => |f k ω|) μ :=
    (measurable_runningMax hmart n).aestronglyMeasurable
  exact MemLp.mono' (memLp_finsetSum (Finset.range (n + 1)) fun k _ => (hL2 k).abs)
    hmeas hle

/-- The absolute value of a real martingale is a submartingale. This is the
`φ = |·|` case of "a convex function of a martingale is a submartingale",
proved directly from `|E[X | ℱ]| ≤ E[|X| | ℱ]`. -/
private theorem Martingale.submartingale_abs (hf : Martingale f ℱ μ) :
    Submartingale (fun n ω => |f n ω|) ℱ μ := by
  refine ⟨fun n => ?_, fun i j hij => ?_, fun n => (hf.integrable n).abs⟩
  · simpa [Real.norm_eq_abs] using (hf.stronglyMeasurable n).norm
  · have h1 : μ[f j | ℱ i] =ᵐ[μ] f i := hf.condExp_ae_eq hij
    have h2 : (fun ω => ‖μ[f j | ℱ i] ω‖) ≤ᵐ[μ] μ[(fun ω => ‖f j ω‖) | ℱ i] :=
      norm_condExp_le _
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [← hω1]
    simpa [Real.norm_eq_abs] using hω2

/-- `ENNReal.ofReal` commutes with a finite supremum. -/
private lemma ofReal_sup' {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hs : s.Nonempty) :
    ENNReal.ofReal (s.sup' hs b) = s.sup' hs (fun i => ENNReal.ofReal (b i)) := by
  apply le_antisymm
  · have hex : ∃ i, i ∈ s ∧ s.sup' hs b = b i :=
      Finset.exists_mem_eq_sup' (α := ℝ) hs b
    obtain ⟨i, hi, hieq⟩ := hex
    rw [hieq]
    exact Finset.le_sup' (fun j => ENNReal.ofReal (b j)) hi
  · exact Finset.sup'_le hs (fun i => ENNReal.ofReal (b i)) fun i hi =>
      ENNReal.ofReal_le_ofReal (Finset.le_sup' b hi)

/-- For nonnegative functions, squaring commutes with a finite supremum. -/
private lemma sup'_sq {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hs : s.Nonempty)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    (s.sup' hs b) ^ 2 = s.sup' hs (fun i => (b i) ^ 2) := by
  apply le_antisymm
  · have hex : ∃ i, i ∈ s ∧ s.sup' hs b = b i :=
      Finset.exists_mem_eq_sup' (α := ℝ) hs b
    obtain ⟨i, hi, hieq⟩ := hex
    rw [hieq]
    exact Finset.le_sup' (fun j => (b j) ^ 2) hi
  · exact Finset.sup'_le hs (fun i => (b i) ^ 2) fun i hi =>
      pow_le_pow_left₀ (hb i hi) (Finset.le_sup' b hi) 2

/-- Tonelli swap for the tail integral: integrating the set integral of `|g|`
over `{M ≥ t}` against `t ∈ (0, ∞)` equals integrating `|g| * M`. -/
private lemma lintegral_ofReal_setIntegral_abs_ge {M g : Ω → ℝ} [SFinite μ]
    (hM_meas : Measurable M) (hg_meas : Measurable g)
    (hg_int : Integrable (fun ω => |g ω|) μ) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (|g ω| * M ω) ∂μ := by
  have hF_meas : AEMeasurable (Function.uncurry
      (fun (t : ℝ) (ω : Ω) => if t ≤ M ω then ENNReal.ofReal |g ω| else 0))
      (((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod μ) := by
    have hS : MeasurableSet {p : ℝ × Ω | p.1 ≤ M p.2} :=
      measurableSet_le measurable_fst (hM_meas.comp measurable_snd)
    have hG : Measurable (fun p : ℝ × Ω => ENNReal.ofReal |g p.2|) :=
      ENNReal.measurable_ofReal.comp
        (by simpa [Real.norm_eq_abs] using (hg_meas.comp measurable_snd).norm)
    have hEq : Function.uncurry
        (fun (t : ℝ) (ω : Ω) => if t ≤ M ω then ENNReal.ofReal |g ω| else 0) =
        Set.indicator {p : ℝ × Ω | p.1 ≤ M p.2} (fun p => ENNReal.ofReal |g p.2|) := by
      funext p
      obtain ⟨t, ω⟩ := p
      by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
    rw [hEq]
    exact (Measurable.indicator hG hS).aemeasurable
  have h_inner_left : ∀ t : ℝ,
      ∫⁻ ω, (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂μ =
        ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ) := by
    intro t
    have hset : MeasurableSet {ω | t ≤ M ω} := measurableSet_le measurable_const hM_meas
    rw [ofReal_integral_eq_lintegral_ofReal (hg_int.integrableOn)
      (Eventually.of_forall fun ω => abs_nonneg _)]
    rw [← lintegral_indicator hset]
    apply lintegral_congr_ae
    filter_upwards with ω
    by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
  have h_inner_right : ∀ ω : Ω,
      ∫⁻ t in Set.Ioi (0 : ℝ), (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂volume =
        ENNReal.ofReal (|g ω| * M ω) := by
    intro ω
    have h1 : (∫⁻ t in Set.Ioi (0 : ℝ),
          (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂volume) =
        ∫⁻ t in (Set.Iic (M ω) ∩ Set.Ioi (0 : ℝ)), ENNReal.ofReal |g ω| ∂volume := by
      rw [← Measure.restrict_restrict measurableSet_Iic,
        ← lintegral_indicator (measurableSet_Iic : MeasurableSet (Set.Iic (M ω)))
          (μ := volume.restrict (Set.Ioi 0))]
      apply lintegral_congr_ae
      filter_upwards with t
      by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
    rw [h1, setLIntegral_const]
    have hset : Set.Iic (M ω) ∩ Set.Ioi (0 : ℝ) = Set.Ioc 0 (M ω) := by
      ext t
      simp [Set.mem_Ioc, and_comm]
    rw [hset, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (abs_nonneg _)]
  calc ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ)
      = ∫⁻ t in Set.Ioi 0, ∫⁻ ω,
          (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂μ := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t _
        exact (h_inner_left t).symm
    _ = ∫⁻ ω, (∫⁻ t in Set.Ioi (0 : ℝ),
          (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂volume) ∂μ :=
        lintegral_lintegral_swap hF_meas
    _ = ∫⁻ ω, ENNReal.ofReal (|g ω| * M ω) ∂μ :=
        lintegral_congr_ae (ae_of_all μ fun ω => h_inner_right ω)

/-- The threshold set integral `t ↦ ∫_{M ≥ t} |g|` is measurable in `t`. -/
private lemma measurable_ofReal_setIntegral_abs_ge {M g : Ω → ℝ} [SFinite μ]
    (hM_meas : Measurable M) (hg_meas : Measurable g)
    (hg_int : Integrable (fun ω => |g ω|) μ) :
    Measurable (fun t => ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ)) := by
  have hFmeas : Measurable (Function.uncurry
      (fun (t : ℝ) (ω : Ω) => if t ≤ M ω then ENNReal.ofReal |g ω| else 0)) := by
    have hS : MeasurableSet {p : ℝ × Ω | p.1 ≤ M p.2} :=
      measurableSet_le measurable_fst (hM_meas.comp measurable_snd)
    have hG : Measurable (fun p : ℝ × Ω => ENNReal.ofReal |g p.2|) :=
      ENNReal.measurable_ofReal.comp
        (by simpa [Real.norm_eq_abs] using (hg_meas.comp measurable_snd).norm)
    have hEq : Function.uncurry
        (fun (t : ℝ) (ω : Ω) => if t ≤ M ω then ENNReal.ofReal |g ω| else 0) =
        Set.indicator {p : ℝ × Ω | p.1 ≤ M p.2} (fun p => ENNReal.ofReal |g p.2|) := by
      funext p
      obtain ⟨t, ω⟩ := p
      by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
    rw [hEq]
    exact Measurable.indicator hG hS
  have hEq : (fun t => ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ)) =
      (fun t => ∫⁻ ω, (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂μ) := by
    funext t
    show ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |g ω| ∂μ) =
      ∫⁻ ω, (if t ≤ M ω then ENNReal.ofReal |g ω| else 0) ∂μ
    have hset : MeasurableSet {ω | t ≤ M ω} := measurableSet_le measurable_const hM_meas
    rw [ofReal_integral_eq_lintegral_ofReal (hg_int.integrableOn)
      (Eventually.of_forall fun ω => abs_nonneg _)]
    rw [← lintegral_indicator hset]
    apply lintegral_congr_ae
    filter_upwards with ω
    by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
  rw [hEq]
  exact hFmeas.lintegral_prod_right

/-- **Doob's L² maximal inequality, finite horizon.** Let $\mu$ be a probability measure and let
$(f_k)_{k \in \mathbb{N}}$ be a real-valued martingale with respect to a filtration
$(\mathcal{F}_k)$ and $\mu$ such that every $f_k$ is in $L^2(\mu)$. Then for every
$n \in \mathbb{N}$, $\int (\max_{k \le n} |f_k|)^2 \, d\mu \le 4 \int f_n^2 \, d\mu$. -/
theorem Martingale.doob_sq_maximal_ineq [IsProbabilityMeasure μ] (hmart : Martingale f ℱ μ)
    (hL2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, (f n ω) ^ 2 ∂μ := by
  classical
  -- The running maximum `M`.
  set M : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => |f k ω| with hM_def
  have hf_meas : ∀ k, Measurable (f k) := fun k =>
    (hmart.stronglyMeasurable k).mono (ℱ.le k) |>.measurable
  have hM_meas : Measurable M := by
    rw [hM_def]
    exact measurable_runningMax hmart n
  have hM_nonneg : ∀ ω, 0 ≤ M ω := fun ω => runningMax_nonneg n ω
  have hM_aemeas : AEMeasurable M μ := hM_meas.aemeasurable
  have hM_memLp : MemLp M 2 μ := by
    rw [hM_def]
    exact memLp_runningMax hmart hL2 n
  have hM_sq_int : Integrable (fun ω => M ω ^ 2) μ := hM_memLp.integrable_sq
  have hfn_sq_int : Integrable (fun ω => (f n ω) ^ 2) μ := (hL2 n).integrable_sq
  -- The two `∫⁻ ofReal (· ^ 2)` quantities.
  set S : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂μ with hS_def
  set T : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂μ with hT_def
  have hS_ne_top : S ≠ ∞ := by
    rw [hS_def, ← ofReal_integral_eq_lintegral_ofReal hM_sq_int
      (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hT_ne_top : T ≠ ∞ := by
    rw [hT_def, ← ofReal_integral_eq_lintegral_ofReal hfn_sq_int
      (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  -- Layer-cake: `S = ∫⁻ t in (0, ∞), μ {M > t} * ofReal (2t)`.
  have hlayer : S = ∫⁻ t in Set.Ioi 0, μ {a | t < M a} * ENNReal.ofReal (2 * t) := by
    have key := lintegral_comp_eq_lintegral_meas_lt_mul (μ := μ) (f := M)
      (g := fun t => 2 * t) (Eventually.of_forall (runningMax_nonneg n)) hM_aemeas
      (fun t _ => (continuous_id.const_mul 2).intervalIntegrable 0 t)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          using mul_nonneg (by norm_num) (Set.mem_Ioi.mp ht).le)
    rw [← key]
    apply lintegral_congr_ae
    filter_upwards with ω
    congr 1
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  -- Tail bound from the weak-type maximal inequality applied to `|f|`.
  have htail : ∀ t : ℝ, 0 < t →
      μ {a | t < M a} * ENNReal.ofReal (2 * t) ≤
        2 * ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
    intro t ht
    set ε : ℝ≥0 := ⟨t, ht.le⟩ with hε
    have hεt : (ε : ℝ) = t := rfl
    have hmax : ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤
        ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
      have h := maximal_ineq (μ := μ) (𝒢 := ℱ) (f := fun n ω => |f n ω|)
        hmart.submartingale_abs (fun n ω => abs_nonneg _) (ε := ε) n
      have hcoe : (ε : ℝ≥0∞) = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_coe_nnreal, hεt]
      rw [hcoe] at h
      exact h
    have hle : μ {a | t < M a} ≤ μ {ω | t ≤ M ω} :=
      measure_mono (fun ω hω => le_of_lt (Set.mem_ofPred_eq.mp hω))
    have hcoeff : ENNReal.ofReal (2 * t) = 2 * ENNReal.ofReal t := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc μ {a | t < M a} * ENNReal.ofReal (2 * t)
        = 2 * (μ {a | t < M a} * ENNReal.ofReal t) := by
          rw [hcoeff]
          ring
      _ ≤ 2 * (μ {ω | t ≤ M ω} * ENNReal.ofReal t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (by positivity))
            (by norm_num)
      _ = 2 * (ENNReal.ofReal t * μ {ω | t ≤ M ω}) := by
          rw [mul_comm (μ _) (ENNReal.ofReal t)]
      _ ≤ 2 * ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) :=
          mul_le_mul_of_nonneg_left hmax (by norm_num)
  -- Cauchy–Schwarz: `∫ |f n| * M ≤ √T * √S`.
  have hCS : ∫⁻ ω, ENNReal.ofReal (|f n ω| * M ω) ∂μ ≤
      T ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
    have hmeas1 : AEMeasurable (fun ω => ENNReal.ofReal |f n ω|) μ :=
      (ENNReal.measurable_ofReal.comp
        (by simpa [Real.norm_eq_abs] using (hf_meas n).norm)).aemeasurable
    have hmeas2 : AEMeasurable (fun ω => ENNReal.ofReal (M ω)) μ :=
      (ENNReal.measurable_ofReal.comp hM_meas).aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ)
      Real.HolderConjugate.two_two hmeas1 hmeas2
    calc ∫⁻ ω, ENNReal.ofReal (|f n ω| * M ω) ∂μ
        = ∫⁻ ω, (ENNReal.ofReal |f n ω| * ENNReal.ofReal (M ω)) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with ω
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
      _ ≤ (∫⁻ ω, (ENNReal.ofReal |f n ω|) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
            (∫⁻ ω, (ENNReal.ofReal (M ω)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := h
      _ = T ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
          congr 1
          · congr 1
            apply lintegral_congr_ae
            filter_upwards with ω
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
          · congr 1
            apply lintegral_congr_ae
            filter_upwards with ω
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (hM_nonneg ω) 2]
  -- Integrate the tail bound, swap the integrals, and apply Cauchy–Schwarz.
  have hS_le : S ≤ 2 * (T ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ)) := by
    calc S = ∫⁻ t in Set.Ioi 0, μ {a | t < M a} * ENNReal.ofReal (2 * t) := hlayer
      _ ≤ ∫⁻ t in Set.Ioi 0,
          2 * ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
          apply setLIntegral_mono_ae' measurableSet_Ioi
          filter_upwards with t ht
          exact htail t ht
      _ = 2 * ∫⁻ t in Set.Ioi 0,
          ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
          rw [lintegral_const_mul _ (measurable_ofReal_setIntegral_abs_ge hM_meas
            (hf_meas n) (hmart.integrable n).abs)]
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (|f n ω| * M ω) ∂μ := by
          rw [lintegral_ofReal_setIntegral_abs_ge hM_meas (hf_meas n)
            (hmart.integrable n).abs]
      _ ≤ 2 * (T ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hCS (by norm_num)
  -- Solve `S ≤ 2 * √T * √S` for `S`, in the reals.
  have hST : S ≤ 4 * T := by
    by_cases hS0 : S = 0
    · rw [hS0]
      positivity
    have hSpos : 0 < S.toReal := ENNReal.toReal_pos hS0 hS_ne_top
    have htoReal : S.toReal ≤ 2 * Real.sqrt T.toReal * Real.sqrt S.toReal := by
      have h1 : (2 * (T ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ))).toReal =
          2 * Real.sqrt T.toReal * Real.sqrt S.toReal := by
        have hT2 : (T ^ (1 / 2 : ℝ)) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT_ne_top
        have hS2 : (S ^ (1 / 2 : ℝ)) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS_ne_top
        have e1 : (T ^ (1 / 2 : ℝ)).toReal = Real.sqrt T.toReal := by
          rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
        have e2 : (S ^ (1 / 2 : ℝ)).toReal = Real.sqrt S.toReal := by
          rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, e1, e2]
        simp [mul_assoc]
      have h2 := (ENNReal.toReal_le_toReal hS_ne_top
        (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS_ne_top)))).mpr hS_le
      rwa [h1] at h2
    have hsqrt : Real.sqrt S.toReal ≤ 2 * Real.sqrt T.toReal := by
      by_contra hcon
      push Not at hcon
      have h1 : Real.sqrt S.toReal * Real.sqrt S.toReal >
          2 * Real.sqrt T.toReal * Real.sqrt S.toReal :=
        mul_lt_mul_of_pos_right hcon (Real.sqrt_pos.mpr hSpos)
      rw [Real.mul_self_sqrt (le_of_lt hSpos)] at h1
      linarith [htoReal]
    have hsq : S.toReal ≤ 4 * T.toReal := by
      calc S.toReal = (Real.sqrt S.toReal) ^ 2 := by
            rw [Real.sq_sqrt (le_of_lt hSpos)]
        _ ≤ (2 * Real.sqrt T.toReal) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
        _ = 4 * T.toReal := by
            rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
            ring
    have hfin : (4 * T) ≠ ∞ := ENNReal.mul_ne_top (by simp) hT_ne_top
    have h4 : (4 * T).toReal = 4 * T.toReal := by
      rw [ENNReal.toReal_mul]
      simp
    apply (ENNReal.toReal_le_toReal hS_ne_top hfin).mp
    rw [h4]
    exact hsq
  -- Convert the `∫⁻ ofReal` bound back to Bochner integrals.
  have hBochner : ∫ ω, (M ω) ^ 2 ∂μ ≤ 4 * ∫ ω, (f n ω) ^ 2 ∂μ := by
    have h1 : ∫ ω, (M ω) ^ 2 ∂μ = S.toReal := by
      rw [hS_def, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun ω => sq_nonneg _) hM_sq_int.aestronglyMeasurable]
    have h2 : ∫ ω, (f n ω) ^ 2 ∂μ = T.toReal := by
      rw [hT_def, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun ω => sq_nonneg _) hfn_sq_int.aestronglyMeasurable]
    rw [h1, h2]
    have hfin : (4 * T) ≠ ∞ := ENNReal.mul_ne_top (by simp) hT_ne_top
    have h3 : S.toReal ≤ (4 * T).toReal :=
      (ENNReal.toReal_le_toReal hS_ne_top hfin).mpr hST
    rw [ENNReal.toReal_mul] at h3
    simpa using h3
  exact hBochner

/-- **Predictable quadratic variation.** Let $\mu$ be a measure on $\Omega$, let
$(\mathcal{F}_k)_{k \in \mathbb{N}}$ be a filtration and let $(f_k)_{k \in \mathbb{N}}$ be a
real-valued process. The predictable quadratic variation of $f$ with respect to
$(\mathcal{F}_k)$ and $\mu$ is the process defined pointwise by
$A_n(\omega) = \sum_{k=0}^{n-1} \mathbb{E}_\mu[(f_{k+1} - f_k)^2 \mid \mathcal{F}_k](\omega)$,
so $A_0 = 0$. For a square-integrable martingale this is the predictable part of $f^2$ in Doob's
decomposition. -/
noncomputable def predictableQuadraticVariation (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun k =>
    (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω)

/-- The predictable quadratic variation is integrable. -/
private theorem integrable_predictableQuadraticVariation [IsProbabilityMeasure μ]
    (n : ℕ) :
    Integrable (predictableQuadraticVariation μ ℱ f n) μ := by
  have h : Integrable (fun ω => ∑ k ∈ Finset.range n,
      (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω) μ :=
    integrable_finsetSum _ (fun k _ => integrable_condExp)
  have hEq : predictableQuadraticVariation μ ℱ f n =
      fun ω => ∑ k ∈ Finset.range n,
        (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω := by
    funext ω
    simp [predictableQuadraticVariation]
  rw [hEq]
  exact h

/-- The predictable quadratic variation is almost everywhere nonnegative:
each summand is a conditional expectation of a square. -/
private theorem predictableQuadraticVariation_nonneg [IsProbabilityMeasure μ]
    (n : ℕ) :
    0 ≤ᵐ[μ] predictableQuadraticVariation μ ℱ f n := by
  have hall : ∀ᵐ ω ∂μ, ∀ k, 0 ≤
      (μ[(fun ω' => (f (k + 1) ω' - f k ω') ^ 2) | ℱ k]) ω :=
    ae_all_iff.mpr fun k =>
      condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  filter_upwards [hall] with ω hω
  simp only [predictableQuadraticVariation]
  exact Finset.sum_nonneg fun k _ => hω k

/-- Orthogonality of a martingale increment against the current value:
`∫ f_{k+1} * f_k = ∫ f_k²`, since `E[f_{k+1} | ℱ_k] = f_k` a.e. -/
private theorem Martingale.integral_mul_succ_eq [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (k : ℕ) :
    ∫ ω, f (k + 1) ω * f k ω ∂μ = ∫ ω, (f k ω) ^ 2 ∂μ := by
  have hprod_int : Integrable (f (k + 1) * f k) μ :=
    (hL2 (k + 1)).integrable_mul (hL2 k)
  have hcond : μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k] =ᵐ[μ] fun ω => (f k ω) ^ 2 := by
    calc μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k]
        =ᵐ[μ] μ[f (k + 1) | ℱ k] * f k :=
          condExp_mul_of_stronglyMeasurable_right (hmart.stronglyMeasurable k)
            hprod_int (hmart.integrable (k + 1))
      _ =ᵐ[μ] f k * f k :=
          (hmart.condExp_ae_eq (Nat.le_succ k)).mul (EventuallyEq.refl (ae μ) (f k))
      _ =ᵐ[μ] fun ω => (f k ω) ^ 2 := by
          filter_upwards with ω
          simp [Pi.mul_apply, pow_two]
  calc ∫ ω, f (k + 1) ω * f k ω ∂μ
      = ∫ ω, μ[(fun ω => f (k + 1) ω * f k ω) | ℱ k] ω ∂μ :=
        (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, (f k ω) ^ 2 ∂μ := integral_congr_ae hcond

/-- **Expectation of the predictable quadratic variation.** Let $\mu$ be a probability measure
and let $(f_k)_{k \in \mathbb{N}}$ be a real-valued martingale with respect to a filtration
$(\mathcal{F}_k)$ and $\mu$ such that every $f_k$ is in $L^2(\mu)$, and let $A_n$ be its
predictable quadratic variation. Then for every $n \in \mathbb{N}$,
$\int A_n \, d\mu = \int f_n^2 \, d\mu - \int f_0^2 \, d\mu$.

The proof telescopes, using the orthogonality of martingale increments. -/
theorem Martingale.integral_predictableQuadraticVariation [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) :
    ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ =
      ∫ ω, (f n ω) ^ 2 ∂μ - ∫ ω, (f 0 ω) ^ 2 ∂μ := by
  have hsum : ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ =
      ∑ k ∈ Finset.range n, ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ := by
    simp only [predictableQuadraticVariation]
    rw [integral_finsetSum _ (fun k _ => integrable_condExp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_condExp (ℱ.le k)]
  have hdiff : ∀ k, ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ =
      ∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, (f k ω) ^ 2 ∂μ := by
    intro k
    have h1 : Integrable (fun ω => (f (k + 1) ω) ^ 2) μ := (hL2 _).integrable_sq
    have h2 : Integrable (fun ω => (f k ω) ^ 2) μ := (hL2 _).integrable_sq
    have hprod_int : Integrable (fun ω => f (k + 1) ω * f k ω) μ :=
      (hL2 (k + 1)).integrable_mul (hL2 k)
    have hprod2_int : Integrable (fun ω => 2 * (f (k + 1) ω * f k ω)) μ :=
      hprod_int.const_mul 2
    have hA : Integrable (fun ω =>
        (f (k + 1) ω) ^ 2 - 2 * (f (k + 1) ω * f k ω)) μ :=
      h1.sub hprod2_int
    calc ∫ ω, (f (k + 1) ω - f k ω) ^ 2 ∂μ
        = ∫ ω, ((f (k + 1) ω) ^ 2 - 2 * (f (k + 1) ω * f k ω) + (f k ω) ^ 2) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
      _ = (∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, 2 * (f (k + 1) ω * f k ω) ∂μ) +
            ∫ ω, (f k ω) ^ 2 ∂μ := by
          rw [integral_add hA h2, integral_sub h1 hprod2_int]
      _ = ∫ ω, (f (k + 1) ω) ^ 2 ∂μ - ∫ ω, (f k ω) ^ 2 ∂μ := by
          rw [integral_const_mul, hmart.integral_mul_succ_eq hL2 k]
          ring
  rw [hsum, Finset.sum_congr rfl (fun k _ => hdiff k)]
  exact Finset.sum_range_sub (fun k => ∫ ω, (f k ω) ^ 2 ∂μ) n

/-- **Doob's L² maximal inequality in terms of the predictable quadratic
variation, finite horizon.** Let $\mu$ be a probability measure and let $(f_k)_{k \in \mathbb{N}}$
be a real-valued martingale with respect to a filtration $(\mathcal{F}_k)$ and $\mu$ such that
every $f_k$ is in $L^2(\mu)$ and $f_0 = 0$ almost everywhere, and let $A_n$ be its predictable
quadratic variation. Then for every $n \in \mathbb{N}$,
$\int (\max_{k \le n} |f_k|)^2 \, d\mu \le 4 \int A_n \, d\mu$. -/
theorem Martingale.doob_sq_maximal_ineq_predictableQuadraticVariation
    [IsProbabilityMeasure μ] (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ)
    (hf0 : f 0 =ᵐ[μ] 0) (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ := by
  have hf0int : ∫ ω, (f 0 ω) ^ 2 ∂μ = 0 := by
    have h : (fun ω => (f 0 ω) ^ 2) =ᵐ[μ] (0 : Ω → ℝ) := hf0.mono fun ω hω => by simp [hω]
    rw [integral_congr_ae h]
    simp
  have hEq : ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ =
      ∫ ω, (f n ω) ^ 2 ∂μ := by
    rw [hmart.integral_predictableQuadraticVariation hL2 n, hf0int, sub_zero]
  rw [hEq]
  exact hmart.doob_sq_maximal_ineq hL2 n

/-- **Doob's L² maximal inequality, infinite horizon.** Let $\mu$ be a probability measure, let
$(f_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to a filtration
$(\mathcal{F}_n)$ and $\mu$ such that every $f_n$ is in $L^2(\mu)$ and $f_0 = 0$ almost
everywhere, and let $A_n$ be its predictable quadratic variation. Then
$\int \sup_n |f_n|^2 \, d\mu \le 4 \int \sup_n \max(A_n, 0) \, d\mu$, where both integrals are
of $[0, \infty]$-valued functions and may be infinite.

Since each $A_n$ is nonnegative almost everywhere, the right side is $4\,\mathbb{E}[A_\infty]$
with $A_\infty = \sup_n A_n$. -/
theorem Martingale.doob_sq_maximal_ineq_iSup [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (hf0 : f 0 =ᵐ[μ] 0) :
    ∫⁻ ω, ⨆ n, ENNReal.ofReal (|f n ω| ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ⨆ n, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ := by
  -- Per-`n` bound in `∫⁻ ofReal` form.
  have hfin_enr : ∀ n, ∫⁻ ω, ENNReal.ofReal (
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |f k ω|) ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ := by
    intro n
    have hB := hmart.doob_sq_maximal_ineq_predictableQuadraticVariation hL2 hf0 n
    have hM_int : Integrable (fun ω =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |f k ω|) ^ 2) μ :=
      (memLp_runningMax hmart hL2 n).integrable_sq
    have hA_int : Integrable (predictableQuadraticVariation μ ℱ f n) μ :=
      integrable_predictableQuadraticVariation n
    have hA_nn : 0 ≤ᵐ[μ] predictableQuadraticVariation μ ℱ f n :=
      predictableQuadraticVariation_nonneg n
    have h1 : ENNReal.ofReal (∫ ω,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |f k ω|) ^ 2 ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            fun k => |f k ω|) ^ 2) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hM_int
        (Eventually.of_forall fun ω => sq_nonneg _)
    have h2 : ENNReal.ofReal (∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hA_int hA_nn
    calc ∫⁻ ω, ENNReal.ofReal (
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            fun k => |f k ω|) ^ 2) ∂μ
        = ENNReal.ofReal (∫ ω,
            ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              fun k => |f k ω|) ^ 2 ∂μ) := h1.symm
      _ ≤ ENNReal.ofReal (4 * ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ) :=
          ENNReal.ofReal_le_ofReal hB
      _ = 4 * ∫⁻ ω, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), h2]
          norm_num
  -- The pointwise supremum of the `|f n|²` is the supremum of the running maxima.
  have hsup_eq : ∀ ω, ⨆ n, ENNReal.ofReal (|f n ω| ^ 2) =
      ⨆ n, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |f k ω|) ^ 2) := by
    intro ω
    apply le_antisymm
    · apply iSup_le
      intro n
      apply le_iSup_of_le n
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    · apply iSup_le
      intro n
      rw [sup'_sq (Finset.range (n + 1)) (fun k => |f k ω|) Finset.nonempty_range_add_one
        (fun k _ => abs_nonneg _), ofReal_sup']
      exact Finset.sup'_le Finset.nonempty_range_add_one
        (fun k => ENNReal.ofReal (|f k ω| ^ 2)) fun k hk =>
        le_iSup (fun m => ENNReal.ofReal (|f m ω| ^ 2)) k
  calc ∫⁻ ω, ⨆ n, ENNReal.ofReal (|f n ω| ^ 2) ∂μ
      = ∫⁻ ω, ⨆ n, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |f k ω|) ^ 2) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact hsup_eq ω
    _ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => |f k ω|) ^ 2) ∂μ := by
        apply lintegral_iSup'
        · intro n
          exact (ENNReal.measurable_ofReal.comp
            ((measurable_runningMax hmart n).pow_const 2)).aemeasurable
        · apply Eventually.of_forall
          intro ω i j hij
          apply ENNReal.ofReal_le_ofReal
          apply pow_le_pow_left₀ (runningMax_nonneg i ω)
          exact Finset.sup'_mono (fun k => |f k ω|)
            (Finset.range_subset_range.mpr (Nat.succ_le_succ hij))
            Finset.nonempty_range_add_one
    _ ≤ ⨆ n, (4 * ∫⁻ ω, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ) :=
        iSup_mono fun n => hfin_enr n
    _ = 4 * ⨆ n, ∫⁻ ω, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ :=
        (ENNReal.mul_iSup 4 _).symm
    _ ≤ 4 * ∫⁻ ω, ⨆ n, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ :=
        mul_le_mul_of_nonneg_left (iSup_lintegral_le _) (by norm_num)

end MeasureTheory
