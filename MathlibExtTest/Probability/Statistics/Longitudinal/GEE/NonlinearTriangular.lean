/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.NonlinearTriangular
public import MathlibExtTest.Probability.Statistics.Longitudinal.GEE.TriangularArrays
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
open ProbabilityTheory.GEE.Triangular ProbabilityTheory.GEE.NonlinearTriangular

namespace MathlibExtTest.GEENonlinearTriangular

/-! ### Smoke tests -/

/-- `∑_{i<3} (i - 1) = 0`: `β = 1` is a root of `ψ_{n,i}(β) = i - β` in row `3`. -/
example : nonlinearEE (fun _ i β (_ : Unit) => (i : ℝ) - β) 3 1 () = 0 := by
  simp [nonlinearEE, sum_range_succ]
  norm_num

/-- Boundary `ε = 0` of the linearization bound: for an exactly linear `f β = c - D (β - β₀)`
the root satisfies `D (b - β₀) = f β₀` exactly. -/
example (c β₀ b : ℝ) (hb : b ∈ Metric.closedBall β₀ 1) (hroot : c - 2 * (b - β₀) = 0) :
    |2 * (b - β₀) - (c - 2 * (β₀ - β₀))| ≤ 0 / (1 - 0) * |c - 2 * (β₀ - β₀)| :=
  abs_linearization_sub_le (f := fun β => c - 2 * (β - β₀)) (f' := fun _ => -2)
    (by norm_num) le_rfl (by norm_num)
    (fun β _ => by simpa using ((hasDerivAt_id β).sub_const β₀).const_mul 2 |>.const_sub c)
    (fun β _ => by norm_num) hb hroot

/-! ### Non-vacuity: a smooth nonlinear mean model

Cluster `i` of row `n` contributes `ψ_{n,i}(β) = U n i + sinh β₀ - sinh β`, so
`Ψₙ(β) = ∑ᵢ U n i + n (sinh β₀ - sinh β)` is nonlinear in `β` with explicit root
`β̂ₙ = arsinh(sinh β₀ + ∑ᵢ U n i / n)`. Every hypothesis of `triangular_nonlinearEE_clt` other
than T36's score-array hypotheses on `U` is discharged below from the definitions, with
sensitivity `Dₙ = n cosh β₀`. -/

variable {Ω : Type*}

/-- The `sinh`-mean cluster estimating function. -/
noncomputable def sinhEE (U : ℕ → ℕ → Ω → ℝ) (β₀ : ℝ) (n i : ℕ) (β : ℝ) (ω : Ω) : ℝ :=
  U n i ω + (Real.sinh β₀ - Real.sinh β)

/-- Its derivative in `β`. -/
noncomputable def sinhEE' (_n _i : ℕ) (β : ℝ) (_ω : Ω) : ℝ := -Real.cosh β

/-- The explicit root `β̂ₙ = arsinh(sinh β₀ + ∑ᵢ U n i / n)`. -/
noncomputable def sinhRoot (U : ℕ → ℕ → Ω → ℝ) (β₀ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.arsinh (Real.sinh β₀ + (∑ i ∈ range n, U n i ω) / n)

lemma nonlinearEE_sinhEE (U : ℕ → ℕ → Ω → ℝ) (β₀ : ℝ) (n : ℕ) (β : ℝ) (ω : Ω) :
    nonlinearEE (sinhEE U β₀) n β ω =
      (∑ i ∈ range n, U n i ω) + n * (Real.sinh β₀ - Real.sinh β) := by
  simp [nonlinearEE, sinhEE, sum_add_distrib]
  ring

lemma nonlinearEE_sinhEE' (n : ℕ) (β : ℝ) (ω : Ω) :
    nonlinearEE (sinhEE' (Ω := Ω)) n β ω = -(n * Real.cosh β) := by
  simp [nonlinearEE, sinhEE']

/-- `sinhRoot` is an exact root in every row. -/
lemma nonlinearEE_sinhRoot (U : ℕ → ℕ → Ω → ℝ) (β₀ : ℝ) (n : ℕ) (ω : Ω) :
    nonlinearEE (sinhEE U β₀) n (sinhRoot U β₀ n ω) ω = 0 := by
  rw [nonlinearEE_sinhEE, sinhRoot, Real.sinh_arsinh]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

lemma antitone_nonlinearEE_sinhEE (U : ℕ → ℕ → Ω → ℝ) (β₀ : ℝ) (n : ℕ) (ω : Ω) :
    Antitone fun β => nonlinearEE (sinhEE U β₀) n β ω := by
  intro a b hab
  simp only [nonlinearEE_sinhEE]
  have := Real.sinh_strictMono.monotone hab
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The slope condition holds deterministically, by continuity of `cosh` at `β₀`. -/
lemma sinh_slope (β₀ : ℝ) : ∀ ε > 0, ∃ δ > 0, Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall β₀ δ,
    ε * (n * Real.cosh β₀) < |nonlinearEE (sinhEE' (Ω := Ω)) n β ω + n * Real.cosh β₀|}) atTop
    (𝓝 0) := by
  intro ε hε
  have hc : 0 < Real.cosh β₀ := Real.cosh_pos β₀
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 Real.continuous_cosh.continuousAt
    (ε * Real.cosh β₀) (by positivity)
  refine ⟨δ / 2, by positivity, tendsto_const_nhds.congr fun n => ?_⟩
  symm
  convert measure_empty (μ := μ)
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
  intro β hβ
  have hd : dist β β₀ < δ := lt_of_le_of_lt (Metric.mem_closedBall.1 hβ) (by linarith)
  have h1 := (hball hd).le
  rw [Real.dist_eq] at h1
  rw [nonlinearEE_sinhEE', show -(n * Real.cosh β) + n * Real.cosh β₀ =
    -(n * (Real.cosh β - Real.cosh β₀)) by ring, abs_neg, abs_mul, Nat.abs_cast]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The sign conditions follow from the triangular weak law `nonlinearEE_tendstoInMeasure_div`
with `aₙ = n`, for bounded scores and bounded cluster sizes. -/
lemma sinh_wlln [IsProbabilityMeasure μ] (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K M : ℝ}
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hM : ∀ n, ∀ i ∈ range n, K * m n i ≤ M) (β₀ β : ℝ) :
    TendstoInMeasure μ (fun n ω => nonlinearEE (sinhEE U β₀) n β ω / n) atTop
      (fun _ => Real.sinh β₀ - Real.sinh β) := by
  set c := Real.sinh β₀ - Real.sinh β with hcdef
  have hUL2 : ∀ n, ∀ i ∈ range n, MemLp (U n i) 2 μ := fun n i hi =>
    MemLp.of_bound (hmeas n i hi).aestronglyMeasurable (K * m n i)
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hbound n i hi ω)
  have hL2 : ∀ n, ∀ i ∈ range n, MemLp (sinhEE U β₀ n i β) 2 μ := fun n i hi =>
    (hUL2 n i hi).add (memLp_const c)
  refine nonlinearEE_tendstoInMeasure_div hL2 (fun n i hi j hj hij => ?_)
    ((eventually_ge_atTop 1).mono fun n hn => by positivity) ?_ ?_
  · exact ((hind n).indepFun (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by simpa using hij)).comp
      (measurable_id.add_const c) (measurable_id.add_const c)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hint : ∀ i ∈ range n, ∫ ω, sinhEE U β₀ n i β ω ∂μ = c := fun i hi => by
      simp only [sinhEE]
      rw [integral_add ((hUL2 n i hi).integrable one_le_two) (integrable_const c), hmean n i hi,
        integral_const, probReal_univ, smul_eq_mul, one_mul, zero_add]
    rw [sum_congr rfl hint, sum_const, card_range, nsmul_eq_mul]
    field_simp
  · have hvle : ∀ n, ∀ i ∈ range n, Var[sinhEE U β₀ n i β; μ] ≤ M ^ 2 := by
      intro n i hi
      change Var[fun ω => U n i ω + c; μ] ≤ M ^ 2
      rw [variance_add_const (hmeas n i hi).aestronglyMeasurable]
      refine (variance_le_expectation_sq (hmeas n i hi).aestronglyMeasurable).trans ?_
      have hb : ∀ ω, (U n i ^ 2) ω ≤ M ^ 2 := fun ω => by
        have h1 := (hbound n i hi ω).trans (hM n i hi)
        simp only [Pi.pow_apply]
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc μ[U n i ^ 2] ≤ ∫ _, M ^ 2 ∂μ :=
            integral_mono_of_nonneg (f := U n i ^ 2) (ae_of_all _ fun ω => sq_nonneg (U n i ω))
              (integrable_const _)
              (ae_of_all _ hb)
        _ = M ^ 2 := by simp
    have hlim : Tendsto (fun n : ℕ => M ^ 2 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (M ^ 2)
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
      (sum_nonneg fun i _ => variance_nonneg _ _) (sq_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]
    calc ∑ i ∈ range n, Var[sinhEE U β₀ n i β; μ] ≤ ∑ _i ∈ range n, M ^ 2 := sum_le_sum (hvle n)
      _ = M ^ 2 * (n : ℝ)⁻¹ * (n : ℝ) ^ 2 := by
          rw [sum_const, card_range, nsmul_eq_mul]; field_simp

/-- **Non-vacuity of `triangular_nonlinearEE_clt`.** For the nonlinear `sinh`-mean model with
explicit root `sinhRoot`, sensitivity `Dₙ = n cosh β₀`, and any score array `U` satisfying
T36's hypotheses with bounded cluster sizes, `n cosh β₀ (β̂ₙ - β₀) / Bₙ ⇒ N(0, 1)`. -/
theorem sinh_model_clt [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ)
    {K M : ℝ} (hK : 0 ≤ K) (β₀ : ℝ)
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hM : ∀ n, ∀ i ∈ range n, K * m n i ≤ M)
    (hpos : ∀ᶠ n in atTop, 0 < rowVariance U μ n)
    (hgrowth : Tendsto (fun n => K * maxClusterSize m n / √(rowVariance U μ n)) atTop (𝓝 0))
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ') :
    TendstoInDistribution (fun n ω => n * Real.cosh β₀ * (sinhRoot U β₀ n ω - β₀) /
      √(rowVariance U μ n)) atTop Y (fun _ => μ) μ' := by
  have hψ0 : ∀ n i, sinhEE U β₀ n i β₀ = U n i := fun n i => by
    funext ω; simp [sinhEE]
  have hc : 0 < Real.cosh β₀ := Real.cosh_pos β₀
  have hlim := sinh_wlln U m hind hmeas hmean hbound hM β₀
  have ha : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn
  have h := triangular_nonlinearEE_clt (μ := μ) (sinhEE U β₀) sinhEE' m hK (β₀ := β₀)
    (by simpa only [hψ0] using hind) (by simpa only [hψ0] using hmeas)
    (by simpa only [hψ0] using hmean) (by simpa only [hψ0] using hbound)
    (by simpa only [hψ0] using hpos) (by simpa only [hψ0] using hgrowth)
    (βhat := sinhRoot U β₀)
    (fun n => (Real.continuous_arsinh.measurable.comp (measurable_const.add
      ((Finset.measurable_fun_sum (range n) fun i hi => hmeas n i hi).div_const _))).aemeasurable)
    (by simp [nonlinearEE_sinhRoot])
    (antitone_nonlinearEE_sinhEE U β₀)
    (fun ε hε => tendsto_measure_nonpos_of_tendstoInMeasure
      (by simpa using Real.sinh_strictMono (by linarith : β₀ - ε < β₀)) ha (hlim _))
    (fun ε hε => tendsto_measure_nonneg_of_tendstoInMeasure
      (by simpa using Real.sinh_strictMono (by linarith : β₀ < β₀ + ε)) ha (hlim _))
    (fun n i ω β => by
      simpa [sinhEE, sinhEE'] using ((Real.hasDerivAt_sinh β).const_sub (Real.sinh β₀)).const_add
        (U n i ω))
    (ha.mono fun n hn => mul_pos hn hc) (sinh_slope β₀) hY
  simpa only [hψ0] using h

/-- Root consistency of `sinhRoot` from the limit form `tendstoInMeasure_root_of_limit`, with
`λ(β) = sinh β₀ - sinh β`. -/
example [IsProbabilityMeasure μ] (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K M : ℝ}
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hM : ∀ n, ∀ i ∈ range n, K * m n i ≤ M) (β₀ : ℝ) :
    TendstoInMeasure μ (sinhRoot U β₀) atTop (fun _ => β₀) :=
  tendstoInMeasure_root_of_limit (antitone_nonlinearEE_sinhEE U β₀)
    (by simp [nonlinearEE_sinhRoot])
    ((eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn)
    (sinh_wlln U m hind hmeas hmean hbound hM β₀)
    (fun ε _ => by simpa using Real.sinh_strictMono (by linarith : β₀ - ε < β₀))
    (fun ε _ => by simpa using Real.sinh_strictMono (by linarith : β₀ < β₀ + ε))

/-- Existence of a root in `(β₀ - ε, β₀ + ε)` with probability tending to one, from
`tendsto_measure_not_exists_root` (continuity of `sinh` plus the weak-law sign conditions). -/
example [IsProbabilityMeasure μ] (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K M : ℝ}
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hM : ∀ n, ∀ i ∈ range n, K * m n i ≤ M) (β₀ ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ¬ ∃ β ∈ Set.Ioo (β₀ - ε) (β₀ + ε),
      nonlinearEE (sinhEE U β₀) n β ω = 0}) atTop (𝓝 0) := by
  have ha : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn
  have hlim := sinh_wlln U m hind hmeas hmean hbound hM β₀
  refine tendsto_measure_not_exists_root hε (fun n ω => ?_)
    (tendsto_measure_nonpos_of_tendstoInMeasure
      (by simpa using Real.sinh_strictMono (by linarith : β₀ - ε < β₀)) ha (hlim _))
    (tendsto_measure_nonneg_of_tendstoInMeasure
      (by simpa using Real.sinh_strictMono (by linarith : β₀ < β₀ + ε)) ha (hlim _))
  have : (fun β => nonlinearEE (sinhEE U β₀) n β ω) =
      fun β => (∑ i ∈ range n, U n i ω) + n * (Real.sinh β₀ - Real.sinh β) :=
    funext fun β => nonlinearEE_sinhEE U β₀ n β ω
  rw [this]
  fun_prop

/-! ### Boundary: degenerate sensitivity

For the cubic mean `g(β) = β³` at `β₀ = 0` the slope `Ψ'ₙ(β) = -3 n β²` vanishes at the truth, so
the slope condition fails for every sensitivity `Dₙ > 0`: at `β = 0` the deviation `|0 + Dₙ|`
is the whole of `Dₙ`. -/

/-- Derivative of the cubic-mean cluster estimating function `U n i + β₀³ - β³`. -/
def cubicEE' (_n _i : ℕ) (β : ℝ) (_ω : Ω) : ℝ := -(3 * β ^ 2)

example [IsProbabilityMeasure μ] (D : ℕ → ℝ) (hD : ∀ᶠ n in atTop, 0 < D n) :
    ¬ ∀ ε > 0, ∃ δ > 0, Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall (0 : ℝ) δ,
      ε * D n < |nonlinearEE (cubicEE' (Ω := Ω)) n β ω + D n|}) atTop (𝓝 0) := by
  intro h
  obtain ⟨δ, hδ, hlim⟩ := h (1 / 2) (by norm_num)
  have hone : Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall (0 : ℝ) δ,
      1 / 2 * D n < |nonlinearEE (cubicEE' (Ω := Ω)) n β ω + D n|}) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hD] with n hn
    symm
    convert measure_univ (μ := μ)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨0, Metric.mem_closedBall_self hδ.le, ?_⟩
    simp only [nonlinearEE, cubicEE']
    norm_num
    rw [abs_of_pos hn]
    linarith
  exact zero_ne_one (tendsto_nhds_unique hlim hone)

/-! ### Boundary: no identification

With `Ψₙ ≡ 0` every `β` is a root, the estimating function is antitone, but the root sequence
`β̂ₙ = β₀ + 1` is not consistent: the sign condition of `tendstoInMeasure_root_of_antitone`
cannot be dropped, and indeed fails here. -/

example [IsProbabilityMeasure μ] (β₀ : ℝ) :
    Tendsto (fun n => μ {ω | nonlinearEE (fun _ _ _ (_ : Ω) => (0 : ℝ)) n (β₀ + 1) ω ≠ 0})
        atTop (𝓝 0) ∧
      (∀ n (ω : Ω), Antitone fun β => nonlinearEE (fun _ _ _ (_ : Ω) => (0 : ℝ)) n β ω) ∧
      ¬ TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β₀ + 1) atTop (fun _ => β₀) ∧
      ¬ ∀ ε > 0, Tendsto (fun n => μ {ω | nonlinearEE (fun _ _ _ (_ : Ω) => (0 : ℝ)) n (β₀ - ε) ω
        ≤ 0}) atTop (𝓝 0) := by
  refine ⟨by simp [nonlinearEE], fun n ω a b _ => by simp [nonlinearEE], fun h => ?_, fun h => ?_⟩
  · rw [tendstoInMeasure_iff_norm] at h
    have := h 1 one_pos
    simp only [add_sub_cancel_left, Real.norm_eq_abs, abs_one, le_refl, Set.ofPred_true,
      measure_univ] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  · have := h 1 one_pos
    simp only [nonlinearEE, sum_const_zero, le_refl, Set.ofPred_true, measure_univ] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-! ### Fully concrete instance: iid Rademacher clusters of size one

On `ℕ → Bool` with the product of fair coins (`fairCoin` from the T36 tests), cluster `i` of
every row has the score `±1` of coin `i`. All of T36's score-array hypotheses hold, so
`sinh_model_clt` applies with no remaining assumptions: `n cosh β₀ (β̂ₙ - β₀) / √n ⇒ N(0, 1)`. -/

/-- The `±1` value of a coin. -/
def rademacher (b : Bool) : ℝ := if b then 1 else -1

/-- Product of fair coins on `ℕ → Bool`. -/
noncomputable def coinProduct : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => MathlibExtTest.GEETriangular.fairCoin

instance : IsProbabilityMeasure coinProduct := by
  unfold coinProduct; infer_instance

/-- Cluster `i` of row `n` scores `±1` according to coin `i`. -/
def radArray (_n i : ℕ) (ω : ℕ → Bool) : ℝ := rademacher (ω i)

lemma measurable_radArray (n i : ℕ) : Measurable (radArray n i) :=
  (measurable_of_finite rademacher).comp (measurable_pi_apply i)

lemma integral_radArray_comp (g : ℝ → ℝ) (n i : ℕ) :
    ∫ ω, g (radArray n i ω) ∂coinProduct =
      ∫ b, g (rademacher b) ∂MathlibExtTest.GEETriangular.fairCoin := by
  rw [← Measure.infinitePi_map_eval (fun _ => MathlibExtTest.GEETriangular.fairCoin) i,
    integral_map (measurable_pi_apply i).aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  rfl

lemma fairCoin_integral (g : Bool → ℝ) :
    ∫ b, g b ∂MathlibExtTest.GEETriangular.fairCoin = (g true + g false) / 2 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  have htrue : MathlibExtTest.GEETriangular.fairCoin.real {true} = 1 / 2 := by
    simp [MathlibExtTest.GEETriangular.fairCoin, Measure.real]
  have hfalse : MathlibExtTest.GEETriangular.fairCoin.real {false} = 1 / 2 := by
    simp [MathlibExtTest.GEETriangular.fairCoin, Measure.real]
  rw [htrue, hfalse, smul_eq_mul, smul_eq_mul]
  ring

lemma rowVariance_radArray (n : ℕ) : rowVariance radArray coinProduct n = n := by
  have h1 : ∀ i, ∫ ω, radArray n i ω ^ 2 ∂coinProduct = 1 := fun i => by
    rw [integral_radArray_comp (fun x => x ^ 2), fairCoin_integral]
    norm_num [rademacher]
  simp [rowVariance, h1]

/-- **Fully concrete non-vacuity.** For iid Rademacher clusters and the nonlinear `sinh`-mean
estimating equation, `n cosh β₀ (β̂ₙ - β₀) / √n ⇒ N(0, 1)`. -/
theorem rademacher_sinh_clt (β₀ : ℝ) :
    TendstoInDistribution (fun n ω => n * Real.cosh β₀ * (sinhRoot radArray β₀ n ω - β₀) /
      √(n : ℝ)) atTop id (fun _ => coinProduct) (gaussianReal 0 1) := by
  have h := sinh_model_clt (μ := coinProduct) (μ' := gaussianReal 0 1) radArray (fun _ _ => 1)
    (K := 1) (M := 1) zero_le_one β₀
    (fun n => by
      have h := (iIndepFun_infinitePi (P := fun _ => MathlibExtTest.GEETriangular.fairCoin)
        (X := fun _ => rademacher) (fun _ => measurable_of_finite _)).precomp
        (g := ((↑) : range n → ℕ)) Subtype.val_injective
      exact h)
    (fun n i _ => measurable_radArray n i)
    (fun n i _ => by
      have h := integral_radArray_comp id n i
      simp only [id] at h
      rw [h, fairCoin_integral]; norm_num [rademacher])
    (fun n i _ ω => by simp only [radArray, rademacher]; split_ifs <;> norm_num)
    (fun _ _ _ => by norm_num)
    (by
      refine (eventually_ge_atTop 1).mono fun n hn => ?_
      rw [rowVariance_radArray]; exact_mod_cast hn)
    (by
      have hlim := tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hne : (range n).Nonempty := nonempty_range_iff.2 (by omega)
      have hM : maxClusterSize (fun _ _ => 1) n = 1 := Finset.sup_const hne _
      simp [rowVariance_radArray, hM])
    HasLaw.id
  simpa only [rowVariance_radArray] using h

end MathlibExtTest.GEENonlinearTriangular
