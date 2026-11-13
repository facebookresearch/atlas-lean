/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.McLeishCLT
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.BorelCantelli

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale

namespace MathlibExtTest.Probability.Martingale.McLeishCLT

noncomputable section

/-! ### Boundary: the zero array

All hypotheses hold for the zero array with `v = 0`; the conclusion is convergence to
`N(0, 0) = δ₀`. -/

example {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) :
    TendstoInDistribution (fun n (_ : Ω) => ∑ _k ∈ range n, (0 : ℝ)) atTop id (fun _ => μ)
      (gaussianReal 0 0) := by
  refine tendstoInDistribution_martingale_mcLeish (fun _ _ _ => (0 : ℝ)) (fun _ => F) id
    (fun n => ?_) ⟨0, by simp, Eventually.of_forall fun n => by simp⟩ (fun ε hε => ?_) 0 ?_
  · have : (fun k (ω : Ω) => ∑ j ∈ range k, (0 : ℝ)) = 0 := by funext; simp
    rw [this]; exact martingale_zero (E := ℝ) F μ
  · simp [not_lt.2 hε.le]
  · intro ε hε
    simp [hε.ne']

/-! ### A non-degenerate instance: the Rademacher walk

Coordinates of `ℕ → Bool` under the product of fair coin measures give independent signs
`ξ k = ±1`. The array `X n k = ξ (k + 1) / √n` is a martingale difference array for the natural
filtration of `ξ`, with realized quadratic variation identically `1` (for `n ≥ 1`) and maximal
increment `1 / √n`. McLeish's theorem gives the CLT `∑_{k<n} ξ (k+1) / √n → N(0, 1)`; every
hypothesis is discharged from the definitions below. -/

/-- The fair coin on `Bool`. -/
def fairCoin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := ⟨by
  simp only [fairCoin, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]⟩

/-- The sign of a coin: `true ↦ 1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Product of fair coins on `ℕ → Bool`. -/
def coins : Measure (ℕ → Bool) := Measure.infinitePi fun _ => fairCoin

instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

/-- The Rademacher signs. -/
def ξ (k : ℕ) (ω : ℕ → Bool) : ℝ := sgn (ω k)

lemma measurable_sgn : Measurable sgn := measurable_of_countable _

lemma stronglyMeasurable_ξ (k : ℕ) : StronglyMeasurable (ξ k) :=
  (measurable_sgn.comp (measurable_pi_apply k)).stronglyMeasurable

lemma abs_ξ (k : ℕ) (ω : ℕ → Bool) : |ξ k ω| = 1 := by
  unfold ξ sgn; split_ifs <;> simp

lemma iIndepFun_ξ : iIndepFun ξ coins :=
  iIndepFun_infinitePi (X := fun _ => sgn) fun _ => measurable_sgn

lemma integral_ξ (k : ℕ) : ∫ ω, ξ k ω ∂coins = 0 := by
  have h : ∫ ω, sgn (ω k) ∂coins = ∫ b, sgn b ∂fairCoin := by
    rw [← Measure.infinitePi_map_eval (fun _ => fairCoin) k, integral_map
      (measurable_pi_apply k).aemeasurable measurable_sgn.aestronglyMeasurable]
    rfl
  unfold ξ
  rw [h, fairCoin, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp [sgn]

/-- The natural filtration of the signs. -/
def coinFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  Filtration.natural ξ stronglyMeasurable_ξ

/-- The Rademacher array. -/
def rademacherArray (n k : ℕ) (ω : ℕ → Bool) : ℝ := ξ (k + 1) ω / Real.sqrt n

lemma martingale_rademacherArray (n : ℕ) :
    Martingale (fun k ω => ∑ j ∈ range k, rademacherArray n j ω) coinFiltration coins := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_) (fun k => ?_) fun k => ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hjk : j + 1 ≤ k := mem_range.1 hj
    exact (((Filtration.stronglyAdapted_natural stronglyMeasurable_ξ (j + 1)).mono
      (coinFiltration.mono hjk)).measurable.div_const _).stronglyMeasurable
  · refine integrable_finsetSum _ fun j _ => ?_
    refine Integrable.of_bound (C := 1 / Real.sqrt n)
      ((stronglyMeasurable_ξ (j + 1)).measurable.div_const _).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [rademacherArray, Real.norm_eq_abs, abs_div, abs_ξ, abs_of_nonneg (Real.sqrt_nonneg _)]
  · have hd : ((fun ω => ∑ j ∈ range (k + 1), rademacherArray n j ω) -
        fun ω => ∑ j ∈ range k, rademacherArray n j ω) = (Real.sqrt n)⁻¹ • ξ (k + 1) := by
      funext ω; simp [sum_range_succ, rademacherArray, div_eq_inv_mul]
    rw [hd]
    filter_upwards [condExp_smul (Real.sqrt n)⁻¹ (ξ (k + 1)) (coinFiltration k),
      iIndepFun_ξ.condExp_natural_ae_eq_of_lt stronglyMeasurable_ξ (Nat.lt_succ_self k)]
      with ω h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change (Real.sqrt n)⁻¹ * coins[ξ (k + 1) | coinFiltration k] ω = 0
    rw [show coinFiltration = Filtration.natural ξ stronglyMeasurable_ξ from rfl, h2,
      integral_ξ, mul_zero]

lemma abs_rademacherArray (n k : ℕ) (ω : ℕ → Bool) :
    |rademacherArray n k ω| = 1 / Real.sqrt n := by
  rw [rademacherArray, abs_div, abs_ξ, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma sum_sq_rademacherArray {n : ℕ} (hn : n ≠ 0) (ω : ℕ → Bool) :
    ∑ k ∈ range n, rademacherArray n k ω ^ 2 = 1 := by
  have h : ∀ k, rademacherArray n k ω ^ 2 = 1 / n := by
    intro k
    rw [← sq_abs, abs_rademacherArray, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
  simp only [h, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- **The Rademacher CLT from McLeish's theorem**, with every hypothesis discharged. -/
theorem tendstoInDistribution_rademacher :
    TendstoInDistribution (fun n ω => ∑ k ∈ range n, rademacherArray n k ω) atTop id
      (fun _ => coins) (gaussianReal 0 1) := by
  refine tendstoInDistribution_martingale_mcLeish rademacherArray (fun _ => coinFiltration) id
    martingale_rademacherArray ⟨1, by simp, Eventually.of_forall fun n => ?_⟩
    (fun ε hε => ?_) 1 ?_
  · -- (a): every squared increment is `1 / n ≤ 1`
    refine (lintegral_mono (g := fun _ => (1 : ℝ≥0∞)) fun ω => iSup₂_le fun k _ => ?_).trans
      (by simp)
    rw [Real.enorm_eq_ofReal_abs, abs_rademacherArray, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_le_one, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg n)
  · -- (b): the maximal increment `1 / √n` is eventually below `ε`
    refine tendsto_const_nhds.congr' ?_
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
    have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
      not_lt, abs_rademacherArray]
    intro k _
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  · -- (c): the realized quadratic variation is eventually exactly `1`
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp [sum_sq_rademacherArray hn, hε.ne']

/-! ### The Lindeberg form on the same array -/

/-- The Rademacher CLT again, through the Lindeberg-condition corollary. -/
example : TendstoInDistribution (fun n ω => ∑ k ∈ range n, rademacherArray n k ω) atTop id
    (fun _ => coins) (gaussianReal 0 1) := by
  have hmeas : ∀ n k, Measurable (rademacherArray n k) := fun n k =>
    (stronglyMeasurable_ξ (k + 1)).measurable.div_const _
  refine tendstoInDistribution_martingale_lindeberg rademacherArray (fun _ => coinFiltration)
    martingale_rademacherArray (fun n k _ => ?_) (fun ε hε => ?_) 1 ?_
  · refine Integrable.of_bound (C := 1) ((hmeas n k).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_rademacherArray, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg n)
  · -- every truncated second moment vanishes once `1 / √n < ε`
    refine tendsto_const_nhds.congr' ?_
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
    have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
    symm
    refine sum_eq_zero fun k _ => ?_
    have hz : ∀ ω, Set.indicator {ω' | ε < |rademacherArray n k ω'|} 1 ω = (0 : ℝ) := by
      intro ω
      refine Set.indicator_of_notMem ?_ _
      simp only [Set.mem_ofPred_eq, not_lt, abs_rademacherArray]
      rw [div_le_iff₀ hpos]
      rw [div_lt_iff₀ hε] at hn
      linarith
    simp [hz]
  · intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp [sum_sq_rademacherArray hn, hε.ne']

/-! ### Finite-dimensional convergence -/

/-- Boundary: the zero array along an arbitrary real time axis, with `A ≡ 0` and the zero limit
process (whose finite-dimensional laws are the degenerate Gaussians `N(0, 0)`). Every finite set
of times is allowed. -/
example {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (N : ℕ → ℝ → ℕ) (hN : ∀ n, Monotone (N n)) (hNr : ∀ n s, N n s ≤ n)
    (I : Finset ℝ) :
    TendstoInDistribution (fun n (_ : Ω) => I.restrict fun s => ∑ _k ∈ range (N n s), (0 : ℝ))
      atTop (fun (_ : ℝ) => I.restrict fun _ => (0 : ℝ)) (fun _ => μ) (gaussianReal 0 1) := by
  refine tendstoInDistribution_fdd_martingale_mcLeish (fun _ _ _ => (0 : ℝ)) (fun _ => F) id
    (fun n => ?_) ⟨0, by simp, Eventually.of_forall fun n => by simp⟩ (fun ε hε => ?_) N hN hNr
    (fun _ => 0) (fun s => ?_) (fun _ _ => 0) (fun _ => measurable_const) (fun J c => ?_) I
  · have : (fun k (_ : Ω) => ∑ _j ∈ range k, (0 : ℝ)) = 0 := by funext; simp
    rw [this]; exact martingale_zero (E := ℝ) F μ
  · simp [not_lt.2 hε.le]
  · intro ε hε
    simp [hε.ne']
  · simp [gaussianReal_zero_var]

/-- Non-degenerate single-time instance: the Rademacher array against `Z = id` under
`N(0, 1)`. This also exhibits a limit process satisfying the Gaussian hypothesis `hZ` with a
nonzero covariance. -/
example (I : Finset Unit) :
    TendstoInDistribution
      (fun n ω => I.restrict fun _ => ∑ k ∈ range n, rademacherArray n k ω) atTop
      (fun x : ℝ => I.restrict fun _ => x) (fun _ => coins) (gaussianReal 0 1) := by
  refine tendstoInDistribution_fdd_martingale_mcLeish rademacherArray (fun _ => coinFiltration) id
    martingale_rademacherArray ⟨1, by simp, Eventually.of_forall fun n => ?_⟩ (fun ε hε => ?_)
    (fun n _ => n) (fun _ => monotone_const) (fun _ _ => le_rfl) (fun _ => 1) (fun _ => ?_)
    (fun _ x => x) (fun _ => measurable_id) (fun J c => ?_) I
  · refine (lintegral_mono (g := fun _ => (1 : ℝ≥0∞)) fun ω => iSup₂_le fun k _ => ?_).trans
      (by simp)
    rw [Real.enorm_eq_ofReal_abs, abs_rademacherArray, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_le_one, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg n)
  · refine tendsto_const_nhds.congr' ?_
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
    have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
      not_lt, abs_rademacherArray]
    intro k _
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  · intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp [sum_sq_rademacherArray hn, hε.ne']
  · -- `∑ c_s x = (∑ c_s) x` is `N(0, (∑ c_s)²)` under `N(0, 1)`
    have h1 : (fun x : ℝ => ∑ s : J, c s * x) = fun x => (∑ s : J, c s) * x := by
      funext x; rw [sum_mul]
    have h2 : ∑ s : J, ∑ u : J, c s * c u * (1 : ℝ) = (∑ s : J, c s) ^ 2 := by
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun s _ => sum_congr rfl fun u _ => mul_one _
    rw [h1, h2, gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact (Real.toNNReal_of_nonneg (sq_nonneg _)).symm

lemma sum_sq_rademacherArray_range (n m : ℕ) (ω : ℕ → Bool) :
    ∑ k ∈ range m, rademacherArray n k ω ^ 2 = m / n := by
  have h : ∀ k, rademacherArray n k ω ^ 2 = 1 / n := by
    intro k
    rw [← sq_abs, abs_rademacherArray, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
  simp only [h, sum_const, card_range, nsmul_eq_mul]
  ring

/-- **Donsker-type finite-dimensional convergence for the Rademacher walk** on `[0, 1]`: with
`N n s = ⌊n s⌋`, the quadratic variation at time `s` is `⌊n s⌋ / n → s`, so for any process `Z`
with the Gaussian finite-dimensional laws of Brownian motion (covariance `min s u`), the
finite-dimensional distributions of the rescaled walk converge to those of `Z`. All hypotheses
except the existence of `Z` are discharged. This is the step-sum shape of the hypothesis `hT81`
of T82's `tendstoInDistribution_arrayStepProcess`, not the input `hfdd` of
`tendstoInDistribution_skorokhod_of_tight_of_fdd` (which concerns continuous processes). -/
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : Set.Icc (0 : ℝ) 1 → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (J : Finset (Set.Icc (0 : ℝ) 1)) (c : J → ℝ),
      P'.map (fun ω => ∑ s : J, c s * Z s ω) = gaussianReal 0
        (∑ s : J, ∑ u : J, c s * c u * ((min (s : Set.Icc (0 : ℝ) 1) u : Set.Icc (0 : ℝ) 1) :
          ℝ)).toNNReal)
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict fun s => ∑ k ∈ range ⌊(n : ℝ) * s⌋₊, rademacherArray n k ω)
      atTop (fun ω => I.restrict fun s => Z s ω) (fun _ => coins) P' := by
  refine tendstoInDistribution_fdd_martingale_mcLeish rademacherArray (fun _ => coinFiltration) id
    martingale_rademacherArray ⟨1, by simp, Eventually.of_forall fun n => ?_⟩ (fun ε hε => ?_)
    (fun (n : ℕ) (s : Set.Icc (0 : ℝ) 1) => ⌊(n : ℝ) * s⌋₊)
    (fun (n : ℕ) s t hst => Nat.floor_mono (mul_le_mul_of_nonneg_left
      (show (s : ℝ) ≤ t from hst) (Nat.cast_nonneg n)))
    (fun n s => ?_) (fun s => (s : ℝ)) (fun s => ?_) Z hZm hZ I
  · refine (lintegral_mono (g := fun _ => (1 : ℝ≥0∞)) fun ω => iSup₂_le fun k _ => ?_).trans
      (by simp)
    rw [Real.enorm_eq_ofReal_abs, abs_rademacherArray, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_le_one, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg n)
  · refine tendsto_const_nhds.congr' ?_
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
    have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
      not_lt, abs_rademacherArray]
    intro k _
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  · -- `⌊n s⌋ ≤ n` since `s ≤ 1`
    have h1 : (n : ℝ) * s ≤ n := by
      have := s.2.2; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa using Nat.floor_le_floor h1
  · -- the quadratic variation at time `s` is the deterministic `⌊n s⌋ / n → s`
    refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
    have hlim : Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 (s : ℝ)) := by
      have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) s.2.1).comp tendsto_natCast_atTop_atTop
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, mul_comm (s : ℝ)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) ε hε] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
      sum_sq_rademacherArray_range]
    exact hn

/-! ### Lindeberg form of finite-dimensional convergence -/

lemma lindeberg_rademacherArray : LindebergConditionTriangular rademacherArray coins := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
  have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
  symm
  refine sum_eq_zero fun k _ => ?_
  have hz : ∀ ω, Set.indicator {ω' | ε < |rademacherArray n k ω'|} 1 ω = (0 : ℝ) := by
    intro ω
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_ofPred_eq, not_lt, abs_rademacherArray]
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  simp [hz]

lemma integrable_sq_rademacherArray (n k : ℕ) :
    Integrable (fun ω => rademacherArray n k ω ^ 2) coins := by
  refine Integrable.of_bound (C := 1)
    (((stronglyMeasurable_ξ (k + 1)).measurable.div_const _).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_rademacherArray, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact div_le_one_of_le₀ (by exact_mod_cast h) (Nat.cast_nonneg n)

/-- The Donsker-type finite-dimensional statement again, through the Lindeberg corollary
`tendstoInDistribution_fdd_martingale_lindeberg` (the form with the hypotheses named in the
task: quadratic-variation convergence plus the Lindeberg condition). -/
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : Set.Icc (0 : ℝ) 1 → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (J : Finset (Set.Icc (0 : ℝ) 1)) (c : J → ℝ),
      P'.map (fun ω => ∑ s : J, c s * Z s ω) = gaussianReal 0
        (∑ s : J, ∑ u : J, c s * c u * ((min (s : Set.Icc (0 : ℝ) 1) u : Set.Icc (0 : ℝ) 1) :
          ℝ)).toNNReal)
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict fun s => ∑ k ∈ range ⌊(n : ℝ) * s⌋₊, rademacherArray n k ω)
      atTop (fun ω => I.restrict fun s => Z s ω) (fun _ => coins) P' := by
  refine tendstoInDistribution_fdd_martingale_lindeberg rademacherArray (fun _ => coinFiltration)
    martingale_rademacherArray (fun n k _ => integrable_sq_rademacherArray n k)
    lindeberg_rademacherArray
    (fun (n : ℕ) (s : Set.Icc (0 : ℝ) 1) => ⌊(n : ℝ) * s⌋₊)
    (fun (n : ℕ) s t hst => Nat.floor_mono (mul_le_mul_of_nonneg_left
      (show (s : ℝ) ≤ t from hst) (Nat.cast_nonneg n)))
    (fun n s => ?_) (fun s => (s : ℝ)) (fun s => ?_) Z hZm hZ I
  · have h1 : (n : ℝ) * s ≤ n := by
      have := s.2.2; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa using Nat.floor_le_floor h1
  · refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
    have hlim : Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 (s : ℝ)) := by
      have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) s.2.1).comp tendsto_natCast_atTop_atTop
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, mul_comm (s : ℝ)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) ε hε] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
      sum_sq_rademacherArray_range]
    exact hn

/-! ### The `hT81` form on `[0,1]` -/

/-- The Rademacher walk through `tendstoInDistribution_fdd_martingaleDifference_floor`, whose
conclusion is the hypothesis `hT81` of T82's `tendstoInDistribution_arrayStepProcess`. The array
hypotheses, the Lindeberg condition and the realized quadratic variation `⌊n t⌋ / n → t` are all
discharged; only the measurable limit `Z : Ω' → C([0,1])` with Brownian finite-dimensional laws
is assumed. -/
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZm : Measurable Z)
    (hZ : ∀ (I : Finset (Set.Icc (0 : ℝ) 1)) (c : I → ℝ),
      P'.map (fun ω => ∑ s : I, c s * Z ω s) = gaussianReal 0
        (∑ s : I, ∑ u : I, c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal) :
    ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊,
        rademacherArray n i ω))
      atTop (fun ω => I.restrict (fun t => Z ω t)) (fun _ => coins) P' := by
  refine tendstoInDistribution_fdd_martingaleDifference_floor (𝓕 := fun _ => coinFiltration)
    (fun n i => ?_) (fun n i => ?_) (fun n i => ?_) lindeberg_rademacherArray (fun t => ?_)
    Z hZm hZ
  · exact ((Filtration.stronglyAdapted_natural stronglyMeasurable_ξ (i + 1)).measurable.div_const
      _).stronglyMeasurable
  · have hd : rademacherArray n i = (Real.sqrt n)⁻¹ • ξ (i + 1) := by
      funext ω; simp [rademacherArray, div_eq_inv_mul]
    rw [hd]
    filter_upwards [condExp_smul (Real.sqrt n)⁻¹ (ξ (i + 1)) (coinFiltration i),
      iIndepFun_ξ.condExp_natural_ae_eq_of_lt stronglyMeasurable_ξ (Nat.lt_succ_self i)]
      with ω h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [show coinFiltration = Filtration.natural ξ stronglyMeasurable_ξ from rfl, h2,
      integral_ξ, mul_zero]
  · refine MemLp.of_bound
      ((stronglyMeasurable_ξ (i + 1)).measurable.div_const _).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_rademacherArray]
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast h)) (Real.sqrt_nonneg _)
  · refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
    have hlim : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t.1⌋₊ : ℝ) / n) atTop (𝓝 t.1) := by
      have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) t.2.1).comp tendsto_natCast_atTop_atTop
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, mul_comm t.1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) ε hε] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
      sum_sq_rademacherArray_range]
    exact hn

/-! ### Public helpers -/

/-- The cut bound is attained: with `c ≡ 1` and `K = 2`, exactly two terms are kept. Computed
from the definition, not through `sum_range_cut_le`. -/
example : ∑ k ∈ range 5, (if ∑ _j ∈ range (k + 1), (1 : ℝ) ≤ 2 then (1 : ℝ) else 0) = 2 := by
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, sum_range_succ, range_zero,
    sum_empty]
  norm_num

/-- A sequence with a negative term: `c = (3, -3, 1, 0, 0, …)`. -/
def cutSeq (k : ℕ) : ℝ := if k = 0 then 3 else if k = 1 then -3 else if k = 2 then 1 else 0

/-- With `K = 1` the cut drops `c 0 = 3` (running sum `3 > 1`) and keeps the later terms
(running sums `0` and `1`), so the kept sum is `-3 + 1 = -2`. Computed from the definition. -/
example : ∑ k ∈ range 3, (if ∑ j ∈ range (k + 1), cutSeq j ≤ 1 then cutSeq k else 0) = -2 := by
  simp only [sum_range_succ, range_zero, sum_empty, cutSeq]
  norm_num

/-- The cut bound needs no sign condition on `c`. -/
example : ∑ k ∈ range 3, (if ∑ j ∈ range (k + 1), cutSeq j ≤ 1 then cutSeq k else 0) ≤ 1 :=
  sum_range_cut_le cutSeq zero_le_one 3

example (c : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range m, (if ∑ j ∈ range (k + 1), c j ≤ 2 then c k else 0) ≤ 2 :=
  sum_range_cut_le c zero_le_two m

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (h : Martingale (fun k ω => ∑ j ∈ range k, X j ω) F μ) (k : ℕ) :
    μ[X k | F k] =ᵐ[μ] 0 :=
  (martingale_increment h k).2.2

example {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {f f' : ℕ → Ω → ℝ}
    {g g' : Ω → ℝ} (hf : TendstoInMeasure μ f atTop g) (hf' : TendstoInMeasure μ f' atTop g') :
    TendstoInMeasure μ (fun n ω => f n ω + f' n ω) atTop (fun ω => g ω + g' ω) :=
  tendstoInMeasure_add hf hf'

end

end MathlibExtTest.Probability.Martingale.McLeishCLT
