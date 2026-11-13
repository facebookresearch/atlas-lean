/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.ConditionalVarianceCLT
public import MathlibExtTest.Probability.Martingale.McLeishCLT

/-!
# Tests for the conditional-variance martingale CLT

The zero array (boundary, `v = 0`) and the Rademacher array `ξ (k+1) / √n` of the McLeish tests,
with every hypothesis of the conditional-variance theorems discharged from the definitions:
the predictable quadratic variation of the Rademacher array is computed directly as
`∑_{k<m} E[1/n | F k] = m / n`, and the conditional Lindeberg sum vanishes once `1/√n < ε`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale
open MathlibExtTest.Probability.Martingale.McLeishCLT

namespace MathlibExtTest.Probability.Martingale.ConditionalVarianceCLT

noncomputable section

/-! ### Boundary: the zero array

All hypotheses hold for the zero array with `v = 0` (computed from the definitions); the
conclusion is convergence to `N(0, 0) = δ₀`. -/

/-- The predictable quadratic variation of the zero martingale is `0`. -/
lemma predictableQuadraticVariation_zero {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (F : Filtration ℕ m0) (m : ℕ) :
    predictableQuadraticVariation μ F (fun k (_ : Ω) => ∑ _j ∈ range k, (0 : ℝ)) m = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

example {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (r : ℕ → ℕ) :
    TendstoInDistribution (fun n (_ : Ω) => ∑ _k ∈ range (r n), (0 : ℝ)) atTop id (fun _ => μ)
      (gaussianReal 0 0) := by
  refine tendstoInDistribution_martingale_condVar (fun _ _ _ => (0 : ℝ)) (fun _ => F) r
    (fun n => ?_) (fun _ _ => MemLp.zero) 0 ?_ (fun ε hε => ?_)
  · have : (fun k (ω : Ω) => ∑ j ∈ range k, (0 : ℝ)) = 0 := by funext; simp
    rw [this]; exact martingale_zero (E := ℝ) F μ
  · simp only [predictableQuadraticVariation_zero]
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simp [not_le.2 hε]
  · rw [tendstoInMeasure_iff_dist]
    intro δ hδ
    simp [not_le.2 hδ]

/-! ### The Rademacher array -/

lemma sq_rademacherArray (n k : ℕ) (ω : ℕ → Bool) : rademacherArray n k ω ^ 2 = 1 / n := by
  rw [← sq_abs, abs_rademacherArray, div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]

/-- **Predictable quadratic variation, from the definition.** The conditional variance of
`ξ (k+1) / √n` is the constant `1/n`, so the predictable quadratic variation up to `m` is
`m / n`. -/
lemma predictableQuadraticVariation_rademacherArray (n m : ℕ) (ω : ℕ → Bool) :
    predictableQuadraticVariation coins coinFiltration
      (fun k ω => ∑ j ∈ range k, rademacherArray n j ω) m ω = m / n := by
  have hk : ∀ k, (fun ω' => (∑ j ∈ range (k + 1), rademacherArray n j ω' -
      ∑ j ∈ range k, rademacherArray n j ω') ^ 2) = fun _ => (1 / n : ℝ) := by
    intro k; funext ω'
    simp [sum_range_succ, sq_rademacherArray]
  simp only [predictableQuadraticVariation, hk, condExp_const (coinFiltration.le _),
    sum_const, card_range, nsmul_eq_mul]
  ring

lemma memLp_rademacherArray (n k : ℕ) : MemLp (rademacherArray n k) 2 coins := by
  refine MemLp.of_bound
    ((stronglyMeasurable_ξ (k + 1)).measurable.div_const _).aestronglyMeasurable 1
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_rademacherArray]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact div_le_one_of_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast h)) (Real.sqrt_nonneg _)

/-- **Conditional Lindeberg, from the definition.** Once `1/√n ≤ ε`, every big-jump indicator
vanishes, so the conditional Lindeberg sum is identically `0`. -/
lemma condLindeberg_rademacherArray (r : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    TendstoInMeasure coins (fun n ω => ∑ k ∈ range (r n),
      (coins[{ω' | ε < |rademacherArray n k ω'|}.indicator
        (fun ω' => rademacherArray n k ω' ^ 2) | coinFiltration k]) ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  refine tendsto_const_nhds.congr' ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (1 / ε)] with n hn
  have hpos : 0 < Real.sqrt n := (one_div_pos.2 hε).trans hn
  have hz : ∀ k, {ω' | ε < |rademacherArray n k ω'|}.indicator
      (fun ω' => rademacherArray n k ω' ^ 2) = 0 := by
    intro k; funext ω
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_ofPred_eq, not_lt, abs_rademacherArray]
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hn
    linarith
  symm
  simp [hz, not_le.2 hδ]

/-- **The Rademacher CLT from the conditional-variance theorem**, with every hypothesis
discharged: predictable quadratic variation `n / n = 1` and the conditional Lindeberg
condition. -/
example : TendstoInDistribution (fun n ω => ∑ k ∈ range n, rademacherArray n k ω) atTop id
    (fun _ => coins) (gaussianReal 0 1) := by
  refine tendstoInDistribution_martingale_condVar rademacherArray (fun _ => coinFiltration) id
    martingale_rademacherArray memLp_rademacherArray 1 ?_
    (fun ε hε => condLindeberg_rademacherArray id ε hε)
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  symm
  convert measure_empty (μ := coins)
  ext ω
  simp only [id, predictableQuadraticVariation_rademacherArray, NNReal.coe_one,
    div_self hn', dist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_le]
  exact hε

/-- The same CLT through the unconditional-Lindeberg corollary. -/
example : TendstoInDistribution (fun n ω => ∑ k ∈ range n, rademacherArray n k ω) atTop id
    (fun _ => coins) (gaussianReal 0 1) := by
  refine tendstoInDistribution_martingale_condVar_lindeberg rademacherArray
    (fun _ => coinFiltration) martingale_rademacherArray memLp_rademacherArray
    lindeberg_rademacherArray 1 ?_
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  symm
  convert measure_empty (μ := coins)
  ext ω
  simp only [predictableQuadraticVariation_rademacherArray, NNReal.coe_one,
    div_self hn', dist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_le]
  exact hε

/-! ### The `hT81` form on `[0,1]` from the predictable quadratic variation -/

/-- The Rademacher walk through `tendstoInDistribution_fdd_martingaleDifference_floor_condVar`:
T82's array hypotheses, its predictable quadratic variation `⌊n t⌋ / n → t` (computed from the
definition, `E[ξ² | F] = 1/n`) and the Lindeberg condition are discharged; no realized
quadratic variation is supplied. Only the measurable Brownian limit `Z` is assumed. -/
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZm : Measurable Z)
    (hZ : ∀ (I : Finset (Set.Icc (0 : ℝ) 1)) (c : I → ℝ),
      P'.map (fun ω => ∑ s : I, c s * Z ω s) = gaussianReal 0
        (∑ s : I, ∑ u : I, c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal) :
    ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊,
        rademacherArray n i ω))
      atTop (fun ω => I.restrict (fun t => Z ω t)) (fun _ => coins) P' := by
  refine tendstoInDistribution_fdd_martingaleDifference_floor_condVar
    (𝓕 := fun _ => coinFiltration) (fun n i => ?_) (fun n i => ?_) (fun n i =>
      memLp_rademacherArray n i) (fun t ht => ?_) lindeberg_rademacherArray Z hZm hZ
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
  · have hsum : ∀ (n : ℕ) (ω : ℕ → Bool), ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊,
        (coins[fun ω => rademacherArray n j ω ^ 2 | coinFiltration j]) ω =
        (⌊(n : ℝ) * t⌋₊ : ℝ) / n := by
      intro n ω
      have hj : ∀ j, (fun ω => rademacherArray n j ω ^ 2) = fun _ => (1 / n : ℝ) := by
        intro j; funext ω; exact sq_rademacherArray n j ω
      simp only [hj, condExp_const (coinFiltration.le _), sum_const, card_range, nsmul_eq_mul]
      ring
    refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
    have hlim : Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) / n) atTop (𝓝 t) := by
      have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ht.1).comp tendsto_natCast_atTop_atTop
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, mul_comm t]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Metric.tendsto_nhds.1 hlim) ε hε] with n hn
    symm
    convert measure_empty (μ := coins)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, hsum]
    exact hn

end

end MathlibExtTest.Probability.Martingale.ConditionalVarianceCLT
