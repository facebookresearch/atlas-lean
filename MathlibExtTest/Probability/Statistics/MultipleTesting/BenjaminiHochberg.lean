/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.BenjaminiHochberg

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- At `q = 0.1` the BH thresholds are `q k / 3 = 1/30, 1/15, 1/10`; two p-values are below
`1/15` but only two (not three) are below `1/10`, so the step-up index is `2`. -/
theorem bhIndex_p3 : bhIndex (1 / 10) p3 = 2 := by
  have h2 : numBelow p3 (1 / 10 * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ 1 / 10 * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h3 : numBelow p3 (1 / 10 * ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ 1 / 10 * ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have hge : 2 ≤ bhIndex (1 / 10) p3 := le_bhIndex (by norm_num) (by rw [h2])
  have hne : bhIndex (1 / 10) p3 ≠ 3 := by
    intro h
    have := bhIndex_le_numBelow (1 / 10) p3
    rw [h, h3] at this
    omega
  have hle := bhIndex_le (1 / 10) p3
  omega

/-- BH at `q = 0.1` rejects the two smallest p-values. -/
example : bhRejections (1 / 10) p3 = {0, 1} := by
  rw [bhRejections, bhIndex_p3]
  ext i
  fin_cases i <;> norm_num [p3]

example : (bhRejections (1 / 10) p3).card = 2 := by
  rw [card_bhRejections (by norm_num), bhIndex_p3]

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity: one uniform p-value with a true null satisfies every hypothesis of the BH
theorem, which then bounds the FDR by `q`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (bhRejections q fun _ : Fin 1 => ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ q * (Finset.univ : Finset (Fin 1)).card / 1 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ : Fin 1 => id) (fun _ => measurable_id)
    (iIndepFun.of_subsingleton) Finset.univ (fun _ _ => HasLaw.id) q hq₀ hq₁

/-- A fair coin on `Bool`: the law of a discrete p-value taking the values `1 / 2` and `1`. -/
noncomputable def coin : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac true + (2 : ENNReal)⁻¹ • Measure.dirac false

/-- The fair coin is a probability measure. -/
instance : IsProbabilityMeasure coin :=
  ⟨by simp [coin, ENNReal.inv_two_add_inv_two]⟩

/-- The discrete p-value `1 / 2` (heads) or `1` (tails); it is not uniform. -/
noncomputable def coinP (b : Bool) : ℝ := if b then 1 / 2 else 1

/-- The coin p-value is valid: `P(coinP ≤ t)` is `0` for `t < 1 / 2`, `1 / 2` for
`1 / 2 ≤ t < 1`, and `1` at `t = 1`. -/
theorem isValidPValue_coinP : IsValidPValue coin coinP := by
  intro t ⟨ht₀, ht₁⟩
  rcases eq_or_lt_of_le ht₁ with rfl | hlt
  · simpa using prob_le_one
  · by_cases hhalf : 1 / 2 ≤ t
    · have hset : {b | coinP b ≤ t} = {true} := by
        ext b; cases b <;> simp [coinP] <;> linarith
      rw [hset]
      calc coin {true} = 2⁻¹ := by simp [coin]
        _ = ENNReal.ofReal (1 / 2) := by
          rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]; simp
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hhalf
    · replace hhalf := not_le.mp hhalf
      have hset : {b | coinP b ≤ t} = ∅ := by
        ext b; cases b <;> simp [coinP] <;> linarith
      simp [hset]

/-- Non-vacuity of the super-uniform BH theorem with a genuinely discrete (non-uniform) true-null
p-value: the FDR is still at most `q`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ b, falseDiscoveryProportion Finset.univ (bhRejections q fun _ : Fin 1 => coinP b) ∂coin ≤
      q * (Finset.univ : Finset (Fin 1)).card / 1 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue
    coin (fun _ : Fin 1 => coinP) (fun _ => measurable_from_top)
    (iIndepFun.of_subsingleton) Finset.univ (fun _ _ => isValidPValue_coinP) q hq₀ hq₁

/-- `H_3 = 1 + 1/2 + 1/3 = 11/6`, the harmonic factor in the BY level for `m = 3`. -/
example : (harmonic 3 : ℝ) = 11 / 6 := by
  norm_num [harmonic, Finset.sum_range_succ]

example : (1 : ℝ) ≤ harmonic 2 := one_le_harmonic (by norm_num)

/-- Non-vacuity of the Benjamini–Yekutieli theorem under perfect dependence: both p-values are the
same uniform random variable, so they are as far from independent as possible, and no independence
hypothesis is supplied. BH at level `q / H_2` still has FDR at most `q * 2 / 2`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (bhRejections (q / harmonic 2) fun _ : Fin 2 => ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ q * 2 / 2 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ : Fin 2 => id) (fun _ => measurable_id)
    Finset.univ (fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id) q hq₀ hq₁

/-! ### PRDS -/

/-- Boundary: with `m = 0` the PRDS theorem applies (PRDS on `∅` is automatic) and bounds the FDR
by `q * 0 / 0 = 0`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (p : Fin 0 → Bool → ℝ) :
    ∫ b, falseDiscoveryProportion ∅ (bhRejections q fun i => p i b) ∂coin ≤ 0 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn coin p
    (fun _ => measurable_from_top) ∅ (isPRDSOn_empty coin p) (by simp) q hq₀ hq₁

/-- Two independent fair coins, as the product measure on `Fin 2 → Bool`. -/
noncomputable def coin2 : Measure (Fin 2 → Bool) := Measure.pi fun _ => coin

/-- The product of two fair coins is a probability measure. -/
instance : IsProbabilityMeasure coin2 := by
  unfold coin2
  infer_instance

/-- The coordinate p-values of `coin2` are measurable. -/
theorem measurable_coin2 (j : Fin 2) : Measurable fun ω : Fin 2 → Bool => coinP (ω j) :=
  (show Measurable coinP from measurable_from_top).comp (measurable_pi_apply j)

/-- The two coordinates of `coin2` are independent. -/
theorem iIndepFun_coin2 : iIndepFun (fun (j : Fin 2) (ω : Fin 2 → Bool) => coinP (ω j)) coin2 :=
  iIndepFun_pi (X := fun _ => coinP) fun _ => measurable_from_top.aemeasurable

/-- Each coordinate p-value of `coin2` is valid: its law is the fair coin. -/
theorem isValidPValue_coin2 (j : Fin 2) : IsValidPValue coin2 fun ω => coinP (ω j) := by
  intro t ht
  calc coin2 {ω | coinP (ω j) ≤ t} = (coin2.map (Function.eval j)) {b | coinP b ≤ t} := by
        rw [Measure.map_apply (measurable_pi_apply j) (MeasurableSet.of_discrete)]; rfl
    _ = coin {b | coinP b ≤ t} := by
        have huniv : coin {false, true} = 1 := by
          rw [show ({false, true} : Set Bool) = Set.univ by ext b; cases b <;> simp]
          exact measure_univ
        simp [coin2, Measure.pi_map_eval, huniv]
    _ ≤ ENNReal.ofReal t := isValidPValue_coinP t ht

/-- Independent discrete p-values are PRDS on every `H0`, so the PRDS theorem gives FDR at most
`q * 2 / 2` for two independent coin p-values that are both true nulls. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (bhRejections q fun j : Fin 2 => coinP (ω j))
      ∂coin2 ≤ q * 2 / 2 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn coin2
    (fun j ω => coinP (ω j)) measurable_coin2 Finset.univ
    (isPRDSOn_of_iIndepFun coin2 _ measurable_coin2 iIndepFun_coin2 _)
    (fun j _ => isValidPValue_coin2 j) q hq₀ hq₁

/-- Perfect positive dependence is PRDS: two identical uniform p-values `p 0 = p 1 = U` are a
nondecreasing function of either coordinate. -/
theorem isPRDSOn_comonotone :
    IsPRDSOn (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ : Fin 2 => id) Finset.univ :=
  isPRDSOn_of_monotone_comp _ _ (fun _ => measurable_id) _ fun _ _ =>
    ⟨fun x _ => x, fun _ _ h _ => h, fun _ => rfl⟩

/-- Under perfect positive dependence the PRDS theorem runs BH at the full level `q` (compare the
Benjamini–Yekutieli fixture above, which needs the smaller level `q / H_2`). -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (bhRejections q fun _ : Fin 2 => ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ q * 2 / 2 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ : Fin 2 => id) (fun _ => measurable_id)
    Finset.univ isPRDSOn_comonotone (fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id)
    q hq₀ hq₁

/-- Antithetic coin p-values: `p 0 = coinP b` and `p 1 = coinP (!b)`; exactly one is `1 / 2`. -/
noncomputable def antiP : Fin 2 → Bool → ℝ := ![coinP, fun b => coinP (!b)]

/-- The flipped coin p-value is valid. -/
theorem isValidPValue_coinP_not : IsValidPValue coin fun b => coinP (!b) := by
  intro t ⟨ht₀, ht₁⟩
  rcases eq_or_lt_of_le ht₁ with rfl | hlt
  · simpa using prob_le_one
  · by_cases hhalf : 1 / 2 ≤ t
    · have hset : {b | coinP (!b) ≤ t} = {false} := by
        ext b; cases b <;> simp [coinP] <;> linarith
      rw [hset]
      calc coin {false} = 2⁻¹ := by simp [coin]
        _ = ENNReal.ofReal (1 / 2) := by
          rw [one_div, ENNReal.ofReal_inv_of_pos two_pos]; simp
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hhalf
    · replace hhalf := not_le.mp hhalf
      have hset : {b | coinP (!b) ≤ t} = ∅ := by
        ext b; cases b <;> simp [coinP] <;> linarith
      simp [hset]

/-- The antithetic pair is **not** PRDS on `{0, 1}`: for the increasing set `D = {x | 1 ≤ x 1}`,
`P(D | p 0 ≤ 1/2) = 1` but `P(D | p 0 ≤ 1) = 1/2`, so the conditional tail decreases, contradicting
`IsPRDSOn.measure_inter_mul_le`. -/
theorem not_isPRDSOn_antiP : ¬ IsPRDSOn coin antiP Finset.univ := by
  intro h
  have hD : MeasurableSet {x : Fin 2 → ℝ | 1 ≤ x 1} :=
    measurableSet_le measurable_const (measurable_pi_apply 1)
  have hup : IsUpperSet {x : Fin 2 → ℝ | 1 ≤ x 1} := fun x y hxy hx => hx.trans (hxy 1)
  have key := h.measure_inter_mul_le (fun _ => measurable_from_top) (Finset.mem_univ 0) hD hup
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have h1 : {b | (fun j => antiP j b) ∈ {x : Fin 2 → ℝ | 1 ≤ x 1}} ∩
      {b | antiP 0 b ≤ 1 / 2} = {true} := by
    ext b; cases b <;> norm_num [antiP, coinP]
  have h2 : {b | antiP 0 b ≤ 1} = Set.univ := by
    ext b; cases b <;> norm_num [antiP, coinP]
  have h3 : {b | (fun j => antiP j b) ∈ {x : Fin 2 → ℝ | 1 ≤ x 1}} ∩
      {b | antiP 0 b ≤ 1} = {true} := by
    ext b; cases b <;> norm_num [antiP, coinP]
  have h4 : {b | antiP 0 b ≤ 1 / 2} = {true} := by
    ext b; cases b <;> norm_num [antiP, coinP]
  rw [h1, h3, h2, h4] at key
  have c1 : coin {true} = 2⁻¹ := by simp [coin]
  rw [c1, measure_univ, mul_one] at key
  have h12 : (1 : ENNReal) ≤ 2⁻¹ := by
    calc (1 : ENNReal) = 2 * 2⁻¹ := (ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
      _ ≤ 2 * (2⁻¹ * 2⁻¹) := by gcongr
      _ = 2⁻¹ := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [ENNReal.one_le_inv] at h12
  norm_num at h12

/-- The Benjamini–Yekutieli arbitrary-dependence theorem does apply to the antithetic pair,
which is not PRDS (`not_isPRDSOn_antiP`). -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ b, falseDiscoveryProportion Finset.univ (bhRejections (q / harmonic 2) fun j => antiP j b)
      ∂coin ≤ q * 2 / 2 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence coin
    antiP (fun _ => measurable_from_top) Finset.univ
    (fun j _ => by
      fin_cases j
      · exact isValidPValue_coinP
      · exact isValidPValue_coinP_not) q hq₀ hq₁

end MathlibExtTest.Probability.Statistics.MultipleTesting.BenjaminiHochberg
