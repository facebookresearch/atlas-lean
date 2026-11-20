/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import MathlibExt.Probability.Statistics.ExactTests.BinomialTest
public import MathlibExt.Probability.Distributions.Hypergeometric
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Topology.UnitInterval
public import MathlibExt.Probability.Distributions.Multinomial

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.ExactTests
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.ExactTests.TailPValue

/-- Non-vacuity: the identity on `ℕ` under the hypergeometric law `H(5, 2, 2)` has that law, so
its upper-tail p-value is valid. -/
example : IsValidPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure
    (upperTailPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure id) :=
  isValidPValue_upperTailPValue HasLaw.id

/-- Non-vacuity: the identity under the hypergeometric law `H(5, 2, 2)` has that law, so its
lower-tail p-value is valid. -/
example : IsValidPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure
    (lowerTailPValue (hypergeometric 5 2 2 (by norm_num) (by norm_num)).toMeasure id) :=
  isValidPValue_lowerTailPValue HasLaw.id

/-- Boundary: the upper tail at cutoff `0` is the total mass `1`. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] : upperTail ν 0 = 1 := by
  simp [upperTail]

/-- Boundary: under a point mass at `3` the upper tail is `1` up to the atom and `0` above it,
so the p-value takes only the values `0` and `1`, for every count `X` and outcome `ω`. -/
example {Ω : Type*} (X : Ω → ℕ) (ω : Ω) :
    upperTailPValue (Measure.dirac 3) X ω = if X ω ≤ 3 then 1 else 0 := by
  simp only [upperTailPValue, upperTail, measureReal_def]
  split_ifs with h <;> simp [Set.indicator, h]

/-- The general theorem applies to any law on `ℕ`, e.g. a binomial count. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℕ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X Bin(n, p) μ) :
    IsValidPValue μ (upperTailPValue Bin(n, p) X) :=
  isValidPValue_upperTailPValue hX

/-- The conditional test for two Poisson rates: for independent `X ~ Po(a)`, `Y ~ Po(b)`, the
upper-tail p-value of `X` under `Bin(N, a / (a + b))` is valid given the total `X + Y = N`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℕ} {a b : NNReal}
    (hab : 0 < a + b) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X (poissonMeasure a) μ) (hY : HasLaw Y (poissonMeasure b) μ)
    (hXY : IndepFun X Y μ) (N : ℕ) :
    IsValidPValue (μ[|{ω | X ω + Y ω = N}])
      (upperTailPValue (binomial N ⟨(a : ℝ) / (a + b), by positivity,
        div_le_one_of_le₀ (le_add_of_nonneg_right b.2) (by positivity)⟩) X) :=
  isValidPValue_upperTailPValue (hasLaw_cond_binomial hab hXm hYm hX hY hXY N)

/-- Non-vacuity of `measure_upperTailPValue_le_upperTail`: the identity on `ℕ` under any
probability measure `ν` is exactly calibrated at every attainable level. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] (k : ℕ) :
    ν {j | upperTailPValue ν id j ≤ upperTail ν k} = ENNReal.ofReal (upperTail ν k) :=
  measure_upperTailPValue_le_upperTail HasLaw.id k

/-- Use: with `X = 0`, the p-value is `(1 - p) ^ n`. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {p : unitInterval} {X : Ω → ℕ}
    (_hX : HasLaw X (binomial n p) μ) (ω : Ω) (hX0 : X ω = 0) :
    lowerTailPValue (binomial n p) X ω = (1 - (p : ℝ)) ^ n := by
  unfold lowerTailPValue lowerTail
  rw [hX0]
  have hset : {j : ℕ | j ≤ 0} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    omega
  rw [hset, binomial_real_singleton]
  simp [Nat.choose_zero_right]

/-- Boundary: with `n = 0` the p-value is `1`. -/
example {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : unitInterval} {X : Ω → ℕ}
    (_hX : HasLaw X (binomial 0 p) μ) (ω : Ω) :
    lowerTailPValue (binomial 0 p) X ω = 1 := by
  unfold lowerTailPValue lowerTail
  have hI : {j : ℕ | j ≤ X ω} = Set.Iic (X ω) := rfl
  rw [hI, binomial_real_Iic]
  have hempty : Finset.Icc (X ω + 1) 0 = ∅ :=
    Finset.Icc_eq_empty_of_lt (by omega)
  unfold binomTail
  rw [hempty, Finset.sum_empty, sub_zero]

/-- Negative: the strict lower tail `{j | j < X ω}` is not valid in general. -/
example (p : unitInterval) (hp : (p : ℝ) = 1 / 2) :
    ¬ IsValidPValue (binomial 1 p)
      (fun ω : ℕ => (binomial 1 p).real {j | j < ω}) := by
  intro hvalid
  have ht : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hle := hvalid (1 / 4) ht
  have hmem : (0 : ℕ) ∈ {ω : ℕ | (binomial 1 p).real {j | j < ω} ≤ 1 / 4} := by
    show (binomial 1 p).real {j : ℕ | j < 0} ≤ 1 / 4
    have hempty : {j : ℕ | j < 0} = ∅ := by
      ext j
      simp
    rw [hempty, measureReal_empty]
    norm_num
  have hsub : ({0} : Set ℕ) ⊆ {ω : ℕ | (binomial 1 p).real {j | j < ω} ≤ 1 / 4} :=
    Set.singleton_subset_iff.mpr hmem
  have hmono : (binomial 1 p) {0} ≤ (binomial 1 p) {ω | (binomial 1 p).real {j | j < ω} ≤ 1 / 4} :=
    measure_mono hsub
  have hreal : (binomial 1 p).real {0} = 1 / 2 := by
    rw [binomial_real_singleton, hp]
    norm_num [Nat.choose_zero_right]
  have hmeas : (binomial 1 p) {0} = ENNReal.ofReal (1 / 2 : ℝ) := by
    have h := ofReal_measureReal (μ := binomial 1 p) (s := ({0} : Set ℕ))
    rw [hreal] at h
    exact h.symm
  have hle2 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [← hmeas]
    exact le_trans hmono hle
  have hlt : ENNReal.ofReal (1 / 4 : ℝ) < ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  exact absurd hle2 (not_le_of_gt hlt)

/-! ### Survival-function p-values at an atom -/

/-- At the atom of a point mass the closed tail `Set.Ici` gives p-value `1`. -/
example : (Measure.dirac (0 : ℝ)).real (Set.Ici 0) = 1 := by
  rw [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_Ici.mpr le_rfl), ENNReal.toReal_one]

/-- `isValidPValue_survival` applies to a law with an atom: the point mass at `0`. -/
example : IsValidPValue (Measure.dirac (0 : ℝ))
    (fun y : ℝ => (Measure.dirac (0 : ℝ)).real (Set.Ici y)) :=
  isValidPValue_survival HasLaw.id

/-- The strict tail `Set.Ioi` would give p-value `0` at the atom, which occurs with probability
`1`, so that p-value is not valid: the closed tail in `isValidPValue_survival` is necessary. -/
example : ¬ IsValidPValue (Measure.dirac (0 : ℝ))
    (fun y : ℝ => (Measure.dirac (0 : ℝ)).real (Set.Ioi y)) := by
  intro h
  have h0 := h 0 ⟨le_rfl, zero_le_one⟩
  have hmem : (0 : ℝ) ∈ {y : ℝ | (Measure.dirac (0 : ℝ)).real (Set.Ioi y) ≤ 0} := by
    show (Measure.dirac (0 : ℝ)).real (Set.Ioi 0) ≤ 0
    rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi]
    simp
  rw [Measure.dirac_apply_of_mem hmem, ENNReal.ofReal_zero] at h0
  exact one_ne_zero (le_zero_iff.mp h0)

/-- Use: the theorem applied to a binomial count gives a concrete level bound. -/
example {n : ℕ} {p : unitInterval} :
    (binomial n p) {ω | min 1 (2 * min (upperTailPValue (binomial n p) id ω)
      (lowerTailPValue (binomial n p) id ω)) ≤ 1 / 2} ≤ ENNReal.ofReal (1 / 2) :=
  (isValidPValue_twoSided HasLaw.id) (1 / 2) ⟨by norm_num, by norm_num⟩

/-- Boundary: under a symmetric binomial law the central observation attains p-value `1`. -/
example (m : ℕ) (p : unitInterval) (hp : (p : ℝ) = 1 / 2) :
    (fun ω : ℕ => min 1 (2 * min (upperTailPValue (binomial (m + m) p) id ω)
      (lowerTailPValue (binomial (m + m) p) id ω))) m = 1 := by
  have hae : ∀ᵐ j ∂(binomial (m + m) p), j ≤ m + m :=
    ae_le_of_hasLaw_binomial HasLaw.id
  have hA : {j : ℕ | m ≤ j} =ᵐ[binomial (m + m) p] ↑(Finset.Icc m (m + m)) := by
    filter_upwards [hae] with j hj
    simp [hj]
  have hB : {j : ℕ | j ≤ m} = ↑(Finset.Icc 0 m) := by
    ext j
    simp only [Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc]
    omega
  have hsym : upperTail (binomial (m + m) p) m = lowerTail (binomial (m + m) p) m := by
    rw [upperTail, lowerTail, measureReal_congr hA, hB, ← sum_measureReal_singleton,
      ← sum_measureReal_singleton]
    simp only [binomial_real_singleton]
    rw [hp, show ((1 : ℝ) - 1 / 2) = 1 / 2 by norm_num]
    refine Finset.sum_bij (fun b _ => (m + m) - b) ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro b₁ hb₁ b₂ hb₂ h
      simp only [Finset.mem_Icc] at hb₁ hb₂ h
      omega
    · intro y hy
      simp only [Finset.mem_Icc] at hy
      refine ⟨(m + m) - y, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · show (m + m) - ((m + m) - y) = y
        omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      have e1 : (m + m) - ((m + m) - b) = b := by omega
      have hC : (m + m).choose ((m + m) - b) = (m + m).choose b :=
        Nat.choose_symm hb.2
      rw [e1, hC]
      ring
  have hunion : ({j : ℕ | m ≤ j} ∪ {j : ℕ | j ≤ m}) = Set.univ := by
    ext j
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  have hsum : (1 : ℝ) ≤ upperTail (binomial (m + m) p) m +
      lowerTail (binomial (m + m) p) m := by
    rw [upperTail, lowerTail]
    have hle : (1 : ENNReal) ≤ (binomial (m + m) p) {j | m ≤ j} +
        (binomial (m + m) p) {j | j ≤ m} := by
      calc (1 : ENNReal) = (binomial (m + m) p) Set.univ := measure_univ.symm
        _ = (binomial (m + m) p) ({j | m ≤ j} ∪ {j | j ≤ m}) := by rw [hunion]
        _ ≤ (binomial (m + m) p) {j | m ≤ j} + (binomial (m + m) p) {j | j ≤ m} :=
            measure_union_le _ _
    rw [← ofReal_measureReal, ← ofReal_measureReal,
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ← ENNReal.ofReal_one] at hle
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg measureReal_nonneg measureReal_nonneg)).mp hle
  show min 1 (2 * min (upperTail (binomial (m + m) p) m)
    (lowerTail (binomial (m + m) p) m)) = 1
  have hmin : min (upperTail (binomial (m + m) p) m)
      (lowerTail (binomial (m + m) p) m) = upperTail (binomial (m + m) p) m := by
    rw [hsym]
    exact min_self _
  have h2 : (1 : ℝ) ≤ 2 * min (upperTail (binomial (m + m) p) m)
      (lowerTail (binomial (m + m) p) m) := by
    rw [hmin]
    linarith [hsum, hsym]
  exact min_eq_left h2

/-- Counterexample: without the factor `2`, `min(U, L)` is not valid. Under `Bernoulli(1 / 2)`
the minimum is `1 / 2` almost surely (on the support `{0, 1}`; off-support, at counts `≥ 2`,
the upper tail is `0`), so the level-`1 / 2` rejection event has mass `1`. -/
example (p : unitInterval) (hp : (p : ℝ) = 1 / 2) :
    ¬ IsValidPValue (binomial 1 p)
      (fun ω : ℕ => min (upperTailPValue (binomial 1 p) id ω)
        (lowerTailPValue (binomial 1 p) id ω)) := by
  intro h
  have h12 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  have hae : ∀ᵐ j ∂(binomial 1 p), j ≤ 1 := ae_le_of_hasLaw_binomial HasLaw.id
  have hsing0 : (binomial 1 p).real {0} = 1 / 2 := by
    rw [binomial_real_zero, hp]
    norm_num
  have hsing1 : (binomial 1 p).real {1} = 1 / 2 := by
    rw [binomial_real_self, hp]
    norm_num
  have hset0 : {j : ℕ | j ≤ 0} = {0} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    omega
  have hU0 : upperTailPValue (binomial 1 p) id 0 = 1 := by
    show upperTail (binomial 1 p) 0 = 1
    have huniv0 : {j : ℕ | 0 ≤ j} = Set.univ := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Nat.zero_le j
    rw [upperTail, huniv0, probReal_univ]
  have hL0 : lowerTailPValue (binomial 1 p) id 0 = 1 / 2 := by
    show lowerTail (binomial 1 p) 0 = 1 / 2
    rw [lowerTail, hset0]
    exact hsing0
  have hU1 : upperTailPValue (binomial 1 p) id 1 = 1 / 2 := by
    show upperTail (binomial 1 p) 1 = 1 / 2
    have hcompl : {j : ℕ | 1 ≤ j} = {j : ℕ | j ≤ 0}ᶜ := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      omega
    rw [upperTail, hcompl, probReal_compl_eq_one_sub MeasurableSet.of_discrete, hset0,
      hsing0]
    norm_num
  have hL1 : lowerTailPValue (binomial 1 p) id 1 = 1 := by
    show lowerTail (binomial 1 p) 1 = 1
    have hB1 : {j : ℕ | j ≤ 1} =ᵐ[binomial 1 p] Set.univ := by
      filter_upwards [hae] with j hj
      simp [hj]
    rw [lowerTail, measureReal_congr hB1, probReal_univ]
  have hUge : ∀ k : ℕ, upperTailPValue (binomial 1 p) id (k + 2) = 0 := by
    intro k
    show upperTail (binomial 1 p) (k + 2) = 0
    have hE : {j : ℕ | k + 2 ≤ j} =ᵐ[binomial 1 p] ∅ := by
      filter_upwards [hae] with j hj
      have hcon : ¬ (k + 2 ≤ j) := by omega
      simp [hcon]
    rw [upperTail, measureReal_congr hE, measureReal_empty]
  have h12' : (binomial 1 p) {ω : ℕ |
      min (upperTailPValue (binomial 1 p) id ω)
        (lowerTailPValue (binomial 1 p) id ω) ≤ 1 / 2} ≤ ENNReal.ofReal (1 / 2) := h12
  have hset : {ω : ℕ | min (upperTailPValue (binomial 1 p) id ω)
      (lowerTailPValue (binomial 1 p) id ω) ≤ 1 / 2} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_cases h0 : ω = 0
    · subst h0
      rw [hU0, hL0]
      exact min_le_right _ _
    · by_cases h1 : ω = 1
      · subst h1
        rw [hU1, hL1]
        exact min_le_left _ _
      · obtain ⟨k, hk⟩ : ∃ k, ω = k + 2 := ⟨ω - 2, by omega⟩
        subst hk
        calc min (upperTailPValue (binomial 1 p) id (k + 2)) _
                ≤ upperTailPValue (binomial 1 p) id (k + 2) := min_le_left _ _
          _ = 0 := hUge k
          _ ≤ 1 / 2 := by norm_num
  rw [hset, measure_univ] at h12'
  have hlt : ENNReal.ofReal (1 / 2 : ℝ) < 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    norm_num
  exact absurd h12' (not_le_of_gt hlt)

end MathlibExtTest.Probability.Statistics.ExactTests.TailPValue
