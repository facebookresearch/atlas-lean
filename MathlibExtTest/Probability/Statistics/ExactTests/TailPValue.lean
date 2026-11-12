/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import MathlibExt.Probability.Statistics.ExactTests.ClopperPearson
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

end MathlibExtTest.Probability.Statistics.ExactTests.TailPValue
