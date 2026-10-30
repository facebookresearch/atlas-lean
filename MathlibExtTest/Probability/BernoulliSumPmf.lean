/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BernoulliSumPmf
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Tests for the pmf of a sum of independent Bernoulli variables

Generic restatements of the public signatures in
`MathlibExt.Probability.BernoulliSumPmf`, the constant-variable
Bernoulli instances under a Dirac measure, the one-coin and two-coin
fair-coin instances, the vanishing of the pmf above the number of
summands, and the fact that the pmf sums to `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace MathlibExtTest.Probability.BernoulliSumPmf

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The general pmf formula restates with the exact public signature. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : Fin m → ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (p i))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      ∑ A ∈ Finset.univ.powersetCard j,
        (∏ i ∈ A, p i) * (∏ i ∈ Finset.univ \ A, (1 - p i)) :=
  bernoulli_sum_pmf hBernoulli hIndep hMeas j

/-- The i.i.d. binomial pmf restates with the exact public signature. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i))
    (j : ℕ) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal =
      (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) :=
  bernoulli_sum_pmf_iid hBernoulli hIndep hMeas j

/-- The constant `1` variable is Bernoulli with parameter `1` under any Dirac measure. -/
example {α : Type*} [MeasurableSpace α] (a : α) :
    IsBernoulliRV (fun _ : α => 1) (Measure.dirac a) 1 := by
  refine ⟨by norm_num, ?_⟩
  simpa using (hasLaw_dirac_of_ae_eq (P := Measure.dirac a)
    (X := fun _ : α => 1) (x := 1) (by simp))

/-- The constant `0` variable is Bernoulli with parameter `0` under any Dirac measure. -/
example {α : Type*} [MeasurableSpace α] (a : α) :
    IsBernoulliRV (fun _ : α => 0) (Measure.dirac a) 0 := by
  refine ⟨by norm_num, ?_⟩
  simpa using (hasLaw_dirac_of_ae_eq (P := Measure.dirac a)
    (X := fun _ : α => 0) (x := 0) (by simp))

/-- One fair coin: `P(S = 0) = 1 / 2`. -/
example {X : Fin 1 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 1, X i ω) ⁻¹' {↑0})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 0]
  norm_num

/-- One fair coin: `P(S = 1) = 1 / 2`. -/
example {X : Fin 1 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 1, X i ω) ⁻¹' {↑1})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 1]
  norm_num

/-- Two fair coins: `P(S = 1) = 1 / 2`. -/
example {X : Fin 2 → Ω → ℕ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (1 / 2))
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin 2, X i ω) ⁻¹' {↑1})).toReal = 1 / 2 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas 1]
  norm_num

/-- The pmf vanishes above the number of summands: `P(S = m + 1) = 0`. -/
example {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑(m + 1)})).toReal = 0 := by
  rw [bernoulli_sum_pmf_iid hBernoulli hIndep hMeas (m + 1)]
  simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), Nat.cast_zero, zero_mul]

/-- The pmf sums to `1`: `∑_{j=0}^{m} P(S = j) = 1`. -/
theorem bernoulli_sum_pmf_sum_eq_one {m : ℕ} {X : Fin m → Ω → ℕ} {p : ℝ}
    (hBernoulli : ∀ i, IsBernoulliRV (X i) μ p)
    (hIndep : iIndepFun X μ)
    (hMeas : ∀ i, Measurable (X i)) :
    ∑ j ∈ Finset.range (m + 1),
      (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal = 1 := by
  calc ∑ j ∈ Finset.range (m + 1),
        (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal
      = ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j) :=
        Finset.sum_congr rfl (fun j _ => bernoulli_sum_pmf_iid hBernoulli hIndep hMeas j)
    _ = (p + (1 - p)) ^ m := by
        rw [add_pow]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = 1 := by rw [show p + (1 - p) = 1 from by ring, one_pow]

private noncomputable def threePointMeasure : Measure ℕ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 +
    (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + Measure.dirac 2

/-- The old two-mass conditions admit this measure, despite its extra mass at `2`. -/
example :
    0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 ∧
      threePointMeasure (id ⁻¹' {0}) = ENNReal.ofReal (1 - (1 / 2 : ℝ)) ∧
      threePointMeasure (id ⁻¹' {1}) = ENNReal.ofReal (1 / 2 : ℝ) := by
  norm_num [threePointMeasure, ENNReal.ofReal_div_of_pos]

/-- The counterexample puts positive mass outside the Bernoulli support. -/
example : threePointMeasure (id ⁻¹' {2}) = 1 := by
  norm_num [threePointMeasure]

/-- A genuine Bernoulli law excludes the concrete three-point counterexample. -/
example : ¬ IsBernoulliRV (id : ℕ → ℕ) threePointMeasure (1 / 2) := by
  rintro ⟨hp, hLaw⟩
  have h := hLaw.measure_eq (p := fun n : ℕ => n = 2) (measurableSet_singleton 2)
  norm_num [threePointMeasure, bernoulliMeasure_apply] at h

/-- A nonconstant Bernoulli variable with parameter `1 / 3`. -/
example : IsBernoulliRV (id : ℕ → ℕ)
    (bernoulliMeasure 1 0 ⟨1 / 3, by norm_num⟩) (1 / 3) :=
  ⟨by norm_num, HasLaw.id⟩

/-- Its two positive masses and zero mass at `2` fix the actual Nat representation. -/
example :
    bernoulliMeasure (1 : ℕ) 0 ⟨1 / 3, by norm_num⟩ {0} = ENNReal.ofReal (2 / 3) ∧
    bernoulliMeasure (1 : ℕ) 0 ⟨1 / 3, by norm_num⟩ {1} = ENNReal.ofReal (1 / 3) ∧
    bernoulliMeasure (1 : ℕ) 0 ⟨1 / 3, by norm_num⟩ {2} = 0 := by
  norm_num [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq]

private noncomputable def coinParameter (i : Fin 2) : unitInterval :=
  if i = 0 then ⟨1 / 3, by norm_num⟩ else ⟨1 / 4, by norm_num⟩

private noncomputable def independentCoins : Measure (Fin 2 → ℕ) :=
  Measure.pi (fun i => bernoulliMeasure 1 0 (coinParameter i))

private instance : IsProbabilityMeasure independentCoins := by
  unfold independentCoins
  infer_instance

private theorem independentCoins_isBernoulli (i : Fin 2) :
    IsBernoulliRV (fun ω : Fin 2 → ℕ => ω i) independentCoins (coinParameter i : ℝ) := by
  refine ⟨(coinParameter i).property, ?_⟩
  exact (measurePreserving_eval
    (fun i : Fin 2 => bernoulliMeasure (1 : ℕ) 0 (coinParameter i)) i).hasLaw

private theorem independentCoins_indep :
    iIndepFun (fun i : Fin 2 => fun ω : Fin 2 → ℕ => ω i) independentCoins :=
  iIndepFun_pi (μ := fun i : Fin 2 => bernoulliMeasure (1 : ℕ) 0 (coinParameter i))
    (X := fun _ => (id : ℕ → ℕ)) (fun _ => aemeasurable_id)

private theorem independentCoins_pmf (j : ℕ) :
    (independentCoins ((fun ω => ∑ i : Fin 2, ω i) ⁻¹' {j})).toReal =
      ∑ A ∈ (Finset.univ : Finset (Fin 2)).powersetCard j,
        (∏ i ∈ A, (coinParameter i : ℝ)) *
          (∏ i ∈ Finset.univ \ A, (1 - (coinParameter i : ℝ))) :=
  bernoulli_sum_pmf independentCoins_isBernoulli independentCoins_indep
    (fun i => measurable_pi_apply i) j

/-- Distinct interior parameters `1 / 3` and `1 / 4`: `P(S = 0) = 1 / 2`. -/
example :
    (independentCoins ((fun ω => ∑ i : Fin 2, ω i) ⁻¹' {0})).toReal = 1 / 2 := by
  rw [independentCoins_pmf]
  have h : (Finset.univ : Finset (Fin 2)).powersetCard 0 = {∅} := by decide
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [h, hu]
  norm_num [coinParameter]

/-- The same heterogeneous sum has `P(S = 1) = 5 / 12`. -/
example :
    (independentCoins ((fun ω => ∑ i : Fin 2, ω i) ⁻¹' {1})).toReal = 5 / 12 := by
  rw [independentCoins_pmf]
  have h : (Finset.univ : Finset (Fin 2)).powersetCard 1 = {{0}, {1}} := by decide
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [h, hu]
  have h0 : ({0, 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  have h1 : ({0, 1} : Finset (Fin 2)) \ {1} = {0} := by decide
  norm_num [coinParameter, h0, h1]

/-- The same heterogeneous sum has `P(S = 2) = 1 / 12`. -/
example :
    (independentCoins ((fun ω => ∑ i : Fin 2, ω i) ⁻¹' {2})).toReal = 1 / 12 := by
  rw [independentCoins_pmf]
  have h : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {{0, 1}} := by decide
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [h, hu]
  norm_num [coinParameter]

/-- No mass lies above the two summands. -/
example :
    (independentCoins ((fun ω => ∑ i : Fin 2, ω i) ⁻¹' {3})).toReal = 0 := by
  rw [independentCoins_pmf]
  have h : (Finset.univ : Finset (Fin 2)).powersetCard 3 = ∅ := by decide
  simp [h]

end MathlibExtTest.Probability.BernoulliSumPmf
