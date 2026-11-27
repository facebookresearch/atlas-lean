/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Moments.Variance

/-!
# The Morris approximate counter

One fresh Bernoulli draw per token either increments the register or leaves it alone.
The parameter of that draw depends on the current register. After `n` tokens the register
belongs to `Fin (n + 1)` because it has taken at most `n` unit steps, not because the
algorithm has imposed a cutoff. The observable `2 ^ x` doubles on an increment.

Source: A. Chakrabarti, *Data Stream Algorithms*, Dartmouth College, July 1, 2025,
Unit 4, Algorithms 5–6 and Lemma 4.3.1, pp. 21–22.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Cslib.Algorithms.Lean.MorrisCounter

/-- Probability that the register `x` advances on the next token. -/
noncomputable def incrementProb (x : ℕ) : unitInterval :=
  ⟨((2 : ℝ) ^ x)⁻¹, by
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩

/-- The Markov transition of one uncapped counter. The two embeddings retain the old
value or increase it by one in the next (larger) finite state space. -/
noncomputable def step (n : ℕ) : Kernel (Fin (n + 1)) (Fin (n + 2)) :=
  Kernel.ofFunOfCountable fun x => bernoulliMeasure x.succ x.castSucc (incrementProb x)

instance (n : ℕ) : IsMarkovKernel (step n) :=
  ⟨fun x => inferInstanceAs
    (IsProbabilityMeasure (bernoulliMeasure x.succ x.castSucc (incrementProb x)))⟩

/-- The increment branch of the transition has mass exactly `1 / 2 ^ x`. -/
theorem step_increment {n : ℕ} (x : Fin (n + 1)) :
    (step n x).real {x.succ} = ((2 : ℝ) ^ x.val)⁻¹ := by
  apply bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp)
  simp [Fin.ext_iff]

/-- Law of the register after `n` tokens, starting from zero and drawing from the transition
kernel afresh at every step. -/
noncomputable def law : (n : ℕ) → Measure (Fin (n + 1))
  | 0 => Measure.dirac 0
  | n + 1 => step n ∘ₘ law n

instance law_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ n ih => exact inferInstanceAs (IsProbabilityMeasure (step n ∘ₘ law n))

/-- The doubling observable `C = 2 ^ x`; the reported count is `C - 1`. -/
noncomputable def value {k : ℕ} (x : Fin k) : ℝ := 2 ^ x.val

/-- Given a register value, the conditional mean of the next doubling observable is `C + 1`. -/
theorem integral_value_step {n : ℕ} (x : Fin (n + 1)) :
    ∫ y, value y ∂(step n x) = value x + 1 := by
  change (∫ y, value y ∂(bernoulliMeasure _ _ _)) = _
  rw [integral_bernoulliMeasure]
  simp only [value, incrementProb, smul_eq_mul, Fin.val_succ, Fin.val_castSucc, pow_succ]
  field_simp
  ring

/-- Given a register value, the conditional second moment is `C² + 3 C`. -/
theorem integral_sq_step {n : ℕ} (x : Fin (n + 1)) :
    ∫ y, value y ^ 2 ∂(step n x) = value x ^ 2 + 3 * value x := by
  change (∫ y, value y ^ 2 ∂(bernoulliMeasure _ _ _)) = _
  rw [integral_bernoulliMeasure]
  simp only [value, incrementProb, smul_eq_mul, Fin.val_succ, Fin.val_castSucc, pow_succ]
  field_simp
  ring

private lemma integral_succ (n : ℕ) (f : Fin (n + 2) → ℝ) :
    ∫ y, f y ∂(law (n + 1)) = ∫ x, ∫ y, f y ∂(step n x) ∂(law n) := by
  rw [law, Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
  · rfl
  · exact Integrable.of_finite

/-- The expected doubling observable after `n` tokens is `n + 1`. -/
theorem integral_value (n : ℕ) : ∫ x, value x ∂(law n) = n + 1 := by
  induction n with
  | zero => simp [law, value]
  | succ n ih =>
    rw [integral_succ]
    simp_rw [integral_value_step]
    rw [integral_add Integrable.of_finite (integrable_const _), ih]
    simp

/-- The estimate `2 ^ x - 1` is unbiased, including on the empty stream. -/
theorem integral_estimate (n : ℕ) : ∫ x, value x - 1 ∂(law n) = n := by
  rw [integral_sub Integrable.of_finite (integrable_const _), integral_value]
  simp

/-- The second moment of the doubling observable is `1 + 3 n (n + 1) / 2`. -/
theorem integral_sq (n : ℕ) :
    ∫ x, value x ^ 2 ∂(law n) = 1 + 3 * n * (n + 1) / 2 := by
  induction n with
  | zero => simp [law, value]
  | succ n ih =>
    rw [integral_succ]
    simp_rw [integral_sq_step]
    rw [integral_add Integrable.of_finite Integrable.of_finite, ih, integral_const_mul,
      integral_value, Nat.cast_succ]
    ring

/-- If `X` is the Morris register after `n` updates, the doubling observable `2 ^ X` has
variance `n * (n - 1) / 2` under the register law. In particular, the variance is zero
both before any updates and after the certain first increment. -/
theorem variance_value (n : ℕ) : Var[value; law n] = n * ((n : ℝ) - 1) / 2 := by
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).2
    Integrable.of_finite)]
  change (∫ x, value x ^ 2 ∂(law n)) - _ = _
  rw [integral_sq, integral_value]
  ring

end Cslib.Algorithms.Lean.MorrisCounter
