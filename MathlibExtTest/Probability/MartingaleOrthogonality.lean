/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MartingaleOrthogonality
public import MathlibExt.Probability.MartingaleConditionalVariance

@[expose] public section

open MeasureTheory Filter

namespace MathlibExtTest.Probability.MartingaleOrthogonality

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The orthogonality API restates with the exact public signature. -/
example (hmart : Martingale X ℱ μ) {m n : ℕ} (hmn : m ≤ n) {Y : Ω → ℝ}
    (hY_meas : StronglyMeasurable[ℱ m] Y)
    (hY_int : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hX_sq : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ) :
    ∫ ω, (X n ω - X m ω) * Y ω ∂μ = 0 :=
  hmart.integral_sub_mul_eq_zero hmn hY_meas hY_int hX_sq

/-- Orthogonality for a constant martingale: the increments vanish, so the
integral is `0` for every `ℱ_m`-measurable square-integrable `Y`. Here `Y`
is taken constant, which is `ℱ_m`-measurable for every `m`. -/
example (c d : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∫ ω, ((fun _ _ => c) n ω - (fun _ _ => c) m ω) * (fun _ => d) ω ∂μ = 0 :=
  (martingale_const ℱ μ c).integral_sub_mul_eq_zero hmn
    stronglyMeasurable_const (integrable_const _) (fun _ => integrable_const _)

/-- Orthogonality for the zero martingale. -/
example {m n : ℕ} (hmn : m ≤ n) {Y : Ω → ℝ}
    (hY_meas : StronglyMeasurable[ℱ m] Y)
    (hY_int : Integrable (fun ω => (Y ω) ^ 2) μ) :
    ∫ ω, ((0 : ℕ → Ω → ℝ) n ω - (0 : ℕ → Ω → ℝ) m ω) * Y ω ∂μ = 0 :=
  (martingale_zero ℝ ℱ μ).integral_sub_mul_eq_zero hmn hY_meas hY_int
    (fun _ => by simp)

/-- The variance-of-increment identity restates with the exact public
signature. -/
example (hmart : Martingale X ℱ μ) {m n : ℕ} (hmn : m ≤ n)
    (hX_sq : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ) :
    ∫ ω, (X n ω - X m ω) ^ 2 ∂μ =
      ∫ ω, (X n ω) ^ 2 ∂μ - ∫ ω, (X m ω) ^ 2 ∂μ :=
  hmart.integral_sub_sq_eq hmn hX_sq

/-- The variance-of-increment identity for a constant martingale: both sides
are `0`, since the increment vanishes and `E[c^2] - E[c^2] = 0`. -/
example (c : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∫ ω, ((fun _ _ => c) n ω - (fun _ _ => c) m ω) ^ 2 ∂μ =
      ∫ ω, ((fun _ _ => c) n ω) ^ 2 ∂μ - ∫ ω, ((fun _ _ => c) m ω) ^ 2 ∂μ :=
  (martingale_const ℱ μ c).integral_sub_sq_eq hmn (fun _ => integrable_const _)

/-- The conditional variance identity restates with the exact public
signature. -/
example (hmart : Martingale X ℱ μ) (hL2 : ∀ n, MemLp (X n) 2 μ)
    {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => (X n ω - X m ω) ^ 2 | ℱ m] =ᵐ[μ]
      fun ω => (μ[fun ω' => (X n ω') ^ 2 | ℱ m]) ω - (X m ω) ^ 2 :=
  hmart.condExp_sub_sq_eq hL2 hmn

/-- The conditional variance identity for the zero martingale: both sides
are `0` a.e. -/
example {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => ((0 : ℕ → Ω → ℝ) n ω - (0 : ℕ → Ω → ℝ) m ω) ^ 2 | ℱ m] =ᵐ[μ]
      fun ω => (μ[fun ω' => ((0 : ℕ → Ω → ℝ) n ω') ^ 2 | ℱ m]) ω -
        ((0 : ℕ → Ω → ℝ) m ω) ^ 2 :=
  (martingale_zero ℝ ℱ μ).condExp_sub_sq_eq (fun _ => MemLp.zero) hmn

/-- The conditional variance identity for a constant martingale: the
increment is `0`, and `E[c^2 | ℱ_m] - c^2 = 0` a.e. -/
example (c : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => ((fun _ _ => c) n ω - (fun _ _ => c) m ω) ^ 2 | ℱ m] =ᵐ[μ]
      fun ω => (μ[fun ω' => ((fun _ _ => c) n ω') ^ 2 | ℱ m]) ω -
        ((fun _ _ => c) m ω) ^ 2 :=
  (martingale_const ℱ μ c).condExp_sub_sq_eq (fun _ => memLp_const c) hmn

/-- Apply orthogonality to the martingale constructed from a terminal variable. -/
example (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) {m n : ℕ} (hmn : m ≤ n)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ m] Y)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    ∫ ω, (μ[Z | ℱ n] ω - μ[Z | ℱ m] ω) * Y ω ∂μ = 0 :=
  (martingale_condExp Z ℱ μ).integral_sub_mul_eq_zero hmn hY hY2
    (fun k => (hZ.condExp (m := ℱ k) one_le_two).integrable_sq)

/-- The same constructed martingale satisfies the second-moment increment identity. -/
example (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) {m n : ℕ} (hmn : m ≤ n) :
    ∫ ω, (μ[Z | ℱ n] ω - μ[Z | ℱ m] ω) ^ 2 ∂μ =
      ∫ ω, (μ[Z | ℱ n] ω) ^ 2 ∂μ - ∫ ω, (μ[Z | ℱ m] ω) ^ 2 ∂μ :=
  (martingale_condExp Z ℱ μ).integral_sub_sq_eq hmn
    (fun k => (hZ.condExp (m := ℱ k) one_le_two).integrable_sq)

/-- Its conditional increment variance follows from the source-facing API. -/
example (Z : Ω → ℝ) (hZ : MemLp Z 2 μ) {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => (μ[Z | ℱ n] ω - μ[Z | ℱ m] ω) ^ 2 | ℱ m] =ᵐ[μ]
      fun ω => μ[fun ω' => (μ[Z | ℱ n] ω') ^ 2 | ℱ m] ω - (μ[Z | ℱ m] ω) ^ 2 :=
  (martingale_condExp Z ℱ μ).condExp_sub_sq_eq
    (fun k => hZ.condExp (m := ℱ k) one_le_two) hmn

#print axioms MeasureTheory.Martingale.integral_sub_mul_eq_zero
#print axioms MeasureTheory.Martingale.integral_sub_sq_eq
#print axioms MeasureTheory.Martingale.condExp_sub_sq_eq

end MathlibExtTest.Probability.MartingaleOrthogonality
