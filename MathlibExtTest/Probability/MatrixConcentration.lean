/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MatrixConcentration

/-!
# Tests for `MathlibExt.Probability.MatrixConcentration`

The five results are applied in small cases: subadditivity for a single summand, the Gaussian
series with the Hermitian hypotheses discharged from the coefficients, the Chernoff bound at
`ε = 0` (the trivial bound) and at `ε = 1/2`, and the Bernstein and Hoeffding bounds for
Rademacher-type summands `Xₖ = ±Aₖ`, whose variance matrix is `∑ₖ Aₖ²` and for which the
Hoeffding domination hypothesis holds with equality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.MatrixLaplaceTransform
open MathlibExt.Probability.MatrixConcentrationWanted
open scoped ComplexOrder

namespace MathlibExtTest.Probability.MatrixConcentration

/-- Subadditivity for a single summand, where independence is automatic:
`E tr e^{θX} ≤ tr exp(log E e^{θX})`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix (Fin 2) (Fin 2) ℂ) (hm : Measurable X) (hX : ∀ ω, (X ω).IsHermitian)
    (θ : ℝ) (hexp : ∀ i j, Integrable (fun ω => NormedSpace.exp (θ • X ω) i j) μ)
    (hsum : Integrable (fun ω => RCLike.re (NormedSpace.exp (θ • X ω)).trace) μ) :
    ∫ ω, RCLike.re (NormedSpace.exp (θ • X ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp
        (cfc Real.log (expect μ fun ω => NormedSpace.exp (θ • X ω)))).trace := by
  simpa using integral_trace_exp_sum_le (N := 1) (X := fun _ => X) (fun _ => hm)
    iIndepFun.of_subsingleton (fun _ => hX) θ (fun _ => hexp) (by simpa using hsum)

/-- A matrix Gaussian series with Hermitian coefficients is Hermitian. -/
lemma isHermitian_gaussianSeries {n : Type*} [Fintype n] {N : ℕ} {A : Fin N → Matrix n n ℂ}
    (hA : ∀ k, (A k).IsHermitian) (ω : Fin N → ℝ) : (gaussianSeries A ω).IsHermitian := by
  refine isSelfAdjoint_sum _ fun k _ => ?_
  rw [← RCLike.real_smul_eq_coe_smul]
  exact (IsSelfAdjoint.all (ω k)).smul (hA k)

/-- The variance matrix `∑ₖ Aₖ²` of Hermitian coefficients is Hermitian. -/
lemma isHermitian_sum_mul_self {n : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    {A : Fin N → Matrix n n ℂ} (hA : ∀ k, (A k).IsHermitian) : (∑ k, A k * A k).IsHermitian :=
  isSelfAdjoint_sum _ fun k _ => by
    have h : (A k * A k).IsHermitian := by simpa [sq] using (hA k).pow 2
    exact h

/-- The Gaussian-series bounds for `2 × 2` Hermitian coefficients, with the Hermitian
hypotheses discharged from the coefficients. -/
example {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (hA : ∀ k, (A k).IsHermitian) (t : ℝ)
    (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).real
        {ω | t ≤ (isHermitian_gaussianSeries hA ω).lambdaMax} ≤
      2 * Real.exp (-t ^ 2 / (2 * (isHermitian_sum_mul_self hA).lambdaMax)) ∧
    ∫ ω, (isHermitian_gaussianSeries hA ω).lambdaMax
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
      Real.sqrt (2 * (isHermitian_sum_mul_self hA).lambdaMax * Real.log 2) := by
  obtain ⟨h1, h2⟩ := matrix_gaussian_series hA (isHermitian_gaussianSeries hA)
    (isHermitian_sum_mul_self hA)
  exact ⟨by simpa using h2 t ht, by simpa using h1⟩

/-- At `ε = 0` the Chernoff upper tail bound is the trivial bound `d`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → Matrix (Fin 3) (Fin 3) ℂ} (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hX : ∀ k ω, (X k ω).IsHermitian) {L : ℝ} (hL : 0 < L)
    (hlow : ∀ k ω, 0 ≤ (hX k ω).lambdaMin) (hup : ∀ k ω, (hX k ω).lambdaMax ≤ L)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hEY : (expect μ fun ω => ∑ k, X k ω).IsHermitian) :
    μ.real {ω | hEY.lambdaMax ≤ (hY ω).lambdaMax} ≤ 3 := by
  simpa using (matrix_chernoff hmeas hind hX hL hlow hup hY hEY).1 0 le_rfl

/-- The Chernoff lower tail bound at `ε = 1/2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → Matrix (Fin 3) (Fin 3) ℂ} (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hX : ∀ k ω, (X k ω).IsHermitian)
    (hlow : ∀ k ω, 0 ≤ (hX k ω).lambdaMin) (hup : ∀ k ω, (hX k ω).lambdaMax ≤ 1)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hEY : (expect μ fun ω => ∑ k, X k ω).IsHermitian) :
    μ.real {ω | (hY ω).lambdaMin ≤ (1 - 1 / 2) * hEY.lambdaMin} ≤
      3 * (Real.exp (-(1 / 2)) / (1 - 1 / 2) ^ (1 - 1 / 2 : ℝ)) ^ (hEY.lambdaMin / 1) := by
  exact_mod_cast (matrix_chernoff hmeas hind hX one_pos hlow hup hY hEY).2 (1 / 2)
    (by norm_num) (by norm_num)

/-- The matrix Bernstein bound for Rademacher-type summands `Xₖ = ±Aₖ` with `λmax(Xₖ) ≤ 1`. Their
variance matrix is `∑ₖ E Xₖ² = ∑ₖ Aₖ²`, which is nonzero as soon as some `Aₖ` is, so the bound
reads `d exp(-(t²/2) / (λmax(∑ₖ Aₖ²) + t/3))`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → Matrix (Fin 2) (Fin 2) ℂ} (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hX : ∀ k ω, (X k ω).IsHermitian)
    {A : Fin N → Matrix (Fin 2) (Fin 2) ℂ} (hsign : ∀ k ω, X k ω = A k ∨ X k ω = -A k)
    (hup : ∀ k ω, (hX k ω).lambdaMax ≤ 1)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ) (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian) (hσ : (∑ k, A k * A k).IsHermitian) (t : ℝ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤ 2 * Real.exp (-(t ^ 2 / 2) / (hσ.lambdaMax + t / 3)) := by
  have hsq : ∀ k ω, X k ω * X k ω = A k * A k := fun k ω => by
    rcases hsign k ω with h | h <;> simp [h]
  have hint2 : ∀ k i j, Integrable (fun ω => (X k ω * X k ω) i j) μ := fun k i j => by
    simp only [hsq]
    exact integrable_const _
  have hE : (∑ k, expect μ fun ω => X k ω * X k ω) = ∑ k, A k * A k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ext i j
    simp [expect, hsq]
  have hV : (∑ k, expect μ fun ω => X k ω * X k ω).IsHermitian := hE ▸ hσ
  have hlam : ∀ {M M' : Matrix (Fin 2) (Fin 2) ℂ} (_ : M = M') (hM : M.IsHermitian)
      (hM' : M'.IsHermitian), hM.lambdaMax = hM'.lambdaMax := by
    rintro _ _ rfl _ _
    rfl
  have h := matrix_bernstein hmeas hind hX zero_le_one hup hint hint2 hcenter hY hV t ht
  rw [hlam hE hV hσ] at h
  simpa using h

/-- Rademacher-type summands `Xₖ = ±Aₖ` satisfy the Hoeffding domination `Xₖ² ≼ Aₖ²` with
equality, so the matrix Hoeffding bound applies to them. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → Matrix (Fin 2) (Fin 2) ℂ} (hmeas : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hX : ∀ k ω, (X k ω).IsHermitian)
    {A : Fin N → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ k, (A k).IsHermitian) (hsign : ∀ k ω, X k ω = A k ∨ X k ω = -A k)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ) (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian) (hσ : (∑ k, A k * A k).IsHermitian)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤ 2 * Real.exp (-t ^ 2 / (8 * hσ.lambdaMax)) := by
  have hdom : ∀ k ω, (A k * A k - X k ω * X k ω).PosSemidef := fun k ω => by
    rcases hsign k ω with h | h <;> rw [h] <;> simp only [neg_mul_neg, sub_self] <;>
      exact Matrix.PosSemidef.zero
  simpa using matrix_hoeffding hmeas hind hX hA hdom hint hcenter hY hσ t ht

end MathlibExtTest.Probability.MatrixConcentration
