/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.UStatistic

/-!
# Tests for the Hájek projection of U-statistics

Order one (the projection of the sample mean is exact), a centred degenerate kernel whose first
projection vanishes, the sample-variance kernel under a fair coin (non-vacuity of the remainder
limit), and the convention `uStatistic = 0` when the degree exceeds the sample size.
-/

@[expose] public section

namespace UStatisticProjectionTest

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- Order one: the Hájek projection of the sample mean is the sample mean itself, so the
remainder vanishes identically for `n ≥ 1`. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : (Fin 1 → ℝ) → ℝ}
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, (uStatistic g x - hajekProjection μ g x) ^ 2 ∂(Measure.pi fun _ : Fin n => μ) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hproj (y : Fin 1 → ℝ) : hoeffdingProj μ g 1 y = g y := by
    have hy : (fun _ : Fin 1 => y 0) = y := funext fun j => by rw [Fin.fin_one_eq_zero j]
    simp [hoeffdingProj, hy]
  have hU (x : Fin n → ℝ) : uStatistic g x = (∑ i, g (fun _ => x i)) / n := by
    rw [uStatistic, Nat.descFactorial_one]
    congr 1
    exact Fintype.sum_equiv Equiv.uniqueEmbeddingEquivResult _ _ (fun f => by
      congr 1
      funext k
      rw [Subsingleton.elim k default]
      rfl)
  have hpt (x : Fin n → ℝ) : uStatistic g x - hajekProjection μ g x = 0 := by
    rw [hU, hajekProjection_eq_of_symm μ (fun σ y => by rw [Subsingleton.elim σ 1]; rfl)]
    simp_rw [hproj]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_one]
    field_simp
    ring
  simp [hpt]

/-- Degenerate kernel: for `h(y) = y 0 * y 1` and a centred law the first projection is `0`,
so `σ₁² = 0` and the theorems assert only `n · E[(U - Ĥ)²] → 0`, not a nonzero limit. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : ∫ x, x ∂μ = 0) :
    hoeffdingProj μ (fun y : Fin 2 → ℝ => y 0 * y 1) 1 = fun _ => 0 := by
  funext y
  have hmp := measurePreserving_eval (fun _ : Fin (2 - 1) => μ) 0
  have hz : ∫ z : Fin (2 - 1) → ℝ, z 0 ∂(Measure.pi fun _ => μ) = 0 := by
    have he := integral_map (f := fun x : ℝ => x) hmp.aemeasurable
      (hmp.map_eq.symm ▸ aestronglyMeasurable_id)
    rw [hmp.map_eq] at he
    exact he.symm.trans h0
  simp [hoeffdingProj, integral_const_mul, hz]

/-- The fair coin on `{0, 1} ⊆ ℝ`. -/
noncomputable def coin : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

instance isProbabilityMeasure_coin : IsProbabilityMeasure coin := by
  constructor
  simp [coin, ENNReal.inv_two_add_inv_two]

private theorem integral_coin (g : ℝ → ℝ) : ∫ t, g t ∂coin = (g 0 + g 1) / 2 := by
  rw [coin, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp
  ring

private theorem integral_pi_coin {k : ℕ} (i : Fin k) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ z : Fin k → ℝ, g (z i) ∂(Measure.pi fun _ => coin) = (g 0 + g 1) / 2 := by
  have hmp := measurePreserving_eval (fun _ : Fin k => coin) i
  have he := integral_map (f := g) hmp.aemeasurable (hmp.map_eq.symm ▸ hg.aestronglyMeasurable)
  rw [hmp.map_eq, integral_coin] at he
  exact he.symm

/-- Non-vacuity: the sample-variance kernel `(y 0 - y 1) ^ 2 / 2` is symmetric and square
integrable under the coin law, so the remainder theorem applies. Prove via
`tendsto_mul_integral_sq_uStatistic_sub_hajekProjection`. -/
example :
    Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ x, (uStatistic (fun y : Fin 2 → ℝ => (y 0 - y 1) ^ 2 / 2) x -
          hajekProjection coin (fun y : Fin 2 → ℝ => (y 0 - y 1) ^ 2 / 2) x) ^ 2
          ∂(Measure.pi fun _ : Fin n => coin))
      atTop (𝓝 0) := by
  refine tendsto_mul_integral_sq_uStatistic_sub_hajekProjection coin ?_ ?_
  · intro σ y
    have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have hcases : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
    rcases hcases (σ 0) (σ 1) h01 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [Function.comp_apply, ha, hb]
    · simp only [Function.comp_apply, ha, hb]
      ring
  · have hcoin : ∀ᵐ x ∂coin, x = 0 ∨ x = 1 := by
      refine Measure.ae_smul_measure ?_ _
      rw [ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq]
      simp
    have hpi : ∀ᵐ y ∂(Measure.pi fun _ : Fin 2 => coin), ∀ i, y i = 0 ∨ y i = 1 := by
      rw [ae_all_iff]
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => coin) (i := i)).eventually hcoin
    refine MemLp.of_bound (by fun_prop : Continuous fun y : Fin 2 → ℝ =>
      (y 0 - y 1) ^ 2 / 2).aestronglyMeasurable 1 ?_
    filter_upwards [hpi] with y hy
    rcases hy 0 with h0 | h0 <;> rcases hy 1 with h1 | h1 <;> norm_num [h0, h1]

/-- Boundary `m > n`: the U-statistic is `0` by convention (there are no injective index maps),
which is why the identities assume `m ≤ n`. -/
example (h : (Fin 2 → ℝ) → ℝ) (x : Fin 1 → ℝ) : uStatistic h x = 0 := by
  rw [uStatistic, show (1 : ℕ).descFactorial 2 = 0 by decide, Nat.cast_zero, div_zero]

/-! Nonsymmetric kernel (fair coin, `m = n = 2`, `h y = y 0`): the U-statistic only sees the
symmetrized kernel `(y 0 + y 1) / 2`, so at the sample `(1, 1)` the projection equals the
U-statistic, while the first-coordinate formula `θ + (m / n) ∑ (h₁(xᵢ) - θ)` gives `3 / 2`. -/

/-- The U-statistic of the nonsymmetric kernel `y 0` at the sample `(1, 1)` is `1`. -/
example : uStatistic (fun y : Fin 2 → ℝ => y 0) (fun _ : Fin 2 => (1 : ℝ)) = 1 := by
  simp [uStatistic, Fintype.card_embedding_eq]

/-- The (symmetrized) Hájek projection at the sample `(1, 1)` is also `1`. -/
example : hajekProjection coin (fun y : Fin 2 → ℝ => y 0) (fun _ : Fin 2 => (1 : ℝ)) = 1 := by
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  simp only [hajekProjection, hoeffdingProj, hperm]
  have hcoin : Integrable id coin := by
    rw [coin]
    exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
      (by simp)
  have hint (i : Fin 2) : Integrable (fun y : Fin 2 → ℝ => y i) (Measure.pi fun _ => coin) :=
    (measurePreserving_eval (fun _ : Fin 2 => coin) i).integrable_comp_of_integrable hcoin
  have h0 := integral_pi_coin (k := 2) 0 measurable_id
  have h1 := integral_pi_coin (k := 2) 1 measurable_id
  simp only [id] at h0 h1
  have hθ : ∫ (y : Fin 2 → ℝ), 2⁻¹ * (y 0 + y 1) ∂(Measure.pi fun _ => coin) = 1 / 2 := by
    rw [integral_const_mul, integral_add (hint 0) (hint 1), h0, h1]
    norm_num
  have hin := integral_pi_coin (k := 1) 0 (g := fun t => 2⁻¹ * (1 + t)) (by fun_prop)
  simp only [Finset.sum_pair (show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide),
    Function.comp_apply, Equiv.Perm.coe_one, id, Equiv.swap_apply_left]
  simp only [Nat.add_one_sub_one] at *
  simp [hin]
  rw [hθ]
  norm_num

/-- The unsymmetrized first-coordinate formula gives `3 / 2 ≠ 1` at the same sample. -/
example : (∫ y, (fun y : Fin 2 → ℝ => y 0) y ∂(Measure.pi fun _ => coin)) +
    (2 : ℝ) / 2 * ∑ i : Fin 2, (hoeffdingProj coin (fun y : Fin 2 → ℝ => y 0) 1
      (fun _ => (fun _ : Fin 2 => (1 : ℝ)) i) -
      ∫ y, (fun y : Fin 2 → ℝ => y 0) y ∂(Measure.pi fun _ => coin)) = 3 / 2 := by
  have hθ := integral_pi_coin (k := 2) 0 measurable_id
  simp only [id] at hθ
  simp [hoeffdingProj, hθ]
  norm_num

end UStatisticProjectionTest
