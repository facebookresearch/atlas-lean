/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.FactorAnalysis
public import Mathlib.Probability.Moments.Variance
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Identification in the standardized one-factor model -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExt.Probability.Statistics.Measurement

private theorem oneFactor_observed_covariance {ι Ω : Type*} [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → ℝ) (ε : ι → Ω → ℝ) (l : ι → ℝ)
    (hF : MemLp F 2 P) (hε : ∀ i, MemLp (ε i) 2 P) (hVar : Var[F; P] = 1)
    (hFε : ∀ i, cov[F, ε i; P] = 0)
    (hεε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0) :
    (Matrix.of fun i j => cov[l i • F + ε i, l j • F + ε j; P]) =
      oneFactorCovariance l (fun i => Var[ε i; P]) := by
  have hL (i : ι) : MemLp (l i • F) 2 P := hF.const_smul _
  ext i j
  rw [Matrix.of_apply, covariance_add_left (hL i) (hε i) ((hL j).add (hε j)),
    covariance_add_right (hL i) (hL j) (hε j), covariance_add_right (hε i) (hL j) (hε j)]
  rw [covariance_smul_left, covariance_smul_right, covariance_self hF.aemeasurable, hVar,
    covariance_smul_left, covariance_smul_right, covariance_comm (ε i) F, hFε i, hFε j]
  by_cases hij : i = j
  · subst j
    rw [oneFactorCovariance_diag, covariance_self (hε i).aemeasurable]
    ring
  · rw [oneFactorCovariance_offDiag _ _ hij, hεε i j hij]
    ring

/-- **Identification of a one-factor model from three indicators.** Suppose the square-integrable
factor `F` has variance one, and the square-integrable errors `ε` are pairwise uncorrelated and
uncorrelated with the factor. The observations `Xᵢ = lᵢ F + εᵢ` have covariance `C` with
off-diagonal entries `lᵢ lⱼ` and diagonal entries `lᵢ² + Var(εᵢ)`. With at least three indicators
and every loading nonzero, `lᵢ² = Cᵢⱼ Cᵢₖ / Cⱼₖ` for every distinct triple, and the error variance
is `Cᵢᵢ - lᵢ²`. Any other one-factor parameters producing `C` have matching error variances and
loadings differing by at most one common sign. Fixing the sign of any one loading removes the
ambiguity. Normality and independence are not required. See Brunner, *Confirmatory factor
analysis, part 1*, slides 3–4 and 13. -/
theorem one_factor_identification {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → ℝ) (ε : ι → Ω → ℝ) (l : ι → ℝ)
    (hF : MemLp F 2 P) (hε : ∀ i, MemLp (ε i) 2 P) (hVar : Var[F; P] = 1)
    (hFε : ∀ i, cov[F, ε i; P] = 0) (hεε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0) :
    let ψ := fun i => Var[ε i; P]
    let X := fun i => l i • F + ε i
    let C := Matrix.of fun i j => cov[X i, X j; P]
    C = oneFactorCovariance l ψ ∧
      (∀ i j, i ≠ j → C i j = l i * l j) ∧
      (3 ≤ Fintype.card ι → (∀ i, l i ≠ 0) →
        (∀ i j k, i ≠ j → i ≠ k → j ≠ k → l i ^ 2 = C i j * C i k / C j k) ∧
        (∀ i, ψ i = C i i - l i ^ 2) ∧
        (∀ l' ψ', oneFactorCovariance l' ψ' = C →
          (l' = l ∨ l' = -l) ∧ ψ' = ψ ∧ (∀ i, (0 < l' i ↔ 0 < l i) → l' = l))) := by
  intro ψ X C
  have hC : C = oneFactorCovariance l ψ := oneFactor_observed_covariance F ε l hF hε hVar hFε hεε
  refine ⟨hC, ?_, ?_⟩
  · intro i j hij
    rw [hC, oneFactorCovariance_offDiag _ _ hij]
  · intro hcard hl
    refine ⟨?_, ?_, ?_⟩
    · intro i j k hij hik hjk
      rw [hC, pow_two]
      exact sq_loading_of_oneFactorCovariance l ψ i j k hij hik hjk (hl j) (hl k)
    · intro i
      rw [hC, pow_two]
      exact noise_of_oneFactorCovariance l ψ i
    · intro l' ψ' h'
      have hcard' : Fintype.card (Fin 3) ≤ Fintype.card ι := by simpa using hcard
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard'
      have hne (i j : Fin 3) (hij : i ≠ j) : e i ≠ e j := fun h => hij (e.injective h)
      obtain ⟨hsign, hψ⟩ := eq_or_eq_neg_of_oneFactorCovariance_eq_of_all_ne l ψ l' ψ'
        (e 0) (e 1) (e 2) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
        hl (h'.trans hC)
      refine ⟨hsign, hψ, fun i hi => hsign.resolve_right ?_⟩
      intro hneg
      have he : l' i = -l i := congrFun hneg i
      rw [he, neg_pos] at hi
      rcases lt_or_gt_of_ne (hl i) with hlt | hgt
      · exact (not_lt_of_gt hlt) (hi.mp hlt)
      · exact (not_lt_of_gt hgt) (hi.mpr hgt)

/-- **A zero loading can destroy one-factor identification.** Loadings `(0, 1, 1)` with error
variances `(1, 4, 1)` and loadings `(0, 2, 1/2)` with error variances `(1, 1, 7/4)` give the same
covariance. Both error-variance vectors are nonnegative, and the loading vectors are not related
by a common sign. -/
theorem one_factor_zero_loading_counterexample :
    let l : Fin 3 → ℝ := ![0, 1, 1]
    let ψ : Fin 3 → ℝ := ![1, 4, 1]
    let l' : Fin 3 → ℝ := ![0, 2, 1 / 2]
    let ψ' : Fin 3 → ℝ := ![1, 1, 7 / 4]
    (∀ i, 0 ≤ ψ i ∧ 0 ≤ ψ' i) ∧
      oneFactorCovariance l' ψ' = oneFactorCovariance l ψ ∧ l' ≠ l ∧ l' ≠ -l := by
  intro l ψ l' ψ'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [ψ, ψ']
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [oneFactorCovariance, l, l', ψ, ψ', Matrix.vecMulVec_apply, Matrix.diagonal_apply]
  · intro h
    have he := congrFun h 1
    norm_num [l, l'] at he
  · intro h
    have he := congrFun h 1
    norm_num [l, l', Pi.neg_apply] at he

end MathlibExt.Probability.Statistics.Measurement
