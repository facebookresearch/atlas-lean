/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.ExponentialColeHopf
import MathlibExt.RingTheory.MvPowerSeries.ExponentialDerivative
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! # Rational exponential-series evaluation and truncation tests -/

open MvPowerSeries
open MvPowerSeries.ColeHopf

-- Zero constant coefficient cannot support reciprocal evaluation, even for X.
example : constantCoeff (X (0 : Fin 2) : MvPowerSeries (Fin 2) ℚ) = 0 := by simp

-- All real points, signed weights and negative/zero rates: no majorant assumption
-- is needed merely to evaluate a finite sum of exponentials.
example (x : Fin 2 → ℝ) :
    HasSum (seriesTerm (exponentialHeatMoment Finset.univ
      ![(-2 : ℚ), 3] ![(-1 : ℚ), 0] 2 0) x)
      (-2 * Real.exp (2 * x 0 - x 1) + 3) := by
  convert hasSum_exponentialHeatMoment Finset.univ ![(-2 : ℚ), 3] ![(-1 : ℚ), 0] 2 0 x using 1
  norm_num [_root_.ColeHopf.heatMoment, Fin.sum_univ_two, sub_eq_add_neg]

private def weights : Fin 2 → ℚ := fun _ => 1
private def rates : Fin 2 → ℚ := ![0, 1]
private noncomputable def H (n : ℕ) := exponentialHeatMoment Finset.univ weights rates 1 n
private noncomputable def U := exponentialBurgersSeries Finset.univ weights rates 1

private def m0 : GeometricMajorant (Fin 2) := ⟨2, fun _ => 1, by norm_num, by norm_num⟩
private def m1 : GeometricMajorant (Fin 2) := ⟨1, fun _ => 1, by norm_num, by norm_num⟩
private def mi : GeometricMajorant (Fin 2) := ⟨1/2, fun _ => 1/4, by norm_num, by norm_num⟩
private def mu : GeometricMajorant (Fin 2) := ⟨1, fun _ => 1/8, by norm_num, by norm_num⟩
private def box : Fin 2 → ℚ≥0 := fun _ => 1/16

private theorem majorant0 : IsMajorized (H 0) m0 := by
  have h := isMajorized_exponentialHeatMoment Finset.univ weights rates 1 0
    (R := fun _ => 1) (by norm_num)
    (by intro i _; fin_cases i <;> norm_num [rates])
    (by intro i _; fin_cases i <;> norm_num [rates])
  simpa [H, weights, rates, Fin.sum_univ_two, m0] using h

private theorem majorant1 : IsMajorized (H 1) m1 := by
  have h := isMajorized_exponentialHeatMoment Finset.univ weights rates 1 1
    (R := fun _ => 1) (by norm_num)
    (by intro i _; fin_cases i <;> norm_num [rates])
    (by intro i _; fin_cases i <;> norm_num [rates])
  simpa [H, weights, rates, Fin.sum_univ_two, m1] using h

private theorem majorantInv : IsMajorized (H 0)⁻¹ mi := by
  have h := isMajorized_inv (H 0) (c := 2) (M := 2)
    (by norm_num [H, weights, Fin.sum_univ_two]) (by norm_num)
    (R := fun _ => 1) (r := fun _ => 1/4) (by norm_num) (by norm_num) (by norm_num)
    (fun α _ => majorant0 α) (by norm_num [Fin.prod_univ_two])
  simpa [mi] using h

private theorem majorantU : IsMajorized U mu := by
  have h1 := majorant1.mono
    (⟨1, fun _ => 1/4, by norm_num, by norm_num⟩ : GeometricMajorant (Fin 2))
    (by norm_num [m1]) (by norm_num [m1])
  have h := isMajorized_exponentialBurgersSeries Finset.univ weights rates 1
    (fun _ => 1/4) h1 majorantInv (by simp) (by simp [mi])
  convert h using 1 <;> norm_num [U, mi, mu]

-- The quotient is nontrivial, and its constant coefficient has the correct sign.
example : constantCoeff U = -1 := by
  norm_num [U, exponentialBurgersSeries, coleHopf, pderiv_one_exponentialHeatMoment,
    weights, rates, Fin.sum_univ_two]

-- The new coefficient family really is the previously constructed formal heat solution.
example : H 0 = heatSolution 1 0 1 (exponentialHeatMoment Finset.univ weights rates 0 0) :=
  exponentialHeatMoment_eq_heatSolution _ _ _ _

example : U = Causal.solution 0 (burgersRhs 1 1)
    (coleHopf 1 1 (exponentialHeatMoment Finset.univ weights rates 0 0)) :=
  exponentialBurgersSeries_eq_solution _ _ _ _ (by norm_num [weights, Fin.sum_univ_two])

-- The coefficient certificate also discharges the denominator condition of
-- the actual classical PDE; no independent positivity proof is supplied here.
example (x : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ (1/16 : ℝ)) :
    let u := _root_.ColeHopf.exponentialSolution Finset.univ
      (fun i => (weights i : ℝ)) (fun i => (rates i : ℝ)) 1
    deriv (fun t => u t (x 1)) (x 0) + u (x 0) (x 1) * deriv (u (x 0)) (x 1) =
      iteratedDeriv 2 (u (x 0)) (x 1) := by
  have h := geometricSum_exponentialBurgersSeries Finset.univ weights rates 1
    (by norm_num [weights, Fin.sum_univ_two]) majorant0 majorant1 majorantInv
    (r := box) (by norm_num [box, m0]) (by norm_num [box, m1])
    (by norm_num [box, mi]) (x := x) (by simpa [box] using hx)
  simpa using _root_.ColeHopf.exponentialSolution_burgers Finset.univ
    (fun i => (weights i : ℝ)) (fun i => (rates i : ℝ)) 1 (x 0) (x 1)
    (by simpa only [Rat.cast_one] using h.2)

-- Entire-box certificate for an actual classical Burgers solution:
-- on |t|,|x| <= 1/16, its 8-by-8 coefficient rectangle has error <= 1/32.
example (x : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ (1/16 : ℝ)) :
    |(-2 * Real.exp (x 0 + x 1) / (1 + Real.exp (x 0 + x 1))) -
      rectangularSum (fun _ => 8) U x| ≤ (1/32 : ℝ) := by
  have h := exponentialSolution_truncation Finset.univ weights rates 1
    (by norm_num [weights, Fin.sum_univ_two]) majorant0 majorant1 majorantInv majorantU
    (r := box) (by norm_num [box, m0]) (by norm_num [box, m1])
    (by norm_num [box, mi]) (by norm_num [box, mu]) (fun _ => 8) (x := x)
    (by simpa [box] using hx)
  norm_num [_root_.ColeHopf.exponentialSolution, _root_.ColeHopf.heatMoment,
    weights, rates, Fin.sum_univ_two, geometricTailBound, ratio, box, mu, Fin.prod_univ_two] at h
  simpa [U, rates, div_eq_mul_inv, mul_assoc] using h

-- Strict interior and inverse smallness are real restrictions, not inferred
-- from any finite coefficient prefix.
example : ¬ ((1/8 : ℚ) < mu.radius 0) := by norm_num [mu]
example : ¬ ((2 : ℚ) / |2| * ((∏ _ : Fin 2, (1 - (1/2 : ℚ))⁻¹) - 1) ≤ 1) := by
  norm_num [Fin.prod_univ_two]

-- The explicit coefficient API connects to the canonical formal exponential.
example (a b : ℚ) : exponentialSeries₂ a b =
    expOfConstantCoeffZero (C a * X 0 + C b * X 1) (by simp) :=
  exponentialSeries₂_eq_expOfConstantCoeffZero a b

-- The bridge lets downstream clients use the canonical derivative theorem.
example : pderiv 0 (exponentialSeries₂ (-2) 0) =
    C (-2) * exponentialSeries₂ (-2) 0 := by
  rw [exponentialSeries₂_eq_expOfConstantCoeffZero]
  rw [pderiv_expOfConstantCoeffZero]
  simp
