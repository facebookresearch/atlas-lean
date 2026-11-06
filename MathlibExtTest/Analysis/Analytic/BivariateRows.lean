/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact source consumer adapts the statement in Fermat's Last Theorem
in Lean 4, revision 6e837e75355538c7f80bab5b956861e86c4eacc2.
Source path (join the following two lines):
Theorems/Thm_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_
and_tsum_mul_eval_eq_of_tsum_mul_eval_eq.lean
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
The source's NOTICE identifies no individual author for this file.
The applications and boundaries below are new importing proofs.
-/
module

public import MathlibExt.Analysis.Analytic.BivariateRows

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Importing applications and boundaries for polynomial row extraction -/

open scoped Topology
open Finset FormalMultilinearSeries

namespace BivariateRowsTest

/-- The exact original statement is consumed through the public row API. -/
public theorem exact_source
    (A : ℕ × ℕ → ℂ) (D₁ D₂ : Polynomial ℂ)
    (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hD₂ : D₂.eval 0 ≠ 0) (hr : 0 < r)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A m * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A m * X ^ m.1 * Y ^ m.2) *
        (D₁.eval X * D₂.eval Y) = MvPolynomial.eval ![X, Y] P) :
    ∃ (q : ℕ → Polynomial ℂ) (r₂ : ℝ), 0 < r₂ ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
        Summable (fun m : ℕ => ‖A (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, A (m, j) * X ^ m) * D₁.eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < r₂ →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D₂.eval Y =
          MvPolynomial.eval ![X, Y] P) :=
  MvPolynomial.exists_polynomial_rows A D₁ D₂ P r hD₂ hr h

private theorem scalar_coefficients_unique (a b : ℕ → ℂ) (r : ℝ)
    (hr : 0 < r) (f : ℂ → ℂ)
    (ha : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => b n * z ^ n) (f z)) :
    a = b := by
  have series (c : ℕ → ℂ)
      (hc : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => c n * z ^ n) (f z)) :
      HasFPowerSeriesAt f (ofScalars ℂ c) 0 := by
    rw [hasFPowerSeriesAt_iff]
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) hr)
      fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right] at hz
    simpa only [coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
      using hc z hz
  exact ofScalars_series_injective ℂ ℂ
    ((series a ha).eq_formalMultilinearSeries (series b hb))

private theorem polynomial_hasSum (p : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => p.coeff n * z ^ n) (p.eval z) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  exact hasSum_sum_of_ne_finset_zero fun n hn => by
    rw [Polynomial.notMem_support_iff.mp hn, zero_mul]

private theorem polynomial_eq_of_eval_disk (p q : Polynomial ℂ) (r : ℝ)
    (hr : 0 < r) (h : ∀ z : ℂ, ‖z‖ < r → p.eval z = q.eval z) :
    p = q := by
  have hc := scalar_coefficients_unique p.coeff q.coeff r hr
    (fun z => p.eval z) (fun z _ => polynomial_hasSum p z)
    (fun z hz => (h z hz).symm ▸ polynomial_hasSum q z)
  exact Polynomial.ext fun n => congrFun hc n

private theorem geometric_series (c z : ℂ) (h : ‖c * z‖ < 1) :
    Summable (fun n : ℕ => ‖c ^ n * z ^ n‖) ∧
    (∑' n : ℕ, c ^ n * z ^ n) * (1 - c * z) = 1 := by
  constructor
  · simpa only [mul_pow] using summable_norm_geometric_of_norm_lt_one h
  · rw [← tsum_congr (fun n => mul_pow c z n),
      tsum_geometric_of_norm_lt_one h]
    apply inv_mul_cancel₀
    intro he
    have heq : c * z = 1 := (sub_eq_zero.mp he).symm
    simp [heq] at h

private def shifted (c : ℂ) (n : ℕ) : ℂ :=
  if 0 < n then c ^ (n - 1) else 0

private theorem shifted_series (c z : ℂ) (h : ‖c * z‖ < 1) :
    Summable (fun n : ℕ => ‖shifted c n * z ^ n‖) ∧
    (∑' n : ℕ, shifted c n * z ^ n) * (1 - c * z) = z := by
  have hterm (n : ℕ) : shifted c (n + 1) * z ^ (n + 1) =
      z * (c * z) ^ n := by
    simp [shifted, pow_succ, mul_pow]
    ring
  have hn : Summable (fun n : ℕ => ‖shifted c n * z ^ n‖) := by
    apply (summable_nat_add_iff 1).mp
    exact ((summable_norm_geometric_of_norm_lt_one h).mul_left ‖z‖).congr
      fun n => by rw [hterm, norm_mul]
  have ht : HasSum (fun n : ℕ => shifted c n * z ^ n)
      (z * (1 - c * z)⁻¹) := by
    apply (hasSum_nat_add_iff' 1).mp
    convert (hasSum_geometric_of_norm_lt_one h).mul_left z using 1
    · exact funext hterm
    · simp [shifted]
  refine ⟨hn, ?_⟩
  have hne : 1 - c * z ≠ 0 := by
    intro h0
    have h1 := (geometric_series c z h).2
    simp [h0] at h1
  rw [ht.tsum_eq, mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-- Coefficients of (X+Y)/((1-2X)(1-3Y)); the shifts exclude zero. -/
@[expose] public def rationalCoefficients (m : ℕ × ℕ) : ℂ :=
  (if 0 < m.1 then 2 ^ (m.1 - 1) else 0) * 3 ^ m.2 +
    2 ^ m.1 * (if 0 < m.2 then 3 ^ (m.2 - 1) else 0)

/-- The rational example satisfies the joint, absolutely convergent input. -/
public theorem rational_input (X Y : ℂ) (hX : ‖X‖ < 1 / 4)
    (hY : ‖Y‖ < 1 / 4) :
    Summable (fun m : ℕ × ℕ =>
      ‖rationalCoefficients m * X ^ m.1 * Y ^ m.2‖) ∧
    (∑' m : ℕ × ℕ, rationalCoefficients m * X ^ m.1 * Y ^ m.2) *
      ((1 - 2 * X) * (1 - 3 * Y)) = X + Y := by
  have h2 : ‖(2 : ℂ) * X‖ < 1 := by
    rw [norm_mul]
    norm_num
    linarith
  have h3 : ‖(3 : ℂ) * Y‖ < 1 := by
    rw [norm_mul]
    norm_num
    linarith
  obtain ⟨hF, hFt⟩ := shifted_series 2 X h2
  obtain ⟨hG, hGt⟩ := geometric_series 3 Y h3
  obtain ⟨hH, hHt⟩ := geometric_series 2 X h2
  obtain ⟨hI, hIt⟩ := shifted_series 3 Y h3
  have hFG := hF.mul_norm hG
  have hHI := hH.mul_norm hI
  have hterm (m : ℕ × ℕ) :
      rationalCoefficients m * X ^ m.1 * Y ^ m.2 =
      (shifted 2 m.1 * X ^ m.1) * (3 ^ m.2 * Y ^ m.2) +
      (2 ^ m.1 * X ^ m.1) * (shifted 3 m.2 * Y ^ m.2) := by
    dsimp [rationalCoefficients, shifted]
    ring
  constructor
  · refine Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) (hFG.add hHI)
    rw [hterm]
    exact norm_add_le _ _
  · rw [tsum_congr hterm, hFG.of_norm.tsum_add hHI.of_norm,
      ← tsum_mul_tsum_of_summable_norm hF hG,
      ← tsum_mul_tsum_of_summable_norm hH hI]
    calc
      _ = ((∑' n, shifted 2 n * X ^ n) * (1 - 2 * X)) *
            ((∑' n, (3 : ℂ) ^ n * Y ^ n) * (1 - 3 * Y)) +
          ((∑' n, (2 : ℂ) ^ n * X ^ n) * (1 - 2 * X)) *
            ((∑' n, shifted 3 n * Y ^ n) * (1 - 3 * Y)) := by ring
      _ = X + Y := by rw [hFt, hGt, hHt, hIt]; ring

private theorem rational_row_formula (j : ℕ) (X : ℂ)
    (hX : ‖X‖ < 1 / 4) :
    (∑' m : ℕ, rationalCoefficients (m, j) * X ^ m) *
      (1 - 2 * X) = 3 ^ j * X + shifted 3 j := by
  have h2 : ‖(2 : ℂ) * X‖ < 1 := by
    rw [norm_mul]
    norm_num
    linarith
  obtain ⟨hF, hFt⟩ := shifted_series 2 X h2
  obtain ⟨hH, hHt⟩ := geometric_series 2 X h2
  have hterm (m : ℕ) : rationalCoefficients (m, j) * X ^ m =
      (shifted 2 m * X ^ m) * 3 ^ j +
        (2 ^ m * X ^ m) * shifted 3 j := by
    dsimp [rationalCoefficients, shifted]
    ring
  rw [tsum_congr hterm,
    (hF.of_norm.mul_right _).tsum_add (hH.of_norm.mul_right _),
    tsum_mul_right, tsum_mul_right]
  calc
    _ = ((∑' m, shifted 2 m * X ^ m) * (1 - 2 * X)) * 3 ^ j +
        ((∑' m, (2 : ℂ) ^ m * X ^ m) * (1 - 2 * X)) *
          shifted 3 j := by ring
    _ = 3 ^ j * X + shifted 3 j := by rw [hFt, hHt]; ring

/-- Symbolic row numerators and all-X continuation from one API radius. -/
public theorem rational_application :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      q 0 = Polynomial.X ∧
      (∀ j : ℕ, 0 < j →
        q j = Polynomial.C (3 ^ j) * Polynomial.X +
          Polynomial.C (3 ^ (j - 1))) ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < 1 / 4 →
        Summable (fun m : ℕ => ‖rationalCoefficients (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, rationalCoefficients (m, j) * X ^ m) *
          (1 - 2 * X) = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < R →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * (1 - 3 * Y) = X + Y) := by
  obtain ⟨q, R, hR, hrow, hcol⟩ :=
    MvPolynomial.exists_polynomial_rows rationalCoefficients
      (1 - 2 * Polynomial.X) (1 - 3 * Polynomial.X)
      (MvPolynomial.X 0 + MvPolynomial.X 1) (1 / 4)
      (by simp) (by norm_num) (by
        intro X Y hX hY
        simpa using rational_input X Y hX hY)
  have hq (j : ℕ) : q j = Polynomial.C (3 ^ j) * Polynomial.X +
      Polynomial.C (shifted 3 j) := by
    apply polynomial_eq_of_eval_disk _ _ (1 / 4) (by norm_num)
    intro X hX
    calc
      (q j).eval X =
          (∑' m : ℕ, rationalCoefficients (m, j) * X ^ m) *
            (1 - 2 * X) := by simpa using (hrow j X hX).2.symm
      _ = 3 ^ j * X + shifted 3 j := rational_row_formula j X hX
      _ = _ := by simp
  refine ⟨q, R, hR, ?_, ?_, ?_, ?_⟩
  · simpa [shifted] using hq 0
  · intro j hj
    simpa [shifted, hj] using hq j
  · intro j X hX
    simpa using hrow j X hX
  · intro X Y hY
    simpa using hcol X Y hY

/-- The very same returned radius works at -7 and 1000. -/
public theorem rational_large_coordinates :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      ∀ Y : ℂ, ‖Y‖ < R →
        (Summable (fun j : ℕ => ‖(q j).eval (-7) * Y ^ j‖) ∧
          (∑' j : ℕ, (q j).eval (-7) * Y ^ j) * (1 - 3 * Y) = -7 + Y) ∧
        (Summable (fun j : ℕ => ‖(q j).eval 1000 * Y ^ j‖) ∧
          (∑' j : ℕ, (q j).eval 1000 * Y ^ j) * (1 - 3 * Y) = 1000 + Y) := by
  obtain ⟨q, R, hR, -, -, -, h⟩ := rational_application
  exact ⟨q, R, hR, fun Y hY => ⟨h (-7) Y hY, h 1000 Y hY⟩⟩

/-- Finite support in the first variable, with every second-variable row. -/
@[expose] public def vanishingCoefficients (m : ℕ × ℕ) : ℂ :=
  if m.1 = 0 ∨ m.1 = 2 then 1 else 0

private theorem vanishing_row_series (X : ℂ) :
    Summable (fun m : ℕ => ‖vanishingCoefficients (m, 0) * X ^ m‖) ∧
    HasSum (fun m : ℕ => vanishingCoefficients (m, 0) * X ^ m)
      (1 + X ^ 2) := by
  have hz (m : ℕ) (hm : m ∉ ({0, 2} : Finset ℕ)) :
      vanishingCoefficients (m, 0) * X ^ m = 0 := by
    simp only [mem_insert, mem_singleton] at hm
    simp [vanishingCoefficients, hm]
  refine ⟨summable_of_ne_finset_zero (s := {0, 2})
    (fun m hm => by rw [hz m hm, norm_zero]), ?_⟩
  simpa [vanishingCoefficients] using
    hasSum_sum_of_ne_finset_zero (s := {0, 2}) hz

/-- A nonzero numerator with a first denominator vanishing at zero. -/
public theorem vanishing_input (X Y : ℂ) (hY : ‖Y‖ < 1 / 2) :
    Summable (fun m : ℕ × ℕ =>
      ‖vanishingCoefficients m * X ^ m.1 * Y ^ m.2‖) ∧
    (∑' m : ℕ × ℕ, vanishingCoefficients m * X ^ m.1 * Y ^ m.2) =
      (1 + X ^ 2) / (1 - Y) ∧
    (∑' m : ℕ × ℕ, vanishingCoefficients m * X ^ m.1 * Y ^ m.2) *
      (X * (1 - Y)) = X + X ^ 3 := by
  have hY1 : ‖Y‖ < 1 := by linarith
  obtain ⟨hF, hFt⟩ := vanishing_row_series X
  have hG := summable_norm_geometric_of_norm_lt_one hY1
  have ht : (∑' m : ℕ × ℕ,
      vanishingCoefficients m * X ^ m.1 * Y ^ m.2) =
      (1 + X ^ 2) * (1 - Y)⁻¹ := by
    change (∑' m : ℕ × ℕ,
      vanishingCoefficients (m.1, 0) * X ^ m.1 * Y ^ m.2) = _
    rw [← tsum_mul_tsum_of_summable_norm hF hG, hFt.tsum_eq,
      tsum_geometric_of_norm_lt_one hY1]
  refine ⟨hF.mul_norm hG, ?_, ?_⟩
  · simpa only [div_eq_mul_inv] using ht
  · have hne : 1 - Y ≠ 0 := by
      intro h0
      have heq := (sub_eq_zero.mp h0).symm
      simp [heq] at hY1
    rw [ht]
    calc
      _ = ((1 + X ^ 2) * X) * ((1 - Y)⁻¹ * (1 - Y)) := by ring
      _ = X + X ^ 3 := by rw [inv_mul_cancel₀ hne]; ring

/-- The row API admits D1=X and determines every numerator symbolically. -/
public theorem vanishing_application :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      (∀ j : ℕ, q j = Polynomial.X + Polynomial.X ^ 3) ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < 1 / 2 →
        Summable (fun m : ℕ => ‖vanishingCoefficients (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, vanishingCoefficients (m, j) * X ^ m) * X =
          (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < R →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * (1 - Y) = X + X ^ 3) := by
  obtain ⟨q, R, hR, hrow, hcol⟩ :=
    MvPolynomial.exists_polynomial_rows vanishingCoefficients
      Polynomial.X (1 - Polynomial.X)
      (MvPolynomial.X 0 + MvPolynomial.X 0 ^ 3) (1 / 2)
      (by simp) (by norm_num) (by
        intro X Y _ hY
        have hv := vanishing_input X Y hY
        exact ⟨hv.1, by simpa using hv.2.2⟩)
  refine ⟨q, R, hR, ?_, ?_, ?_⟩
  · intro j
    apply polynomial_eq_of_eval_disk _ _ (1 / 2) (by norm_num)
    intro X hX
    calc
      (q j).eval X =
          (∑' m : ℕ, vanishingCoefficients (m, j) * X ^ m) * X := by
            simpa using (hrow j X hX).2.symm
      _ = (1 + X ^ 2) * X := by
          congr 1
          exact (vanishing_row_series X).2.tsum_eq
      _ = _ := by simp; ring
  · intro j X hX
    simpa using hrow j X hX
  · intro X Y hY
    simpa using hcol X Y hY

/-- One radius from the API handles both zero and a large first coordinate. -/
public theorem vanishing_large_coordinates :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      (∀ j : ℕ, q j = Polynomial.X + Polynomial.X ^ 3) ∧
      ∀ Y : ℂ, ‖Y‖ < R →
        (Summable (fun j : ℕ => ‖(q j).eval 0 * Y ^ j‖) ∧
          (∑' j : ℕ, (q j).eval 0 * Y ^ j) * (1 - Y) = 0) ∧
        (Summable (fun j : ℕ => ‖(q j).eval 1000 * Y ^ j‖) ∧
          (∑' j : ℕ, (q j).eval 1000 * Y ^ j) * (1 - Y) =
            1000 + (1000 : ℂ) ^ 3) := by
  obtain ⟨q, R, hR, hq, -, h⟩ := vanishing_application
  refine ⟨q, R, hR, hq, fun Y hY => ⟨?_, h 1000 Y hY⟩⟩
  simpa using h 0 Y hY

/-- The vanishing-at-zero denominator and numerator are both nonzero. -/
public theorem vanishing_denominator_boundary :
    (Polynomial.X : Polynomial ℂ) ≠ 0 ∧
      (Polynomial.X : Polynomial ℂ).eval 0 = 0 ∧
      (MvPolynomial.X 0 + MvPolynomial.X 0 ^ 3 :
        MvPolynomial (Fin 2) ℂ) ≠ 0 := by
  refine ⟨Polynomial.X_ne_zero, by simp, ?_⟩
  intro h
  have he := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) h
  norm_num at he

/-- A genuinely finite-support input for the identically zero denominator. -/
@[expose] public def finiteCoefficients (m : ℕ × ℕ) : ℂ :=
  if m = (0, 0) then 1 else 0

/-- No nonzero or nonvanishing premise on D1 is needed, even when D1=0. -/
public theorem zero_first_denominator :
    ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      (∀ j : ℕ, q j = 0) ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < 1 →
        Summable (fun m : ℕ => ‖finiteCoefficients (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, finiteCoefficients (m, j) * X ^ m) * 0 =
          (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < R →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * 1 = 0) := by
  obtain ⟨q, R, hR, hrow, hcol⟩ :=
    MvPolynomial.exists_polynomial_rows finiteCoefficients 0 1 0 1
      (by simp) (by norm_num) (by
        intro X Y _ _
        refine ⟨summable_of_ne_finset_zero (s := {(0, 0)})
          (fun m hm => ?_), by simp⟩
        simp only [mem_singleton] at hm
        simp [finiteCoefficients, hm])
  refine ⟨q, R, hR, ?_, ?_, ?_⟩
  · intro j
    apply polynomial_eq_of_eval_disk _ _ 1 zero_lt_one
    intro X hX
    simpa using (hrow j X hX).2.symm
  · simpa using hrow
  · simpa using hcol

private theorem geometric_not_polynomial :
    ¬ ∃ p : Polynomial ℂ, ∀ X : ℂ, ‖X‖ < 1 / 2 →
      (∑' m : ℕ, X ^ m) = p.eval X := by
  rintro ⟨p, hp⟩
  have hc : (fun _ : ℕ => (1 : ℂ)) = p.coeff :=
    scalar_coefficients_unique _ _ (1 / 2) (by norm_num)
      (fun X => p.eval X) (by
        intro X hX
        rw [← hp X hX]
        have hs := hasSum_geometric_of_norm_lt_one
          (show ‖X‖ < 1 by linarith)
        simpa only [one_mul] using hs.summable.hasSum)
      (fun X _ => polynomial_hasSum p X)
  have hz : p.coeff (p.support.sup id + 1) = 0 := by
    apply Polynomial.notMem_support_iff.mp
    intro hn
    have hle := Finset.le_sup (f := id) hn
    change p.support.sup id + 1 ≤ p.support.sup id at hle
    omega
  exact one_ne_zero ((congrFun hc (p.support.sup id + 1)).trans hz)

/-- Without D2(0) nonzero, the geometric first row need not be polynomial. -/
@[expose] public def missingDenominatorCoefficients (m : ℕ × ℕ) : ℂ :=
  if m.2 = 0 then 1 else 0

/-- The counterexample meets every input clause except D2(0) nonzero. -/
public theorem missing_denominator_input (X Y : ℂ)
    (hX : ‖X‖ < 1 / 2) (_hY : ‖Y‖ < 1 / 2) :
    Summable (fun m : ℕ × ℕ =>
      ‖missingDenominatorCoefficients m * X ^ m.1 * Y ^ m.2‖) ∧
    (∑' m : ℕ × ℕ,
      missingDenominatorCoefficients m * X ^ m.1 * Y ^ m.2) *
        ((1 : Polynomial ℂ).eval X * (0 : Polynomial ℂ).eval Y) =
          MvPolynomial.eval ![X, Y] (0 : MvPolynomial (Fin 2) ℂ) := by
  have hF := summable_norm_geometric_of_norm_lt_one
    (show ‖X‖ < 1 by linarith)
  have hG : Summable (fun k : ℕ =>
      ‖(if k = 0 then (1 : ℂ) else 0) * Y ^ k‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [mem_singleton] at hk
    simp [hk]
  have hterm (m : ℕ × ℕ) :
      X ^ m.1 * ((if m.2 = 0 then (1 : ℂ) else 0) * Y ^ m.2) =
      missingDenominatorCoefficients m * X ^ m.1 * Y ^ m.2 := by
    dsimp [missingDenominatorCoefficients]
    ring
  exact ⟨(hF.mul_norm hG).congr (fun m => congrArg norm (hterm m)),
    by simp⟩

/-- Dropping D2(0) nonzero makes the full row conclusion false. -/
public theorem missing_second_denominator :
    ¬ ∃ (q : ℕ → Polynomial ℂ) (R : ℝ), 0 < R ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < 1 / 2 →
        Summable (fun m : ℕ =>
          ‖missingDenominatorCoefficients (m, j) * X ^ m‖) ∧
        (∑' m : ℕ, missingDenominatorCoefficients (m, j) * X ^ m) *
          (1 : Polynomial ℂ).eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < R →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * (0 : Polynomial ℂ).eval Y =
          MvPolynomial.eval ![X, Y] (0 : MvPolynomial (Fin 2) ℂ)) := by
  rintro ⟨q, _, _, hrow, _⟩
  apply geometric_not_polynomial
  refine ⟨q 0, fun X hX => ?_⟩
  simpa [missingDenominatorCoefficients] using (hrow 0 X hX).2

/-- Geometrically growing coefficients for the norm-summability boundary. -/
@[expose] public def growingCoefficients (m : ℕ × ℕ) : ℂ :=
  if m.2 = 0 then 2 ^ m.1 else 0

/-- With D1=0 and D2=1 the cross identity alone cannot ensure summability. -/
public theorem norm_summability_boundary :
    (∀ X Y : ℂ,
      (∑' m : ℕ × ℕ, growingCoefficients m * X ^ m.1 * Y ^ m.2) *
        ((0 : Polynomial ℂ).eval X * (1 : Polynomial ℂ).eval Y) =
          MvPolynomial.eval ![X, Y] (0 : MvPolynomial (Fin 2) ℂ)) ∧
    ‖(1 / 2 : ℂ)‖ < 1 ∧ ‖(0 : ℂ)‖ < 1 ∧
    ¬ Summable (fun m : ℕ × ℕ =>
      ‖growingCoefficients m * (1 / 2 : ℂ) ^ m.1 * (0 : ℂ) ^ m.2‖) := by
  refine ⟨by simp, by norm_num, by norm_num, ?_⟩
  intro hs
  have hh := hs.comp_injective
    (show Function.Injective (fun n : ℕ => (n, (0 : ℕ))) from
      fun _ _ h => congrArg Prod.fst h)
  have hterm (n : ℕ) :
      ‖growingCoefficients (n, 0) * (1 / 2 : ℂ) ^ n * (0 : ℂ) ^ 0‖ =
      (1 : ℝ) := by
    norm_num [growingCoefficients, ← mul_pow]
  have hs1 : Summable (fun _ : ℕ => (1 : ℝ)) := hh.congr hterm
  have he : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs1.tendsto_atTop_zero
  exact one_ne_zero he

/-- The large-coordinate tests are strictly outside both original bidisks. -/
public theorem large_coordinates_outside_input_disks :
    (1 / 2 : ℝ) < ‖(-7 : ℂ)‖ ∧ (1 / 2 : ℝ) < ‖(1000 : ℂ)‖ := by
  norm_num

end BivariateRowsTest
