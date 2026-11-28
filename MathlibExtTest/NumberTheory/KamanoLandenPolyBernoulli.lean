/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KamanoLandenPolyBernoulli

/-! # Tests for `MathlibExt.NumberTheory.KamanoLandenPolyBernoulli` -/

namespace MathlibExtTest.KamanoLandenPolyBernoulli

open MetaMathlibExt PowerSeries

/-- The Landen data of the example in the docstring of `generalizedPolyBernoulliC_landen`:
`s = 1`, `g₀` with rows `(1, -1)` and `(1, 0)`, and `g₁` the identity matrix. -/
noncomputable abbrev exampleData : LandenData := ⟨1, 1, 0, ![1], ![0], ![0], ![1]⟩

/-- The transformed data `exampleData.tilde`, with the field expressions of `LandenData.tilde`:
`g̃₀` has rows `(1, -1)` and `(0, -1)`, and `g̃₁` has rows `(1, 0)` and `(1, -1)`. -/
noncomputable abbrev exampleTilde : LandenData :=
  ⟨1, -0, -1, ![1], ![0], fun i => (1 - 0) * ![1] i - ![0] i, fun i => (1 - 0) * ![0] i - ![1] i⟩

example : exampleData.tilde = exampleTilde := rfl

-- The hypothesis of the Landen formula holds for the example: `g₁` is invertible.
example : ∀ i, exampleData.a i * exampleData.d i - exampleData.b i * exampleData.c i ≠ 0 := by
  intro i
  fin_cases i
  simp

-- The transformed data: `g̃₀` has bottom row `(-d₀, -c₀) = (0, -1)`, and `g̃` is `g` again after a
-- second transformation.
example : exampleData.tilde.c₀ = 0 ∧ exampleData.tilde.d₀ = -1 := by
  simp [LandenData.tilde]

example : exampleData.tilde.tilde = exampleData := LandenData.tilde_tilde _

private theorem modifyLast_one : [1].modifyLast (· + 1) = [2] := by
  simp [List.modifyLast, List.modifyLast.go]

/-- The constant term of `d/dt F(z(t))` is `F'(0) z'(0)`. -/
private theorem coeff_zero_derivative_subst {f z : ℝ⟦X⟧} (hz : constantCoeff z = 0) :
    coeff 0 (derivative (subst z f)) = coeff 1 f * coeff 1 z := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hz), coeff_zero_eq_constantCoeff_apply,
    map_mul]
  have h := constantCoeff_subst_of_constantCoeff_zero (a := z) (S := ℝ) hz (derivative f)
  rw [show constantCoeff (subst z (derivative f)) = constantCoeff (derivative f) from
    h.trans (by simp)]
  simp [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]

private theorem constantCoeff_landenExpVariable (D : LandenData) :
    constantCoeff (landenExpVariable D) = 0 := by
  simp [landenExpVariable]

-- The variable of `g` is `z(t) = (eᵗ - 1) / eᵗ = t + O(t²)`.
private theorem coeff_one_landenExpVariable : coeff 1 (landenExpVariable exampleData) = 1 := by
  have h := congrArg (coeff 1) (landenExpVariable_spec exampleData (by simp))
  have h0 := constantCoeff_landenExpVariable exampleData
  set z := landenExpVariable exampleData
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp [Finset.sum_range_succ, coeff_exp, h0] at h
  exact h

-- The variable of `g̃` is `(eᵗ - 1) / (-1) = -t + O(t²)`.
private theorem coeff_one_landenExpVariable_tilde :
    coeff 1 (landenExpVariable exampleTilde) = -1 := by
  have h := congrArg (coeff 1) (landenExpVariable_spec exampleTilde (by simp))
  set z := landenExpVariable exampleTilde
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp [coeff_exp] at h
  linarith

-- `Li_{(2)}(g; z) = Σ zᵐ / m²` here; its coefficient of `z` is `1`.
private theorem coeff_one_polylog :
    coeff 1 (generalizedMultiplePolylog exampleData ![1] ![1] [2]) = 1 := by
  have hΦ : exampleData.formSeries ![1] = 1 := by
    simp [LandenData.formSeries, landenFormSeries_identity]
  rw [generalizedMultiplePolylog, List.reverse_singleton, LandenData.polylogRev.eq_5, hΦ,
    one_mul, LandenData.polylogRev.eq_3]
  simp [integralDivX, landenFormSeries, linearFractionalPoleSeries]

-- For the transformed data the coefficient of `z` in `Li_{(2)}(g̃; z)` is `-1`.
private theorem coeff_one_polylog_tilde :
    coeff 1 (generalizedMultiplePolylog exampleTilde ![1] ![1] [2]) = -1 := by
  rw [generalizedMultiplePolylog, List.reverse_singleton, LandenData.polylogRev.eq_5,
    LandenData.polylogRev.eq_3, integralDivX, coeff_mk, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, LandenData.formSeries, integralDivX, landenFormSeries,
    linearFractionalPoleSeries]

-- The statement is not degenerate: `C₀ = 1` for the example (`k = (1)`, so `k↑ = (2)`).
example : generalizedPolyBernoulliC exampleData ![1] ![1] [1] 0 = 1 := by
  rw [generalizedPolyBernoulliC, modifyLast_one,
    coeff_zero_derivative_subst (constantCoeff_landenExpVariable _), coeff_one_polylog,
    coeff_one_landenExpVariable]
  simp

-- The right-hand side of the Landen formula, computed directly for the example with `n = 0`:
-- `Li_{(2)}(g̃; ·)` evaluated at the variable `z(t)` of `g` has `d/dt` with constant term `-1`,
-- and `(-1)^{0+1} · 0! · (-1) = 1 = C₀`.
example : coeff 0 (derivative (subst (landenExpVariable exampleData)
    (generalizedMultiplePolylog exampleData.tilde ![1] ![1] [2]))) = -1 := by
  rw [coeff_zero_derivative_subst (constantCoeff_landenExpVariable _)]
  change coeff 1 (generalizedMultiplePolylog exampleTilde ![1] ![1] [2]) * _ = _
  rw [coeff_one_polylog_tilde, coeff_one_landenExpVariable]
  ring

-- The Landen formula applied to the example data, the index `k = (1)` and `n = 0`.
example : generalizedPolyBernoulliC exampleData ![1] ![1] [1] 0 =
    (-1 : ℝ) ^ (0 + 1) * ((0 : ℕ).factorial * coeff 0 (derivative (subst
      (landenExpVariable exampleData) (generalizedMultiplePolylog exampleData.tilde ![1] ![1]
        ([1].modifyLast (· + 1)))))) :=
  generalizedPolyBernoulliC_landen exampleData (by intro i; fin_cases i; simp) ![1] ![1]
    (Composition.single 1 Nat.one_pos) 0

-- Why the transformed data is evaluated at the variable of `g`: with its own variable
-- `(eᵗ - 1) / (-d₀ eᵗ - c₀)`, the transformed data gives the same `C₀ = 1` as `g`, so the
-- identity printed in the source, `C₀ = (-1)^{0-1} C₀(g̃)`, would read `1 = -1`.
example : generalizedPolyBernoulliC exampleData.tilde ![1] ![1] [1] 0 = 1 := by
  change generalizedPolyBernoulliC exampleTilde ![1] ![1] [1] 0 = 1
  rw [generalizedPolyBernoulliC, modifyLast_one,
    coeff_zero_derivative_subst (constantCoeff_landenExpVariable _), coeff_one_polylog_tilde,
    coeff_one_landenExpVariable_tilde]
  simp

-- Edge case: for the empty index `k↑` is empty, `Li_{()} = 0`, and every `Cₙ` vanishes.
example (D : LandenData) (β γ : Fin D.s → ℝ) (n : ℕ) :
    generalizedPolyBernoulliC D β γ [] n = 0 := by
  have hz := HasSubst.of_constantCoeff_zero' (constantCoeff_landenExpVariable D)
  rw [generalizedPolyBernoulliC, show ([] : List ℕ).modifyLast (· + 1) = [] from rfl,
    generalizedMultiplePolylog, List.reverse_nil, LandenData.polylogRev.eq_1,
    ← coe_substAlgHom hz, map_zero, map_zero, map_zero, mul_zero]

-- Junk value: when `c₀ + d₀ = 0` the variable `z(t)` is the zero series.
example (D : LandenData) (h : D.c₀ + D.d₀ = 0) : landenExpVariable D = 0 := by
  rw [landenExpVariable, PowerSeries.inv_eq_zero.mpr (by simpa using h), mul_zero]

private noncomputable abbrev classicalExampleData : LandenData :=
  ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩

-- The weight-zero composition gives the zero series, for arbitrary weights.
example (β₁ β₂ γ₁ γ₂ : ℝ) :
    subst (-(X * mk fun _ => (1 : ℝ)))
      (generalizedMultiplePolylog classicalExampleData ![β₁, β₂] ![γ₁, γ₂] []) = 0 := by
  simpa only [Composition.ones_blocks, List.replicate_zero, generalizedMultiplePolylog,
    List.reverse_nil, LandenData.polylogRev.eq_1, neg_zero] using
    generalizedMultiplePolylog_landen_connection_classical β₁ β₂ γ₁ γ₂ (Composition.ones 0)

private def twoOne : Composition 3 := ⟨[2, 1], by simp, by decide⟩

private theorem classicalExampleData_formSeries (a b : ℝ) :
    classicalExampleData.formSeries ![a, b] = C a + C b * landenFormSeries 1 (-1) 1 0 := by
  rw [LandenData.formSeries, Fin.sum_univ_two]
  simp [landenFormSeries_identity]

-- The index `(2, 1)` uses both the β and γ recursions. For these weights the
-- transformed forms are `1 - P` and `1 + P`, where `P = z / (1 - z)`.
example : coeff 2 (subst (-(X * mk fun _ => (1 : ℝ)))
    (generalizedMultiplePolylog classicalExampleData ![1, 2] ![1, 0] twoOne.blocks)) = -(3 / 8) := by
  rw [generalizedMultiplePolylog_landen_connection_classical 1 2 1 0 twoOne]
  rw [show twoOne.blocks = [2, 1] from rfl, generalizedMultiplePolylog,
    show ([2, 1] : List ℕ).reverse = [1, 2] from rfl, LandenData.polylogRev.eq_4,
    LandenData.polylogRev.eq_5, LandenData.polylogRev.eq_3, map_neg]
  simp only [classicalExampleData_formSeries]
  norm_num [classicalExampleData, landenFormSeries, linearFractionalPoleSeries, integralDivX,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]

end MathlibExtTest.KamanoLandenPolyBernoulli
