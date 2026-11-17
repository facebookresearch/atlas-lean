/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Degree
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the degree in the Selberg class

`FunctionalEquation.mul`, `mul_mem` and `FunctionalEquation.degree_eq_add_of_mul` at `1 · ζ` and
`ζ · ζ`.
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

/-! ### The functional equation of a product -/

/-- `FunctionalEquation.mul` concatenates the Gamma factors: `ζ²` has two, both `Γ(s/2)`. -/
example : (zetaFE.mul zetaFE).d = 2 ∧ (zetaFE.mul zetaFE).w = 1 ∧
    (zetaFE.mul zetaFE).Q = Real.pi ^ (-(1 / 2 : ℝ)) * Real.pi ^ (-(1 / 2 : ℝ)) ∧
    ∀ i, (zetaFE.mul zetaFE).α i = 1 / 2 ∧ (zetaFE.mul zetaFE).r i = 0 := by
  refine ⟨rfl, by simp [FunctionalEquation.mul, zetaFE, FunctionalEquation.riemannZeta], rfl,
    fun i => ?_⟩
  induction i using Fin.addCases with
  | left j => exact ⟨Fin.append_left _ _ j, Fin.append_left _ _ j⟩
  | right j => exact ⟨Fin.append_right _ _ j, Fin.append_right _ _ j⟩

/-- The degree of `ζ²` is `2`. -/
example : (zetaFE.mul zetaFE).degree = 2 := by
  rw [FunctionalEquation.degree_mul, zetaFE_degree]; norm_num

/-- Multiplying by the trivial functional equation of `1` keeps the degree. -/
example : (oneFE.mul zetaFE).degree = zetaFE.degree := by
  rw [FunctionalEquation.degree_mul, oneFE_degree, zero_add]

/-! ### Closure under products -/

/-- `ζ · ζ` (coefficients `d(n)`, the divisor function) is in the Selberg class. -/
example : zetaC * zetaC ∈ selbergClass := mul_mem zeta_mem_selbergClass zeta_mem_selbergClass

/-- `ζ³ ∈ 𝒮`. -/
example : zetaC ^ 3 ∈ selbergClass := by
  rw [pow_succ, pow_two]
  exact mul_mem (mul_mem zeta_mem_selbergClass zeta_mem_selbergClass) zeta_mem_selbergClass

/-- `1 · a = a`: multiplying by `1 ∈ 𝒮` stays in `𝒮`, and gives back `a`. -/
example {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass) : 1 * a ∈ selbergClass ∧ 1 * a = a :=
  ⟨mul_mem one_mem_selbergClass ha, one_mul a⟩

theorem isLSeriesContinuation_zeta_mul_zeta :
    IsLSeriesContinuation (zetaC * zetaC) (fun s => riemannZeta s * riemannZeta s) := by
  refine ⟨fun s hs => ?_, isLSeriesContinuation_zeta.2.mul isLSeriesContinuation_zeta.2⟩
  change riemannZeta s * riemannZeta s = _
  rw [isLSeriesContinuation_zeta.1 s hs, ArithmeticFunction.LSeries_mul'
    (LSeriesSummable_of_mem zeta_mem_selbergClass hs)
    (LSeriesSummable_of_mem zeta_mem_selbergClass hs)]

/-- Every functional equation of `ζ²` has degree `2`. -/
example (D : FunctionalEquation fun s => riemannZeta s * riemannZeta s) : D.degree = 2 := by
  rw [FunctionalEquation.degree_eq_add_of_mul zetaC zetaC zeta_mem_selbergClass
    zeta_mem_selbergClass _ _ _ isLSeriesContinuation_zeta isLSeriesContinuation_zeta
    isLSeriesContinuation_zeta_mul_zeta zetaFE zetaFE D, zetaFE_degree]
  norm_num

/-! ### Additivity of the degree -/

theorem isLSeriesContinuation_one_mul_zeta :
    IsLSeriesContinuation (1 * zetaC) riemannZeta := by
  rw [one_mul]; exact isLSeriesContinuation_zeta

/-- `deg ζ = deg 1 + deg ζ`, i.e. `1 = 0 + 1`. -/
example : zetaFE.degree = oneFE.degree + zetaFE.degree :=
  FunctionalEquation.degree_eq_add_of_mul 1 zetaC one_mem_selbergClass zeta_mem_selbergClass
    _ _ _ isLSeriesContinuation_one isLSeriesContinuation_zeta
    isLSeriesContinuation_one_mul_zeta oneFE zetaFE zetaFE

/-- Additivity forces every functional equation of `ζ` to have degree `1`. -/
example (D : FunctionalEquation riemannZeta) : D.degree = 1 := by
  have := FunctionalEquation.degree_eq_add_of_mul 1 zetaC one_mem_selbergClass
    zeta_mem_selbergClass _ _ _ isLSeriesContinuation_one isLSeriesContinuation_zeta
    isLSeriesContinuation_one_mul_zeta oneFE zetaFE D
  rw [oneFE_degree, zetaFE_degree, zero_add] at this
  exact this

end SelbergClassTest
