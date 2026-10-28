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

`mul_mem_of_functionalEquation` and `FunctionalEquation.degree_eq_add_of_mul` at `1 · ζ`.
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

theorem isLSeriesContinuation_one_mul_zeta :
    IsLSeriesContinuation (1 * zetaC) riemannZeta := by
  rw [one_mul]; exact isLSeriesContinuation_zeta

example : 1 * zetaC ∈ selbergClass :=
  mul_mem_of_functionalEquation one_mem_selbergClass zeta_mem_selbergClass
    isLSeriesContinuation_one isLSeriesContinuation_zeta isLSeriesContinuation_one_mul_zeta zetaFE

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
  have h0 : oneFE.degree = 0 := by
    unfold FunctionalEquation.degree
    rw [Finset.sum_eq_zero fun i _ => i.elim0, mul_zero]
  rw [h0, zetaFE_degree, zero_add] at this
  exact this

end SelbergClassTest
