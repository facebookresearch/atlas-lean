/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.DegreeZero
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for degree-zero members of the Selberg class
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

example : (1 : ArithmeticFunction ℂ) = 1 :=
  eq_one_of_degree_eq_zero one_mem_selbergClass isLSeriesContinuation_one oneFE oneFE_degree

/-- `ζ` has no functional equation of degree `0`. -/
example (D : FunctionalEquation riemannZeta) : D.degree ≠ 0 := fun h =>
  zetaC_ne_one (eq_one_of_degree_eq_zero zeta_mem_selbergClass isLSeriesContinuation_zeta D h)

end SelbergClassTest
