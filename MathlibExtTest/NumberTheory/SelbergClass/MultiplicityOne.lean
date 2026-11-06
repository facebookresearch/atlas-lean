/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.MultiplicityOne
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for strong multiplicity one in the Selberg class
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

/-- The zero hypothesis is met (trivially) when `F = G`. -/
example : zetaC = zetaC :=
  eq_of_isLittleO_sum_abs_sub_analyticOrderNatAt zetaC zetaC zeta_mem_selbergClass
    zeta_mem_selbergClass riemannZeta riemannZeta isLSeriesContinuation_zeta
    isLSeriesContinuation_zeta (by simp)

/-- `1` and `ζ` differ, so their zeros differ by more than `o(T)`. -/
example : ¬ (fun T : ℝ => ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ |ρ.im| ≤ T ∧
      ((fun _ => (1 : ℂ)) ρ = 0 ∨ riemannZeta ρ = 0)},
      |(analyticOrderNatAt (fun _ => (1 : ℂ)) ρ : ℝ) - analyticOrderNatAt riemannZeta ρ|)
      =o[Filter.atTop] (fun T : ℝ => T) := fun h =>
  zetaC_ne_one (eq_of_isLittleO_sum_abs_sub_analyticOrderNatAt 1 zetaC one_mem_selbergClass
    zeta_mem_selbergClass _ _ isLSeriesContinuation_one isLSeriesContinuation_zeta h).symm

end SelbergClassTest
