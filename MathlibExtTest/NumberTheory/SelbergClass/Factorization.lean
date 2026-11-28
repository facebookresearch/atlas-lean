/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Factorization
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the degree bounds and factorization into primitives
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

example : 0 ≤ zetaFE.degree := zetaFE.degree_nonneg

example : 1 ≤ zetaFE.degree :=
  one_le_degree_of_ne_one zeta_mem_selbergClass zetaC_ne_one isLSeriesContinuation_zeta zetaFE

/-- The hypothesis `b ≠ 1` of `one_le_degree_of_ne_one` is needed: `deg 1 = 0`. -/
example : ¬ 1 ≤ oneFE.degree := by
  unfold FunctionalEquation.degree
  rw [Finset.sum_eq_zero fun i _ => i.elim0, mul_zero]
  norm_num

example : ∃ l : Multiset (ArithmeticFunction ℂ), (∀ g ∈ l, IsSelbergPrimitive g) ∧
    l.prod = zetaC :=
  exists_multiset_prod_eq zeta_mem_selbergClass zetaC_ne_one

end SelbergClassTest
