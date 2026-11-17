/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.DegreeBound
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the degree bound `0 < d → 1 ≤ d`
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

example : 1 ≤ zetaFE.degree :=
  one_le_degree_of_pos zetaC zeta_mem_selbergClass riemannZeta isLSeriesContinuation_zeta zetaFE
    (by rw [zetaFE_degree]; norm_num)

end SelbergClassTest
