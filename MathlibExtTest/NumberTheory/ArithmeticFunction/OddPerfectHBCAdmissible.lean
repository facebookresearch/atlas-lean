/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible
import Mathlib.Tactic.NormNum

/-!
# Tests of Stone's square-root product bound

Apply the product bound to the HBC-admissible tuple $(3, 4)$ at $1/2$.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible

example : (3 : ℝ) * 4 ≤ 2 ^ 4 - 2 ^ 2 := by
  have h := MetaMathlibExt.hbcAdmissible_prod_le_sqrt 1 1 2
    (by decide) (by decide) (by decide) (by decide) (fun i => i + 2)
    (by decide) (fun i _ _ => by omega)
    (by norm_num [Finset.prod_Icc_succ_top])
    (by norm_num)
  convert h using 1 <;> norm_num [Finset.prod_Icc_succ_top]

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectHBCAdmissible
