/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Polynomial.PairwiseSumResultant

namespace MetaMathlibExt

open Polynomial

/-- Three equal roots give a cubed factor and an odd resultant sign. -/
example (a b : ℚ) :
    (1 - C (a + b) * X) ^ 3 =
      -resultant (1 - X - C (C a * X)) ((X - C (C b * X)) ^ 3) 1 3 := by
  simpa [resultant, Finset.prod_const, pow_succ] using
    prod_one_sub_add_eq_resultant 1 3 (fun _ ↦ a) (fun _ ↦ b)

/-- An empty first family gives the unit polynomial for every second family. -/
example (n : ℕ) (β : Fin n → ℚ) :
    1 = resultant 1 (∏ j, (X - C (C (β j) * X))) 0 n := by
  simpa only [resultant, Finset.prod_of_isEmpty, Nat.zero_mul, pow_zero, one_mul] using
    prod_one_sub_add_eq_resultant 0 n Fin.elim0 β

end MetaMathlibExt
