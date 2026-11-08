/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.BigOperators.ProdCompPow
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for `Fintype.prod_comp_eq_prod_pow`

The labels `true, true, false` regrouped by value, in general and for `f true = 2`,
`f false = 3`: the product `2 * 2 * 3 = 3 ^ 1 * 2 ^ 2 = 12`.
-/

namespace MathlibExtTest.ProdCompPow

example (f : Bool → ℕ) :
    ∏ k : Fin 3, f (![true, true, false] k) =
      ∏ c : Bool, f c ^ (Finset.univ.filter fun k => ![true, true, false] k = c).card :=
  Fintype.prod_comp_eq_prod_pow _ f

example : ∏ k : Fin 3, (fun b : Bool => if b then 2 else 3) (![true, true, false] k) = 12 := by
  rw [Fintype.prod_comp_eq_prod_pow (![true, true, false] : Fin 3 → Bool)
    (fun b : Bool => if b then (2 : ℕ) else 3)]
  decide

end MathlibExtTest.ProdCompPow
