/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.NielsenBound

/-!
# Tests for Nielsen's bound
-/

open MetaMathlibExt

-- With a single denominator the strict prefix condition is just 2/3 < 1.
example (u : ℕ) (hu : 1 < u) (h : 1 - 1 / (u : ℚ) ≤ 2 / 3) : u ≤ 3 := by
  have bound := nielsen_prod_one_sub_inv_bound 1 2 3 (fun _ => u) monotone_const
    (fun _ => hu) (by simpa using h) (by norm_num [Finset.prod_filter])
  norm_num at bound
  omega

-- For the denominators 3 and 4, the full product is exactly 1/2 and the bound is sharp.
example : (∏ i : Fin 2, (i.val + 3)) ≤ 12 := by
  rw [← Nat.one_mul (∏ i : Fin 2, (i.val + 3))]
  exact nielsen_prod_one_sub_inv_bound 2 1 2 (fun i => i.val + 3)
    (fun _ _ hij => Nat.add_le_add_right hij 3) (by decide)
    (by norm_num [Fin.prod_univ_two]) (by norm_num [Finset.prod_filter, Fin.prod_univ_two])
