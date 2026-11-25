/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciCompositionSum
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open scoped BigOperators

-- The least shift and offset, where the prefactor uses a negative integer power.
example :
    (1 / ((3 : ℂ) ^ (-1 : ℤ) * 3)) *
      (∑ c : Composition 1, (-1 : ℂ) ^ (1 - c.length) *
        ∏ i : Fin c.length, ((c.blocksFun i : ℂ) + 2)) = 3 := by
  have h := gibonacci_add_eq_composition_sum 0 1 (by decide) (by decide)
    (Or.inr (by decide)) 3 (by decide) 1 (by norm_num) 1 (by decide)
  norm_num [gibonacciNumber] at h ⊢
  exact h.symm

-- The other square root, at an offset where the part of size two has weight zero.
example :
    (25 / (3 : ℂ)) *
      (∑ c : Composition 3, (-1 / 5 : ℂ) ^ (3 - c.length) *
        ∏ i : Fin c.length, (2 - (c.blocksFun i : ℂ))) = 8 := by
  have h := gibonacci_add_eq_composition_sum 0 1 (by decide) (by decide)
    (Or.inr (by decide)) 3 (by decide) (-1) (by norm_num) 3 (by decide)
  norm_num [gibonacciNumber, sub_eq_add_neg, add_comm] at h ⊢
  exact h.symm

end MetaMathlibExt
