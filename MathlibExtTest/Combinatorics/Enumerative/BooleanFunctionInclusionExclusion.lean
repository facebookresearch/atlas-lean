/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BooleanFunctionInclusionExclusion

open MetaMathlibExt

-- Both constant functions count when there are no variables.
example : (Nat.card {f : (Fin 0 → Bool) → Bool // IsNondegenerateBoolFun f} : ℤ) = 2 := by
  have h := card_nondegenerate_boolFun_eq_alternating_sum (fun _ _ => True)
    (fun _ _ _ _ => Iff.rfl) 0
  simp only [and_true] at h
  rw [h]
  simp_rw [Nat.card_eq_fintype_card]
  decide

-- Inclusion–exclusion gives 16 - 2 * 4 + 2 functions depending on both variables.
example : (Nat.card {f : (Fin 2 → Bool) → Bool // IsNondegenerateBoolFun f} : ℤ) = 10 := by
  have h := card_nondegenerate_boolFun_eq_alternating_sum (fun _ _ => True)
    (fun _ _ _ _ => Iff.rfl) 2
  simp only [and_true, Nat.card_subtype_true, Nat.card_fun, Nat.card_fin] at h
  rw [h, Nat.card_eq_fintype_card (α := Bool)]
  decide
