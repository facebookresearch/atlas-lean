/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean

open MetaMathlibExt

-- Before negation, `x 0 && !x 1` is increasing in coordinate 0 and decreasing in coordinate 1.
example : IsUnateBoolFun (fun x : Fin 2 → Bool => !(x 0 && !x 1)) := by
  apply isUnateBoolFun_not
  unfold IsUnateBoolFun IsBoolFunIncreasingIn IsBoolFunDecreasingIn
  decide

-- With no variables the unique input gives one function of each weight, zero and one.
example : Nat.card {f : (Fin 0 → Bool) → Bool // Monotone f ∧ boolFunWeight f = 0} = 1 := by
  rw [card_monotone_boolFun_weight_symm 0 0 (by decide), Nat.card_eq_fintype_card]
  decide

-- On two variables the unique monotone functions of weights one and three are AND and OR.
example : Nat.card {f : (Fin 2 → Bool) → Bool // Monotone f ∧ boolFunWeight f = 3} = 1 := by
  rw [card_monotone_boolFun_weight_symm 2 3 (by decide), Nat.card_eq_fintype_card]
  decide

example : boolFunWeight (boolFunConcat (fun _ : Fin 1 → Bool => false) (fun x => x 0)) = 1 := by
  decide
