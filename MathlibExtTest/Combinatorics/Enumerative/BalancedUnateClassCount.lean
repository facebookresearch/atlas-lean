/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BalancedUnateClassCount

open MetaMathlibExt

-- There are no balanced functions on zero variables: the domain has odd cardinality.
example :
    boolFunClassCount (n := 0) IsBoolFunNNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ (0 : ℕ)) = 0 ∧
      boolFunClassCount (n := 0) IsBoolFunNPNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ (0 : ℕ)) = 0 := by
  have hnone : (fun f : (Fin 0 → Bool) → Bool => Monotone f ∧ 2 * boolFunWeight f = 2 ^ (0 : ℕ)) =
      fun _ => False := by
    funext f
    apply propext
    simp only [pow_zero, iff_false]
    rintro ⟨_, hw⟩
    omega
  obtain ⟨hNN, hNPN⟩ := boolFunClassCount_balanced_unate_eq_monotone 0
  rw [hnone] at hNN hNPN
  exact ⟨hNN.trans (boolFunClassCount_false _), hNPN.trans (boolFunClassCount_false _)⟩

-- At arity two, the two clauses apply to the relations with and without input permutations.
example :
    boolFunClassCount (n := 2) IsBoolFunNNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 4) =
        boolFunClassCount (n := 2) IsBoolFunNNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 4) ∧
      boolFunClassCount (n := 2) IsBoolFunNPNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 4) =
        boolFunClassCount (n := 2) IsBoolFunNPNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 4) :=
  boolFunClassCount_balanced_unate_eq_monotone 2
