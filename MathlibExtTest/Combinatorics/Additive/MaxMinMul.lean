/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Additive.MaxMinMul

/-!
# Max-min digit map regressions

Successor is monotone but does not preserve zero.
-/

open MetaMathlibExt

private theorem succ_mono : Monotone Nat.succ := fun _ _ h => Nat.succ_le_succ h

-- The product of the mapped zero sequences has coefficient 1 at every index.
example (k : ℕ) : maxMinMul (fun _ => 1) (fun _ => 1) k = 1 := by
  exact (congrFun (digitMap_lunar_hom succ_mono 0 0).2 k).trans
    (by simp [maxMinMul])

-- Check both operations on unequal coefficients, including a zero input digit.
example :
    ((Nat.succ ∘ (fun k => if k = 0 then 2 else 0)) ⊔
      (Nat.succ ∘ (fun k => if k = 1 then 3 else 0))) 1 = 4 ∧
    maxMinMul (Nat.succ ∘ (fun k => if k = 0 then 2 else 0))
      (Nat.succ ∘ (fun k => if k = 1 then 3 else 0)) 1 = 3 := by
  have h := digitMap_lunar_hom succ_mono
    (fun k => if k = 0 then 2 else 0) (fun k => if k = 1 then 3 else 0)
  constructor
  · rw [congrFun h.1 1]; decide
  · rw [congrFun h.2 1, Function.comp_apply, maxMinMul_one]; decide
