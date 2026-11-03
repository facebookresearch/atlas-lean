/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the dense coefficient update from integers to semirings and connect it to Mathlib's
little-endian polynomial coefficient lists.
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList

/-! # Dense coefficient lists under multiplication by a linear polynomial

This module updates a little-endian coefficient list when its polynomial is multiplied on the
left by `C r + X * C c`. The list remains dense: each update adds one entry, even when the new
leading coefficient is zero.

Adapted from `eth/proof/networks/Eight/SecCrossing_PolyDefs.lean` and
`eth/proof/networks/Eight/SecCrossing_MulOut.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- The dense little-endian coefficients after left multiplication by `C r + X * C c`. -/
def mulLinearCoeffList (r c : R) (l : List R) : List R :=
  List.zipWithAll (fun a b => a.getD 0 + b.getD 0)
    (l.map (r * ·)) ((0 :: l).map (c * ·))

private theorem length_zipWithAll {A B C : Type*} (f : Option A → Option B → C)
    (p : List A) (q : List B) :
    (List.zipWithAll f p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp
  | cons a p ih =>
    cases q with
    | nil => simp
    | cons b q => simp [ih]

/-- A linear-coefficient update always adds one dense coefficient. -/
@[simp] theorem length_mulLinearCoeffList (r c : R) (l : List R) :
    (mulLinearCoeffList r c l).length = l.length + 1 := by
  rw [mulLinearCoeffList, length_zipWithAll]
  simp

/-- The coefficient at every index, including beyond the dense output, follows the source
recurrence `r * l[j] + c * l[j - 1]`. -/
@[simp] theorem getD_mulLinearCoeffList (r c : R) (l : List R) (j : ℕ) :
    (mulLinearCoeffList r c l).getD j 0 =
      r * l.getD j 0 + c * (0 :: l).getD j 0 := by
  simp only [mulLinearCoeffList, List.getD_eq_getElem?_getD,
    List.getElem?_zipWithAll, List.getElem?_map]
  cases h₁ : l[j]? <;> cases h₂ : (0 :: l)[j]? <;> simp_all

/-- Interpreting the dense output as a little-endian polynomial is left multiplication by the
linear polynomial `C r + X * C c`. -/
@[simp] theorem ofCoeffList_mulLinearCoeffList (r c : R) (l : List R) :
    ofCoeffList (mulLinearCoeffList r c l) =
      (C r + X * C c) * ofCoeffList l := by
  simp only [mulLinearCoeffList, ofCoeffList_zipWithAll_add, ofCoeffList_map_mul,
    ofCoeffList_zero_cons, add_mul]
  rw [← mul_assoc, X_mul_C, mul_assoc]

end Polynomial
