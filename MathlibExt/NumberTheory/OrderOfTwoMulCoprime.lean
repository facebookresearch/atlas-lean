/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Order of two modulo a coprime product

The Chinese remainder equivalence takes the residue of two to the pair of its residues.
The ATLAS wiki attributes the formula to E. L. Roettger and H. C. Williams,
*Some Remarks Concerning the Lucas-Lehmer Primality Test*.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- The multiplicative order of two modulo a product of coprime odd natural numbers is the
least common multiple of its orders modulo the two factors.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Proposition 11. -/
public theorem orderOf_two_mul_coprime {m₁ m₂ : ℕ} (h₁ : Odd m₁) (h₂ : Odd m₂)
    (hc : m₁.Coprime m₂) :
    orderOf (2 : ZMod (m₁ * m₂)) =
      Nat.lcm (orderOf (2 : ZMod m₁)) (orderOf (2 : ZMod m₂)) := by
  calc
    _ = orderOf (ZMod.chineseRemainder hc 2) :=
      ((ZMod.chineseRemainder hc).toMulEquiv.orderOf_eq 2).symm
    _ = _ := by rw [map_ofNat]; exact Prod.orderOf_mk

end MetaMathlibExt
