/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Fermat
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.NumberTheory.FermatNumberSquareFactors
public import MathlibExt.NumberTheory.FermatNumberWarrenBray
public import MathlibExt.NumberTheory.GeneralizedFermatFactorCount
public import MathlibExt.NumberTheory.GeneralizedFermatGCD
public import MathlibExt.NumberTheory.GeneralizedFermatPeriod
public import MathlibExt.NumberTheory.GeneralizedFermatShiftDivisibility
public import MathlibExt.NumberTheory.GeneralizedFermatSquareFactors
public import MathlibExt.NumberTheory.GeneralizedFermatWieferich
public import MathlibExt.NumberTheory.WieferichPrime
public import MathlibExt.NumberTheory.WieferichOrder
public import MathlibExt.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt

/-!
# Notes on Jakóbczyk's hypothesis on Fermat numbers

Statements from Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat
Numbers*, INTEGERS 26 (2026), Article A77, about the Fermat numbers
`F_n = 2^{2^n} + 1` (Mathlib's `Nat.fermatNumber`), their generalizations
`F_n(a, b) = a^{b^n} + 1`, and Wieferich primes to base `2` (`Nat.IsWieferichPrime`, i.e.
`p² ∣ 2^{p-1} - 1`) and to base `a` (`a^{p-1} ≡ 1 (mod p²)`).

The characterization of Wieferich primes to base `a` by multiplicative orders,
`MetaMathlibExt.pow_sub_one_modEq_one_sq_iff_orderOf_eq`, is proved in
`MathlibExt.NumberTheory.WieferichOrder`, and `MetaMathlibExt.not_pow_pow_modEq_one_of_lt`
is proved in `MathlibExt.NumberTheory.JakobczykFermatNotPowPowModEqOneOfLt`.
-/

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
