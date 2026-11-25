/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeAddSub

/-! # Tests for the sum and difference bases modulo the fifth Fermat number -/

namespace MetaMathlibExt.fermatNumber_isStrongPseudoprime_two_pow_add_sub

private theorem five_composite : ¬(Nat.fermatNumber 5).Prime := by
  rw [show Nat.fermatNumber 5 = 641 * 6700417 by decide]
  exact Nat.not_prime_mul (by decide) (by decide)

-- At the endpoint `t = 0` the two bases are the neighbors of `2 ^ 16`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) 65537 ∧
    IsStrongPseudoprime (Nat.fermatNumber 5) 65535 :=
  fermatNumber_isStrongPseudoprime_two_pow_add_sub five_composite 0

-- At `t = 16`, the sum wraps around modulo `F₅` and the difference is `-65537`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) 65535 ∧
    IsStrongPseudoprime (Nat.fermatNumber 5) (-65537) :=
  fermatNumber_isStrongPseudoprime_two_pow_add_sub five_composite 16

end MetaMathlibExt.fermatNumber_isStrongPseudoprime_two_pow_add_sub
