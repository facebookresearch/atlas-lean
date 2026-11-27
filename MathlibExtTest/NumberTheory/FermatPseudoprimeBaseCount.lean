/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatPseudoprimeBaseCount

/-! # Concrete counts of Fermat pseudoprime bases -/

namespace MetaMathlibExt

-- The units modulo 8 are not cyclic; only base 1 passes.
example : {b : ℕ | 1 ≤ b ∧ b < 8 ∧ Nat.FermatPsp 8 b}.ncard = 1 := by
  rw [card_fermatPsp_bases_eq_prod_gcd (by decide) (by decide)]
  decide +kernel

-- The repeated prime in 45 = 3² × 5 contributes just gcd(44, 2).
example : {b : ℕ | 1 ≤ b ∧ b < 45 ∧ Nat.FermatPsp 45 b}.ncard = 8 := by
  rw [card_fermatPsp_bases_eq_prod_gcd (by decide) (by decide)]
  decide +kernel

-- For 28 = 4 × 7 the 2-power contributes one and the odd prime contributes three.
example : {b : ℕ | 1 ≤ b ∧ b < 28 ∧ Nat.FermatPsp 28 b}.ncard = 3 := by
  rw [card_fermatPsp_bases_eq_prod_gcd (by decide) (by decide)]
  decide +kernel

end MetaMathlibExt
