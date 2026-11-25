/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PadicValuationMinTwice

namespace MetaMathlibExt

private def valuations (ℓ a b c d : ℕ) : Fin 6 → ℕ :=
  ![padicValNat ℓ (a * b + 1), padicValNat ℓ (a * c + 1), padicValNat ℓ (a * d + 1),
    padicValNat ℓ (b * c + 1), padicValNat ℓ (b * d + 1), padicValNat ℓ (c * d + 1)]

private def RepeatedMin (x : Fin 4 → ℕ) : Prop :=
  ∃ i j, i ≠ j ∧ x i = x j ∧ ∀ k, x i ≤ x k

private def AllThree (v : Fin 6 → ℕ) : Prop :=
  RepeatedMin ![v 1, v 2, v 3, v 4] ∧ RepeatedMin ![v 0, v 1, v 4, v 5] ∧
    RepeatedMin ![v 0, v 2, v 3, v 5]

private theorem allThree_of_valuations {ℓ a b c d : ℕ} (hℓ : ℓ.Prime) (v : Fin 6 → ℕ)
    (hv : ∀ i, valuations ℓ a b c d i = v i) : AllThree v := by
  rw [← funext hv]
  exact padicValNat_two_smallest_eq hℓ a b c d

-- A zero entry gives values `1` in three slots, but the other slots need not have valuation zero.
example : AllThree ![0, 0, 0, 0, 1, 0] :=
  allThree_of_valuations (a := 0) (b := 1) (c := 2) (d := 5) Nat.prime_two _ (by decide +kernel)

-- For 2 the pairs of minimizing positions (zero-based) are (0,3), (1,2), and (0,1).
example : AllThree ![2, 1, 2, 4, 1, 3] :=
  allThree_of_valuations (a := 1) (b := 3) (c := 5) (d := 11) Nat.prime_two _ (by decide +kernel)

-- At the odd prime 3, the third tuple still has a positive minimum although some slots are zero.
example : AllThree ![1, 0, 1, 2, 0, 2] :=
  allThree_of_valuations (ℓ := 3) (a := 1) (b := 2) (c := 4) (d := 11) (by decide) _ (by decide +kernel)

#print axioms padicValNat_two_smallest_eq

end MetaMathlibExt
