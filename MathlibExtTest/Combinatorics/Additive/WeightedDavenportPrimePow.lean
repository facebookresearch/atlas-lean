/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportPrimePow

namespace MetaMathlibExt

/-- In rank one with the smallest exponent and weight, the threshold is two. -/
example : weightedDavenport {1} (Fin 1 → ZMod 2) = 2 :=
  weightedDavenport_pi_zmod_prime_pow_of_dvd 2 1 1 Nat.prime_two (by decide)
    (fun _ => 1) monotone_const le_rfl le_rfl {1} (by decide) (by decide) (by decide)

/-- Weight two on the factors of orders eight and sixteen gives a threshold of eleven. -/
example : weightedDavenport {2} ((i : Fin 2) → ZMod (2 ^ ((i : ℕ) + 3))) = 11 :=
  (weightedDavenport_pi_zmod_prime_pow_of_dvd 2 2 2 Nat.prime_two (by decide)
    (fun i => (i : ℕ) + 3) (fun _ _ h => Nat.add_le_add_right h 3)
    (by decide) (by decide) {2} (by decide) (by decide) (by decide)).trans (by decide)

/-- In rank one the comparison with later factors is vacuous. The remainder of 32
modulo the weight bound 10 is two, and weight eight gives threshold four. -/
example : weightedDavenport {8} (Fin 1 → ZMod 32) = 4 :=
  (weightedDavenport_pi_zmod_prime_pow_of_not_dvd 2 1 2 Nat.prime_two (by decide)
    (fun _ => 5) monotone_const (by decide) (by decide) {8}
    (by decide) (by decide) (by decide) (by decide)).trans (by decide)

/-- Weights four and seven on two factors of order eight give threshold three. -/
example : weightedDavenport {4, 7} (Fin 2 → ZMod 8) = 3 :=
  (weightedDavenport_pi_zmod_prime_pow_of_not_dvd 2 2 1 Nat.prime_two (by decide)
    (fun _ => 3) monotone_const (by decide) (by decide) {4, 7}
    (by decide) (by decide) (by decide) (by decide)).trans (by decide)

end MetaMathlibExt
