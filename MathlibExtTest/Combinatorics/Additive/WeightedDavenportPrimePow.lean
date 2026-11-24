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

end MetaMathlibExt
