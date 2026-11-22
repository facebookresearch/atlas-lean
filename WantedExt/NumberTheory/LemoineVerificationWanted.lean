/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Bounded verification of Lemoine's conjecture (statement)

Statement-only target from Zsófia Juhász, Máté Bartalos, Péter Magyar, and Gábor Farkas,
*Empirical Verification of a Generalization of Goldbach's Conjecture*: the computational
verification of Lemoine's conjecture up to `10^13`. The unbounded conjecture is
`OpenConjectures.NumberTheory.LemoineConjecture.conjecture`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Lemoine's conjecture holds up to `10^13`: every odd `n` with `5 < n ≤ 10^13` is `p + 2q`
for primes `p` and `q` (then `p` is odd, as `n` is). This is the abstract's sentence "We verify
Lemoine's conjecture up to a new record of `10^13`"; the abstract's other claims (the
Hardy–Littlewood generalization under unspecified congruence criteria, counterexample lists,
running-time comparisons) are not formalized.

Source: Zsófia Juhász, Máté Bartalos, Péter Magyar, and Gábor Farkas, *Empirical Verification of
a Generalization of Goldbach's Conjecture*, Journal of Integer Sequences 27 (2024),
Article 24.4.3, abstract (`jis-2024-24.4.3-abstract-main`). -/
public theorem_wanted lemoine_of_le_ten_pow_thirteen (n : ℕ) (hn : Odd n) (h5 : 5 < n)
    (hle : n ≤ 10 ^ 13) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

end

end MetaMathlibExt
