/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many primes of the form $4k^2 + 2k + 1$.** There are infinitely many natural
numbers $k$ such that $4k^2 + 2k + 1$ is prime.

The source derives this from its Conjecture A (Bunyakovsky's conjecture). Only this polynomial
is stated here, not the full Bunyakovsky conjecture nor the companion polynomial $9k^2 + 6k + 2$.

Source: Jean-Marie De Koninck and Matthieu Moineau, "Consecutive Integers
Divisible by a Power of their Largest Prime Factor", Journal of Integer
Sequences 21 (2018), Article 18.9.3, lines 239–242,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/DeKoninck/dek22.tex>.
-/
theorem_wanted conjectureA_prime_values_four_square :
    Set.Infinite {k : ℕ | Nat.Prime (4 * k ^ 2 + 2 * k + 1)}

end

end MetaMathlibExt
