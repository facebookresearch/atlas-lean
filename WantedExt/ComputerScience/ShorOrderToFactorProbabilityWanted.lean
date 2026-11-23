/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Basic.Real.Basic

/-!
# Most units give a factor in Shor's reduction (wanted)

The proved deterministic step is `Cslib.Shor.gcd_factor_of_order`: if the order `r` of `x`
modulo `n` is even and `x ^ (r / 2) ≢ -1 (mod n)`, then `gcd (x ^ (r / 2) - 1, n)` is a
nontrivial factor of `n`. This file records the probabilistic step: such `x` form at least a
`1 - 1 / 2 ^ (k - 1)` fraction of the units modulo an odd `n` with `k` distinct prime factors.

## Source

P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a
quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509 (arXiv:quant-ph/9508027), Section 5,
second and third paragraphs; Shor attributes the reduction to G. L. Miller (1976).
-/

@[expose] public section


namespace Cslib.Shor

/-- **Most units give a factor in Shor's reduction.** Let `n` be an odd positive integer with
`k` distinct prime factors. Among the units `x` modulo `n`, those whose multiplicative order `r`
is even and satisfies `x ^ (r / 2) ≠ -1` form a fraction at least `1 - 1 / 2 ^ (k - 1)` of all
units. For such `x`, `gcd (x ^ (r / 2) - 1, n)` is a nontrivial factor of `n`
(`Cslib.Shor.gcd_factor_of_order`), so a random unit yields a factor with probability at least
`1 - 1 / 2 ^ (k - 1)`, which is at least `1 / 2` when `n` is not a prime power (P. W. Shor,
SIAM J. Comput. 26 (1997), Section 5: "this procedure, when applied to a random `x (mod n)`,
yields a factor of `n` with probability at least `1 - 1/2^{k-1}`, where `k` is the number of
distinct odd prime factors of `n`"). -/
theorem_wanted card_units_good_for_factoring_ge {n : ℕ} [NeZero n] (hn : Odd n) :
    (1 - 1 / (2 : ℝ) ^ (n.primeFactors.card - 1)) * Fintype.card (ZMod n)ˣ ≤
      ((Finset.univ.filter fun x : (ZMod n)ˣ =>
        Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1).card : ℝ)

end Cslib.Shor
