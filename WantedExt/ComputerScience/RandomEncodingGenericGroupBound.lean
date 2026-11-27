/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Crypto.Framework.GenericGroup.RandomEncoding
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.PrimeFin

/-!
# Shoup's generic group bound with random identifiers

A. V. Sutherland, *18.783 Elliptic Curves*, MIT, Spring 2013, Lecture 11, §11.1,
Theorem 11.1 (pp. 1–3) gives the strict constant in this version of Shoup's bound.
The group is written in exponent coordinates with respect to its given generator.

The finite experiment needs enough `n`-bit words to label the group. The lecture's
`n = O(log N)` convention concerns families of groups and word lengths, not a second
restriction on a single experiment. Only the finite probability inequality is stated here.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup.RandomEncoding

/-- In a cyclic group of order `N ≥ 2` with largest prime divisor `p`, a strategy given the
random identifiers of the generator and the target succeeds with probability strictly less
than `m²/(2p)` if its call budget plus `4⌈log₂ N⌉` is at most `m`. Assume `N ≤ 2^n`, so there
are enough `n`-bit strings to label the group. Draw the secret uniformly in `ZMod N`, draw one
encoding uniformly from all injections of the group into `n`-bit strings, and draw the strategy's
coins from its own law, which need not be uniform. These three draws are mutually independent.
Identity, inversion and composition each use one call; computation on visible bits is free.

Source: A. V. Sutherland, MIT 18.783, Spring 2013, Lecture 11, Theorem 11.1. -/
theorem_wanted winProb_lt_sq_div_twice_largestPrime {N n q m : ℕ} (hN : 1 < N)
    (hcap : N ≤ 2 ^ n) (hm : q + 4 * Nat.clog 2 N ≤ m) {R : Type*}
    (coins : PMF R) (a : R → Strategy N n q) :
    let p := N.primeFactors.max' (Nat.nonempty_primeFactors.mpr hN)
    winProb ((experiment hN hcap coins a).map fun z => decide (z.2 = z.1)) <
      (m : ℝ) ^ 2 / (2 * p)

end Cslib.Crypto.Framework.GenericGroup.RandomEncoding
