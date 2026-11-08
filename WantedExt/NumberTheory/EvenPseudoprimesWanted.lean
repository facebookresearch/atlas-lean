/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Even pseudoprimes and their reciprocal sum
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.NumberTheory.EvenPseudoprime

@[expose] public section

namespace MathlibExt.NumberTheory.EvenPseudoprimesWanted

/-!
# Even pseudoprimes — wishlist

This file states, without proving, Beeger's theorem that there are
infinitely many even pseudoprimes and the Cheng–Kinlaw–Nguyen bounds for
the sum of their reciprocals. The predicate and set are the shared
definitions from `MathlibExt.NumberTheory.EvenPseudoprime`.
-/

/--
**Beeger's theorem.** There are infinitely many even pseudoprimes.

Source: N. G. W. H. Beeger, "On even numbers `m` dividing
`2 ^ m - 2`," American Mathematical Monthly 58 (1951), 553–555.
-/
public theorem_wanted evenPseudoprimes_infinite :
    MathlibExt.NumberTheory.evenPseudoprimes.Infinite

/--
**Cheng–Kinlaw–Nguyen reciprocal-sum bounds.** The sum of the
reciprocals of all even pseudoprimes lies strictly between `0.000011`
and `0.0059`.

Source: Xuyan Cheng, Paul Kinlaw, and Duc Nguyen, "The Reciprocal Sum
of Even Pseudoprimes," Journal of Integer Sequences 29 (2026), main
theorem, `https://cs.uwaterloo.ca/journals/JIS/VOL29/Kinlaw/kinlaw11.tex`.
-/
public theorem_wanted evenPseudoprime_reciprocal_sum_bounds :
    (11 : ℝ) / 1000000 <
        ∑' N : MathlibExt.NumberTheory.evenPseudoprimes,
          (1 : ℝ) / (N.val : ℝ) ∧
      ∑' N : MathlibExt.NumberTheory.evenPseudoprimes,
          (1 : ℝ) / (N.val : ℝ) <
        (59 : ℝ) / 10000

end MathlibExt.NumberTheory.EvenPseudoprimesWanted
