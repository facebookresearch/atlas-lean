/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arbitrarily long sequences of Sierpiński numbers

Statement from Carrie E. Finch-Smith and R. Scottfield
Groth, "Arbitrarily Long Sequences of Sierpiński Numbers
that are the Sum of a Sierpiński Number and a Mersenne
Number", *Journal of Integer Sequences* 28 (2025),
Article 25.2.4
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Finch/finchs1.html>).

The Mersenne numbers are Mathlib's `mersenne j`
(`= 2^j - 1`, so `mersenne 0 = 0` and the shifted
family includes `k` itself, matching the paper's
title), compositeness is the
shared predicate `Nat.IsComposite`, and the base
integer ranges over `ℕ` (any
`k + M_j ≤ 0` would violate the compositeness conclusion
anyway). The paper's "(in arithmetic progression)" is
part of the conclusion: a full arithmetic progression
`a + r * d` (with `0 < d`) of base integers has the
property. Sanity-checked numerically: `78557` realizes
the `t = 0` case's property, and candidates for `t = 1`
exist on bounded exponent ranges.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LucasLehmer
public import MathlibExt.NumberTheory.Composite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SierpinskiMersenneWanted

/-- **Theorem 1**: for every fixed `t` there is an
arithmetic progression of integers `k = a + r * d`
(`0 < d`) such that `(k + M_j) * 2^n + 1` is composite
for every `j ≤ t` and every nonnegative `n`, where
`M_j = mersenne j` is the `j`-th Mersenne number.

Source: Carrie E. Finch-Smith and R. Scottfield Groth,
"Arbitrarily Long Sequences of Sierpiński Numbers that
are the Sum of a Sierpiński Number and a Mersenne
Number", Theorem 1. -/
theorem_wanted exists_arithProg_sierpinski_add_mersenne
    (t : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ r : ℕ, ∀ j ≤ t, ∀ n : ℕ,
      Nat.IsComposite ((a + r * d + mersenne j) * 2 ^ n + 1)

end MathlibExt.NumberTheory.SierpinskiMersenneWanted
