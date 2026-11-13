/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 730
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem730Wanted

/-! UnsolvedMath record `EP-730`. -/

/-- Infinitely many pairs `0 < n < m` for which `choose (2n) n` and
`choose (2m) m` have the same prime divisors. -/
def conjecture : Prop :=
  Set.Infinite { nm : ℕ × ℕ |
    0 < nm.1 ∧ nm.1 < nm.2 ∧
      ∀ p : ℕ, Nat.Prime p →
        (p ∣ Nat.choose (2 * nm.1) nm.1 ↔ p ∣ Nat.choose (2 * nm.2) nm.2) }

/--
Resolved true: Resolved true: erdosproblems.com/730 records the problem as solved by a proof
generated with GPT Pro (prompted by L. Price) and accepted by the site: for all x there are >>
x^{1/2} values n <= x with C(2n,n) and C(2n+2,n+1) having the same prime divisors, so infinitely
many pairs (n, n+1) exist. Source: T. F. Bloom, Erdős Problem #730, erdosproblems.com (live
page, LaTeX source and forum threads read 2026-10-22), https://www.erdosproblems.com/730; L.
Price (with GPT Pro), proof for Erdős Problem #730, accepted on erdosproblems.com,
https://www.overleaf.com/read/gpttrsmhbhbk. Moved from
`OpenConjectures/NumberTheory/ErdosProblem730`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem730Wanted
