/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter

/-!
# Meissel–Mertens constant: definitions

The definitions that the statements of
`WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted`, and of the wanted modules
built on it, use, moved here unchanged so that their proofs can import them.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **The Meissel–Mertens constant.** With $p$ ranging over the primes and $\log$ the natural
logarithm, the Meissel–Mertens constant is the real number
$$B = \lim_{n \to \infty} \Bigl(\sum_{p \le n} \frac{1}{p} - \log \log n\Bigr),$$
the limit taken over natural numbers $n$. Numerically, $B \approx 0.2614972128$. -/
noncomputable def meisselMertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ =>
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      1 / (p : ℝ)) - Real.log (Real.log n))

end

end MetaMathlibExt
