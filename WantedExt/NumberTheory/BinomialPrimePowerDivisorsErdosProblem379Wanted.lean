/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Prime-power divisors common to all binomial coefficients (Erdős Problem 379)

Erdős Problem 379: let `S(n)` be the largest integer such that for all `1 ≤ k < n` the binomial
coefficient `C(n, k)` is divisible by `p^{S(n)}` for some prime `p` (depending on `k`). Is `limsup
S(n) = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.BinomialPrimePowerDivisorsErdosProblem379Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #379, https://www.erdosproblems.com/379 (status PROVED
(LEAN)). UnsolvedMath record UM-30006846 (`EP-379`), dataset ulamai/UnsolvedMath v1.8.0.

`limsup S(n) = ∞` is stated as: for every `s` there are infinitely many `n ≥ 2` for which every
`C(n, k)`, `1 ≤ k < n`, has a divisor `p^s` with `p` prime. This is equivalent, since the property
is monotone in `s` and `S(n)` is finite for `n ≥ 2` (`C(n, 1) = n`). Compared with the
formal-conjectures statement `ErdosProblems/379.lean` (equivalent to its ℕ∞-valued limsup; no code
imported).
-/

/-- Every `n.choose k` with `1 ≤ k < n` is divisible by `p ^ s` for some prime `p` (depending on
`k`). -/
def AllBinomialsHavePrimePowerDivisor (n s : ℕ) : Prop :=
  ∀ k ∈ Finset.Ico 1 n, ∃ p : ℕ, p.Prime ∧ p ^ s ∣ n.choose k

/-- Erdős Problem 379: `limsup S(n) = ∞`, i.e. for every `s` there are infinitely many `n ≥ 2`
such that every `n.choose k` with `1 ≤ k < n` is divisible by the `s`-th power of some prime. -/
def binomialPrimePowerExponentUnbounded : Prop :=
  ∀ s : ℕ, {n : ℕ | 2 ≤ n ∧ AllBinomialsHavePrimePowerDivisor n s}.Infinite

/--
Resolved true: Cambie, Kovač and Tao proved `limsup S(n) = ∞` (erdosproblems.com/379 comments);
erdosproblems.com/379 links a Lean formalization of their proof and lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #379, https://www.erdosproblems.com/379 (status PROVED
(LEAN)); resolution: S. Cambie, V. Kovač and T. Tao, comments on erdosproblems.com/379; Lean
formalization teorth/analysis, Analysis/Misc/erdos_379.lean, limsup S(n) = ∞
(erdosproblems.com/379),
https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/erdos_379.lean.
-/
public theorem_wanted binomialPrimePowerExponentUnbounded_holds :
    binomialPrimePowerExponentUnbounded

end MathlibExt.NumberTheory.BinomialPrimePowerDivisorsErdosProblem379Wanted
