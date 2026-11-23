/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An eventual threshold for quadratic character sums (Erdős Problem 981)

Erdős Problem 981: let `ε > 0` and `f_ε(p)` be the smallest integer `m` such that `∑_{n ≤ N} (n/p) <
εN` for all `N ≥ m`. Prove that `∑_{p < x} f_ε(p) ∼ c_ε x / log x` for some `c_ε > 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.CharacterSumThresholdErdosProblem981Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #981, https://www.erdosproblems.com/981 (status
PROVED). UnsolvedMath record UM-30007108 (`EP-981`), dataset ulamai/UnsolvedMath v1.8.0.

`(n/p)` is the Legendre symbol, written `jacobiSym n p` (they agree for prime `p`); the sum is over
the odd primes `p < x`, and `m`, `N` are positive integers (`f_ε(p)` exists because the partial sums
are bounded by `p`). This is Erdős's eventual-time formulation, the one on the page now; an earlier
version of the page had a first-passage variant, solved separately by Tang and Zhang. `∼` is
`Asymptotics.IsEquivalent` as `x → ∞` through `ℕ`. Compared with the formal-conjectures statement
`ErdosProblems/981.lean` (`erdos_981`, equivalent: the prime `2` and the term `n = 0` change
nothing; no code imported).
-/

open Asymptotics Filter

/-- `f_ε(p)`: the least `m ≥ 1` such that `∑_{n ≤ N} (n / p) < ε N` for every `N ≥ m`, where
`(n / p)` is the Legendre symbol (`jacobiSym n p` for prime `p`); it exists for `ε > 0`, since the
partial sums are bounded by `p`. -/
noncomputable def characterSumThreshold (ε : ℝ) (p : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∀ N : ℕ, m ≤ N → ((∑ n ∈ Finset.Icc 1 N, jacobiSym n p : ℤ) : ℝ) < ε * N}

/-- Erdős Problem 981: for every `ε > 0` there is `c_ε > 0` with
`∑_{p < x} f_ε(p) ~ c_ε x / log x`, the sum over odd primes. -/
def characterSumThresholdAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    (fun x : ℕ => ∑ p ∈ (Nat.primesBelow x).filter (fun p => p ≠ 2),
        (characterSumThreshold ε p : ℝ)) ~[atTop] fun x => c * x / Real.log x

/--
Resolved true: Elliott proved `∑_{p < x} f_ε(p) ∼ c_ε x / log x` for this eventual-time threshold,
for every `ε > 0`; erdosproblems.com/981 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #981, https://www.erdosproblems.com/981 (status PROVED); resolution: P. D. T. A.
Elliott, A conjecture of Erdős concerning character sums, Indag. Math. (1969), 164-171,
erdosproblems.com/981: 'This was proved by Elliott'; Q. Tang in the discussion thread confirms that
Elliott's paper resolves Erdős's eventual-time formulation [Er65b, (80)],
https://www.erdosproblems.com/981.
-/
public theorem_wanted characterSumThresholdAsymptotic_holds : characterSumThresholdAsymptotic

end MathlibExt.NumberTheory.CharacterSumThresholdErdosProblem981Wanted
