/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Comparing `φ(n)` with `φ(n - φ(n))` (Erdős Problem 1064)

Erdős Problem 1064: prove that `φ(n) > φ(n - φ(n))` for almost all `n`, but that `φ(n) < φ(n -
φ(n))` for infinitely many `n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.TotientOfTotientComplementErdosProblem1064Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1064, https://www.erdosproblems.com/1064 (status
PROVED). UnsolvedMath record UM-30007150 (`EP-1064`), dataset ulamai/UnsolvedMath v1.8.0.

"Almost all" is natural density `1`, written as the proportion of `n < N` tending to `1`. `n - φ(n)`
is truncated subtraction, harmless since `φ(n) ≤ n`. The two claims are separate targets. Compared
with the formal-conjectures statement `ErdosProblems/1064.lean` (equivalent; no code imported).
-/

/-- The proportion of `n < N` with `φ(n - φ(n)) < φ(n)`. -/
noncomputable def totientExceedsProportion (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => Nat.totient (n - Nat.totient n) < Nat.totient n).card : ℝ) / N

/-- Erdős Problem 1064, first part: `φ(n) > φ(n - φ(n))` for almost all `n` (natural density `1`).
-/
def totientExceedsAlmostAll : Prop :=
  Filter.Tendsto totientExceedsProportion Filter.atTop (nhds 1)

/-- Erdős Problem 1064, second part: `φ(n) < φ(n - φ(n))` for infinitely many `n`. -/
def totientDeficitInfinitelyOften : Prop :=
  {n : ℕ | Nat.totient n < Nat.totient (n - Nat.totient n)}.Infinite

/--
Resolved true: Luca and Pomerance proved that `φ(n) > φ(n - φ(n))` holds on a set of natural density
`1` (indeed `φ(n) > φ(n - φ(n)) + f(n)` for almost all `n` whenever `f(n) = o(n)`);
erdosproblems.com/1064 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1064, https://www.erdosproblems.com/1064 (status PROVED); resolution: F. Luca and C. Pomerance, On
some problems of Mąkowski-Schinzel and Erdős concerning the arithmetical functions φ and σ, Colloq.
Math. (2002), 111-130; A. Grytczuk, F. Luca and M. Wójtowicz, A conjecture of Erdős concerning
inequalities for the Euler totient function, Publ. Math. Debrecen (2001), 9-16, Luca-Pomerance: φ(n)
> φ(n - φ(n)) has density 1; Grytczuk-Luca-Wójtowicz: φ(n) < φ(n - φ(n)) infinitely often, e.g. n =
15 · 2^k (erdosproblems.com/1064), https://www.erdosproblems.com/1064.
-/
public theorem_wanted totientExceedsAlmostAll_holds : totientExceedsAlmostAll

/--
Resolved true: Grytczuk, Luca and Wójtowicz proved that `φ(n) < φ(n - φ(n))` for infinitely many
`n`; for example `n = 15 · 2^k` (`k ≥ 1`) has `φ(n) = 4 · 2^k` and `φ(n - φ(n)) = φ(11 · 2^k) = 5 ·
2^k`. Source: T. F. Bloom, Erdős Problems, Problem #1064, https://www.erdosproblems.com/1064 (status
PROVED); resolution: F. Luca and C. Pomerance, On some problems of Mąkowski-Schinzel and Erdős
concerning the arithmetical functions φ and σ, Colloq. Math. (2002), 111-130; A. Grytczuk, F. Luca
and M. Wójtowicz, A conjecture of Erdős concerning inequalities for the Euler totient function,
Publ. Math. Debrecen (2001), 9-16, Luca-Pomerance: φ(n) > φ(n - φ(n)) has density 1;
Grytczuk-Luca-Wójtowicz: φ(n) < φ(n - φ(n)) infinitely often, e.g. n = 15 · 2^k
(erdosproblems.com/1064), https://www.erdosproblems.com/1064.
-/
public theorem_wanted totientDeficitInfinitelyOften_holds : totientDeficitInfinitelyOften

end MathlibExt.NumberTheory.TotientOfTotientComplementErdosProblem1064Wanted
