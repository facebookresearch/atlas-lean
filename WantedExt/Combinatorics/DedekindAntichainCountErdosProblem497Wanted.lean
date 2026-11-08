/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Number of antichains of subsets (Erdős Problem 497)

Erdős Problem 497 (Dedekind's problem): how many antichains of subsets of `[n]` are there?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #497, https://www.erdosproblems.com/497 (status SOLVED
(LEAN)). UnsolvedMath record UM-30006903 (`EP-497`), dataset ulamai/UnsolvedMath v1.8.0.

The answer recorded as the solution is Kleitman's asymptotic `2 ^ ((1 + o(1)) C(n, ⌊n/2⌋))`, stated
as `log₂ M(n) / C(n, ⌊n/2⌋) → 1`. Antichains are for `⊆` and include the empty family and `{∅}`.
Compared with the formal-conjectures statement `ErdosProblems/497.lean` (equivalent; it uses an
explicit `o(1)` function and `DedekindNumber`; no code imported).
-/

/-- The number of antichains (for `⊆`) of subsets of an `n`-element set, i.e. the Dedekind number
`M(n)`; the empty family and `{∅}` count. -/
noncomputable def antichainCount (n : ℕ) : ℕ :=
  {F : Finset (Finset (Fin n)) | IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))}.ncard

/-- Erdős Problem 497, Kleitman's answer: the number of antichains of subsets of `[n]` is
`2 ^ ((1 + o(1)) C(n, ⌊n / 2⌋))`, i.e. `log₂ M(n) / C(n, ⌊n / 2⌋) → 1`. -/
def antichainCountLogAsymptotic : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.logb 2 (antichainCount n) / (n.choose (n / 2) : ℝ))
    Filter.atTop (nhds 1)

/--
Resolved true: Kleitman proved that the number of antichains of subsets of `[n]` is `2 ^ ((1 + o(1))
C(n, ⌊n/2⌋))`. Source: T. F. Bloom, Erdős Problems, Problem #497, https://www.erdosproblems.com/497
(status SOLVED (LEAN)); resolution: D. Kleitman, On Dedekind's problem: the number of monotone
Boolean functions, Proc. Amer. Math. Soc. (1969), 677-682, erdosproblems.com/497: resolved by
Kleitman, the number is 2^{(1 + o(1)) C(n, ⌊n/2⌋)}, https://www.erdosproblems.com/497.
-/
public theorem_wanted antichainCountLogAsymptotic_holds : antichainCountLogAsymptotic

end MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497Wanted
