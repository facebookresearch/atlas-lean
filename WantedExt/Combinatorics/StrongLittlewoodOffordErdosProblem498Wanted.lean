/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The strong Littlewood-Offord problem in the plane (Erdős Problem 498)

Erdős Problem 498: for `z₁, …, zₙ ∈ ℂ` with `|zᵢ| ≥ 1` and a disc `D` of radius `1`, do at most
`C(n, ⌊n/2⌋)` of the sums `∑ εᵢ zᵢ` (`εᵢ = ±1`) lie in `D`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Combinatorics.StrongLittlewoodOffordErdosProblem498Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #498, https://www.erdosproblems.com/498 (status PROVED
(LEAN)). UnsolvedMath record UM-30006904 (`EP-498`), dataset ulamai/UnsolvedMath v1.8.0.

The disc is open: for a closed disc the statement fails at `n = 1` (`z₁ = 1`, both `±1` lie in the
closed unit disc at `0`). Sums are counted by sign vector. Compared with the formal-conjectures
statement `ErdosProblems/498.lean` (equivalent; no code imported).
-/

/-- **Strong Littlewood–Offord bound in the plane.** The statement that for every natural
number $n$, all complex numbers $z_1, \dots, z_n$ with $|z_i| \ge 1$ for every $i$, and every
open disc $D$ of radius $1$ in $\mathbb{C}$, at most $\binom{n}{\lfloor n/2 \rfloor}$ of the
$2^n$ sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{1, -1\}^n$ satisfy
$\sum_i \varepsilon_i z_i \in D$ (Erdős Problem 498). -/
def signedSumsInUnitDiscBound : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, 1 ≤ ‖z i‖) → ∀ c : ℂ,
    {ε : Fin n → Bool | ∑ i, (if ε i then (1 : ℂ) else -1) * z i ∈ Metric.ball c 1}.ncard ≤
      n.choose (n / 2)

/--
**Kleitman's theorem on signed sums in the plane.** For every natural number $n$, all complex
numbers $z_1, \dots, z_n$ with $|z_i| \ge 1$ for every $i$, and every open disc $D$ of radius $1$
in $\mathbb{C}$, at most $\binom{n}{\lfloor n/2 \rfloor}$ of the $2^n$ sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{1, -1\}^n$ satisfy $\sum_i \varepsilon_i z_i \in D$.

Kleitman proved this bound for complex $z_i$ (later for vectors in any Hilbert space); Erdős had
proved it for real $z_i$.

Source: T. F. Bloom, Erdős Problems, Problem
#498, https://www.erdosproblems.com/498 (status PROVED (LEAN)); resolution: D. J. Kleitman, On a
lemma of Littlewood and Offord on the distribution of certain sums, Math. Z. (1965), 251-259,
erdosproblems.com/498: solved in the affirmative by Kleitman; generalized to Hilbert spaces
(Kleitman 1970), https://www.erdosproblems.com/498.
-/
public theorem_wanted signedSumsInUnitDiscBound_holds : signedSumsInUnitDiscBound

end MathlibExt.Combinatorics.StrongLittlewoodOffordErdosProblem498Wanted
