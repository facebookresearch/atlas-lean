/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A reverse Littlewood–Offord problem (Erdős Problem 395)

Erdős Problem 395: if `z₁, …, zₙ ∈ ℂ` with `|zᵢ| = 1`, is the probability that `|ε₁z₁ + ⋯ + εₙzₙ| ≤
√2`, for independent uniform signs `εᵢ ∈ {-1, 1}`, at least `≫ 1/n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED
(LEAN)). UnsolvedMath record UM-30006851 (`EP-395`), dataset ulamai/UnsolvedMath v1.8.0.

The probability is the proportion of the `2ⁿ` sign vectors, encoded as `Fin n → Bool`; the constant
is absolute and `n ≥ 1`. Compared with the formal-conjectures statement `ErdosProblems/395.lean`
(equivalent; no code imported).
-/

/-- **Number of short signed sums.** For complex numbers $z_1, \dots, z_n$, this is the number of
sign vectors $(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$. -/
noncomputable def smallSignedSumCount {n : ℕ} (z : Fin n → ℂ) : ℕ :=
  {ε : Fin n → Bool | ‖∑ i, (if ε i then (1 : ℂ) else -1) * z i‖ ≤ Real.sqrt 2}.ncard

/-- **Reverse Littlewood–Offord statement of Erdős Problem 395.** The statement that there is a
real constant $c > 0$ such that for every natural number $n \ge 1$ and all complex numbers
$z_1, \dots, z_n$ with $|z_i| = 1$ for every $i$, the number $N$ of sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ with
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$ satisfies $c/n \le N/2^n$. That is,
for independent uniformly random signs this inequality holds with probability at least $c/n$. -/
def reverseLittlewoodOffordSqrtTwo : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) →
    c / n ≤ (smallSignedSumCount z : ℝ) / 2 ^ n

/--
**Erdős Problem 395 holds: the reverse Littlewood–Offord bound.** There is a real constant
$c > 0$ such that for every natural number $n \ge 1$ and all complex numbers $z_1, \dots, z_n$
with $|z_i| = 1$ for every $i$, at least a $c/n$ fraction of the $2^n$ sign vectors
$(\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$ satisfy
$|\varepsilon_1 z_1 + \dots + \varepsilon_n z_n| \le \sqrt{2}$. That is, for independent uniformly
random signs this inequality holds with probability at least $c/n$.

This was proved by He, Juškevičius, Narayanan and Spiro. The order $1/n$ is sharp: take half of the
$z_i$ equal to $1$ and the rest equal to the imaginary unit $\mathrm{i}$.

Source: T. F. Bloom, Erdős
Problems, Problem #395, https://www.erdosproblems.com/395 (status PROVED (LEAN)); resolution: X. He,
T. Juškevičius, B. Narayanan and S. Spiro, The reverse Littlewood-Offord problem of Erdős,
arXiv:2408.11034 (2024), probability ≫ 1/n, sharp (erdosproblems.com/395),
https://arxiv.org/abs/2408.11034.
-/
public theorem_wanted reverseLittlewoodOffordSqrtTwo_holds : reverseLittlewoodOffordSqrtTwo

end MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted
