/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Duffin-Schaeffer conjecture

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.DuffinSchaefferConjecture` — annals_duffin_schaeffer_conjecture (manifest `manifests/problems/annals_duffin_schaeffer_conjecture.toml`, rev 1, submitter Katerina Hristova, Kevin Buzzard, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted` namespace. Mathematical
statements are unchanged. Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted
/-!
# Main Statements from On the Duffin-Schaeffer conjecture

We formalise the statements of the main results from D. Koukoulopoulos and J. Maynard,
`On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020.

## Implementation Details

In the paper, `ℕ` denotes the positive integers, which are denoted `ℕ+` in Lean.
Hence, no changes to the domains of the functions `ψ` and `ψ⋆` have been made in the formalisation.
-/

set_option autoImplicit false

namespace DuffinSchaefferConjecture

open NNReal ENNReal MeasureTheory

open scoped Nat

/-- **The approximation inequality (1.7).** For a function $\psi$ from the positive integers to
the nonnegative reals, a real number $\alpha$, a natural number $a$ and a positive integer $q$,
inequality (1.7) is the condition $|\alpha - a/q| \le \psi(q)/q$. -/
def inequality_1_7 (ψ : ℕ+ → ℝ≥0) (α : ℝ) (a : ℕ) (q : ℕ+) : Prop :=
  |α - a / q| ≤ ψ q / q

/-- **The set $\mathcal{A}$ of the Duffin–Schaeffer conjecture.** For a function $\psi$ from the
positive integers to the nonnegative reals, $\mathcal{A}(\psi)$ is the set of real numbers
$\alpha \in [0, 1]$ for which inequality (1.7), $|\alpha - a/q| \le \psi(q)/q$, has infinitely
many solutions $(a, q)$ with $a$ a natural number, $q$ a positive integer and $\gcd(a, q) = 1$. -/
def 𝒜 (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 ψ α a q}.Infinite}

/-- **Koukoulopoulos–Maynard Theorem 1 (Duffin–Schaeffer conjecture).** Let $\psi$ be a function
from the positive integers to the nonnegative reals such that the series
$\sum_{q \ge 1} \psi(q)\varphi(q)/q$ diverges, where $\varphi$ is Euler's totient function. Let
$\mathcal{A}(\psi)$ be the set of real numbers $\alpha \in [0, 1]$ for which
$|\alpha - a/q| \le \psi(q)/q$ has infinitely many solutions with $a$ a natural number, $q$ a
positive integer and $\gcd(a, q) = 1$. Then $\mathcal{A}(\psi)$ is a Borel set and has
Lebesgue measure $1$.

Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_1 (ψ : ℕ+ → ℝ≥0) (hdivergence : ¬ Summable fun q ↦ (ψ q * φ q) / q) :
    MeasurableSet (𝒜 ψ) ∧ volume (𝒜 ψ) = 1

/-- **The set $\mathcal{K}$ of Catlin's conjecture.** For a function $\psi$ from the positive
integers to the nonnegative reals, $\mathcal{K}(\psi)$ is the set of real numbers
$\alpha \in [0, 1]$ for which inequality (1.7), $|\alpha - a/q| \le \psi(q)/q$, has infinitely
many solutions $(a, q)$ with $a$ a natural number and $q$ a positive integer such that $a \le q$.

The fractions $a/q$ need not be reduced. -/
def 𝒦 (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | {(a, q) : ℕ × ℕ+ | a ≤ q ∧ inequality_1_7 ψ α a q}.Infinite}

/-- **The function $\psi^*$ of Catlin's conjecture.** For a function $\psi$ from the positive
integers to the nonnegative reals, $\psi^*$ sends each positive integer $q$ to
$\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with } q \mid n\}$,
where $\varphi$ is Euler's totient function and the supremum is taken in $[0, \infty]$. -/
noncomputable def ψ_star (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0∞ :=
  fun q ↦ φ q * sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

/-- **Koukoulopoulos–Maynard Theorem 2(a) (Catlin's conjecture, convergent case).** Let $\psi$
be a function from the positive integers to the nonnegative reals, and for each positive integer
$q$ let $\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with }
q \mid n\}$, where $\varphi$ is Euler's totient function and the supremum is taken in
$[0, \infty]$. Let $\mathcal{K}(\psi)$ be the set of real numbers $\alpha \in [0, 1]$ for which
$|\alpha - a/q| \le \psi(q)/q$ has infinitely many solutions with $a$ a natural number and $q$ a
positive integer such that $a \le q$. If $\sum_{q \ge 1} \psi^*(q) < \infty$, then
$\mathcal{K}(\psi)$ is a Borel set and has Lebesgue measure $0$.

Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q < ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 0

/-- **Koukoulopoulos–Maynard Theorem 2(b) (Catlin's conjecture, divergent case).** Let $\psi$
be a function from the positive integers to the nonnegative reals, and for each positive integer
$q$ let $\psi^*(q) = \varphi(q) \cdot \sup \{\psi(n)/n : n \text{ a positive integer with }
q \mid n\}$, where $\varphi$ is Euler's totient function and the supremum is taken in
$[0, \infty]$. Let $\mathcal{K}(\psi)$ be the set of real numbers $\alpha \in [0, 1]$ for which
$|\alpha - a/q| \le \psi(q)/q$ has infinitely many solutions with $a$ a natural number and $q$ a
positive integer such that $a \le q$. If $\sum_{q \ge 1} \psi^*(q) = \infty$, then
$\mathcal{K}(\psi)$ is a Borel set and has Lebesgue measure $1$.

Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q = ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1

/-- **The convergence exponent $s(\psi)$.** For a function $\psi$ from the positive integers to
the nonnegative reals, $s(\psi)$ is the infimum, taken in the nonnegative reals, of the set of
real numbers $\beta \ge 0$ for which the series $\sum_{q \ge 1} \varphi(q) (\psi(q)/q)^{\beta}$
converges, where $\varphi$ is Euler's totient function. If there is no such $\beta$, then
$s(\psi) = 0$. -/
noncomputable def s_inf (ψ : ℕ+ → ℝ≥0) : ℝ≥0 :=
  sInf {β | Summable fun q : ℕ+ ↦ φ q * (ψ q / q) ^ β.1}

/-- **Koukoulopoulos–Maynard Corollary 3 (Hausdorff dimension of $\mathcal{A}$).** Let $\psi$
be a function from the positive integers to $[0, 1/2]$. Let $\mathcal{A}(\psi)$ be the set of
real numbers $\alpha \in [0, 1]$ for which $|\alpha - a/q| \le \psi(q)/q$ has infinitely many
solutions with $a$ a natural number, $q$ a positive integer and $\gcd(a, q) = 1$. Let $s(\psi)$
be the infimum, taken in the nonnegative reals (where the empty set has infimum $0$), of the
real numbers $\beta \ge 0$ for which the series $\sum_{q \ge 1} \varphi(q) (\psi(q)/q)^{\beta}$
converges, where $\varphi$ is Euler's totient function. Then the Hausdorff dimension of
$\mathcal{A}(\psi)$ equals $\min(s(\psi), 1)$.

Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted corollary_3 (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n, ψ n ∈ Set.Icc 0 (1 / 2)) :
    dimH (𝒜 ψ) = min (s_inf ψ) 1

end DuffinSchaefferConjecture

end MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted
