/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On approximation to a real number by algebraic numbers of bounded degree

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.OnApproximationOfReals` — annals_on_approximation_of_reals (manifest `manifests/problems/annals_on_approximation_of_reals.toml`, rev 1, submitter Katerina Hristova, Kevin Buzzard, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.OnApproximationOfRealsWanted` namespace. Mathematical statements are unchanged, except that the algebraic approximants are restricted from `ℂ` to `ℝ` as Poëls' theorem requires (see `AlgebraicDegLE`). Source: A. Poëls, `On approximation to a real number by algebraic numbers of bounded degree`, Annals of Math, 201 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-1-OnApproximationOfReals.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.OnApproximationOfRealsWanted
/-!
# Main Statement from On approximation to a real number by algebraic numbers of bounded degree

We formalise the statement of the main result from A. Poëls,
`On approximation to a real number by algebraic numbers of bounded degree`,
Annals of Math, 201 (1) 2025.
-/

set_option autoImplicit false

namespace OnApproximationOfReals

open NNReal ENNReal

/-- **Height of a real algebraic number.** Let $\alpha$ be a real algebraic number, let $p$ be its
monic minimal polynomial over $\mathbb{Q}$, and let $D$ be the least common multiple of the
denominators of the nonzero coefficients of $p$. The height $H(\alpha)$ is the largest absolute
value of a coefficient of the integer polynomial $D p$. For a real number that is not algebraic
over $\mathbb{Q}$, the height is $0$.

Equivalently, $H(\alpha)$ is the largest absolute value of a coefficient of the minimal polynomial
of $\alpha$ scaled to have coprime integer coefficients. -/
noncomputable def height (α : ℝ) : ℕ :=
  -- Let `p` be the minimal polynomial of `α`, defined to be monic and over `ℚ`.
  letI p := minpoly ℚ α
  -- Now let `D` be the LCM of the denominators of the nonzero coefficients.
  letI D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val)
  -- The height of `α` is the supremum of the finite set of `|n|`, where `n` runs
  -- through the numerators of the nonzero coefficients of `D * p`.
  Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs)

/-- **Real algebraic numbers of bounded degree.** For a natural number $n$, this is the type of
real numbers $\alpha$ that are algebraic over $\mathbb{Q}$ and whose minimal polynomial over
$\mathbb{Q}$ has degree at most $n$.

Source: the lean-eval source ranged over `ℂ`; the classical exponent in Poëls' theorem uses real
algebraic approximants, so this is restricted to `ℝ` (recorded as a Lean variant). -/
def AlgebraicDegLE (n : ℕ) : Type :=
  {α : ℝ // IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n}

/-- **Approximation exponents admitting infinitely many solutions.** Let $n$ be a natural number,
$\xi$ a real number, and $H(\alpha)$ the height of a real algebraic number $\alpha$. This is the
set of real numbers $\omega > 0$ for which there are infinitely many real algebraic numbers
$\alpha$ of degree at most $n$ with $0 < |\xi - \alpha| \le H(\alpha)^{-\omega - 1}$.

When $n \ge 1$ and $\xi$ is irrational, this set contains the interval $(0, 1)$ by Dirichlet's
theorem.

Source: `ω` here is `ω⋆` in the paper.
-/
def ω_stars (n : ℕ) (ξ : ℝ) : Set ℝ≥0 :=
  {ω : ℝ≥0 | 0 < ω ∧
    {α : AlgebraicDegLE n | 0 < ‖ξ - α.1‖ ∧ ‖ξ - α.1‖ ≤ (height α.1) ^ (- (ω : ℝ) - 1)}.Infinite}

/-- **Classical exponent of approximation by algebraic numbers.** For a natural number $n$ and a
real number $\xi$, let $H(\alpha)$ denote the height of a real algebraic number $\alpha$. The
classical exponent $\omega^*_n(\xi)$ is the supremum in $[0, \infty]$ of the set of real numbers
$\omega > 0$ for which there are infinitely many real algebraic numbers $\alpha$ of degree at
most $n$ with $0 < |\xi - \alpha| \le H(\alpha)^{-\omega - 1}$.
It is $0$ when this set is empty. -/
noncomputable def classicalExponent (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  sSup (((↑) : ℝ≥0 → ℝ≥0∞) '' (ω_stars n ξ))

/-- We use notation `ω⋆` for the classical exponent. -/
notation "ω⋆" => classicalExponent

/--
**Poëls' lower bound for the classical exponent.** Let $n \ge 2$ be an integer and let
$a = 1/(2 - \log 2)$. For every real number $\xi$ that is transcendental over $\mathbb{Q}$, the
classical exponent of approximation to $\xi$ by real algebraic numbers of degree at most $n$
satisfies $\omega^*_n(\xi) \ge a n$.

Source: A. Poëls, `On approximation to a real number by algebraic numbers of bounded degree`, Annals of Math, 201 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-1-OnApproximationOfReals.lean Via leanprover/lean-eval@38361be, problem `annals_on_approximation_of_reals`.
-/
public theorem_wanted theorem_1_1 (n : ℕ) (hn : n ≥ 2) (ξ : ℝ) (hξ : Transcendental ℚ ξ) :
    letI a : ℝ := 1 / (2 - Real.log 2)
    (ω⋆ n ξ : EReal) ≥ (a : EReal) * n

end OnApproximationOfReals

end MathlibExt.NumberTheory.OnApproximationOfRealsWanted
