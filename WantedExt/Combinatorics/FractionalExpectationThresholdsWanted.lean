/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thresholds versus fractional expectation-thresholds

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.FractionalExpectationThresholds` — annals_fractional_expectation_thresholds (manifest `manifests/problems/annals_fractional_expectation_thresholds.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted` namespace. Mathematical
statements are unchanged. Source: K. Frankston, J. Kahn, B. Narayanan, and J. Park, `Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.SetBernoulli

@[expose] public section

namespace MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
/-!
# Main Statement from Thresholds versus fractional expectation-thresholds

We formalise the statement of the main result from K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
-/

set_option autoImplicit false

namespace FractionalExpectationThresholds

open ProbabilityTheory unitInterval Set

open scoped NNReal

section Definitions

open Classical in
/-- **Weakly $p$-small families.** Let $X$ be a finite set, $p \in [0, 1]$, and $\mathcal F$ a
family of subsets of $X$. Then $\mathcal F$ is weakly $p$-small if there is a function $g$ from
subsets of $X$ to the nonnegative reals such that $\sum_{S \subseteq T} g(S) \ge 1$ for every
$T \in \mathcal F$ and $\sum_{S \subseteq X} g(S)\, p^{|S|} \le 1/2$. -/
def IsWeaklySmall {X : Type*} [Fintype X] (p : I) (𝓕 : Set (Set X)) : Prop :=
  ∃ g : Set X → ℝ≥0, (∀ T ∈ 𝓕, ∑ S with S ⊆ T, g S ≥ 1) ∧ ∑ S, g S * (p : ℝ) ^ S.ncard ≤ 2⁻¹

open Classical in
/-- **The threshold $p_c(\mathcal F)$.** For a set $X$ and $p \in [0, 1]$, let $\mu_p$ be the
$p$-biased product measure on subsets of $X$, under which each element of $X$ lies in the
random subset independently with probability $p$. For a family $\mathcal F$ of subsets of $X$,
$p_c(\mathcal F)$ is some $p \in [0, 1]$ with $\mu_p(\mathcal F) = 1/2$ if such a $p$ exists,
and $0$ otherwise.

When $X$ is finite and $\mathcal F$ is increasing, nonempty and not the family of all subsets
of $X$, such a $p$ exists and is unique; it is the threshold of $\mathcal F$. -/
noncomputable def p_c {X : Type*} (𝓕 : Set (Set X)) : I :=
  if h : ∃ p, setBer(univ, p).real (𝓕 : Set (Set X)) = 2⁻¹ then Classical.choose h else 0

/-- **The fractional expectation-threshold $q_f(\mathcal F)$.** For a family $\mathcal F$ of
subsets of a finite set $X$, $q_f(\mathcal F)$ is the supremum, in $[0, 1]$, of the set of all
$p \in [0, 1]$ such that $\mathcal F$ is weakly $p$-small; it is $0$ if there is no such $p$. -/
noncomputable def q_f {X : Type*} [Fintype X] (𝓕 : Set (Set X)) : I :=
  sSup {p | IsWeaklySmall p 𝓕}

/-- **Size of a largest minimal element, $\ell(\mathcal F)$.** For a family $\mathcal F$ of
subsets of a set $X$, $\ell(\mathcal F)$ is the largest cardinality of a minimal element of
$\mathcal F$ (minimal with respect to inclusion), a natural number.

By convention $\ell(\mathcal F) = 0$ when $\mathcal F$ has no minimal element or when the
cardinalities of its minimal elements are unbounded, and an infinite set counts as having
cardinality $0$. -/
noncomputable def l {X : Type*} (𝓕 : Set (Set X)) : ℕ :=
  ⨆ (A : 𝓕) (_ : IsMin A), (A : Set X).ncard

end Definitions

/- The constant `K` in Theorem 1.1. -/
/-- **The constant of the Frankston–Kahn–Narayanan–Park theorem.** A real number $K$, not yet
specified, that is to serve as the universal constant in the bound of the threshold of an
increasing family by $K$ times its fractional expectation-threshold times the logarithm of the
size of its largest minimal element.

Source: K. Frankston, J. Kahn, B. Narayanan, and J. Park, `Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean Via leanprover/lean-eval@38361be, problem `annals_fractional_expectation_thresholds`. -/
public def_wanted K : ℝ

/-- **Thresholds versus fractional expectation-thresholds.** Let $K$ be the universal real
constant still to be supplied. For every finite set $X$ and every increasing family $\mathcal F$
of subsets of $X$ (closed under taking supersets) with $\ell(\mathcal F) \ge 2$, where
$\ell(\mathcal F)$ is the size of a largest minimal element of $\mathcal F$,
$$p_c(\mathcal F) \le K \, q_f(\mathcal F) \log \ell(\mathcal F),$$
where $p_c$ is the threshold, $q_f$ the fractional expectation-threshold and $\log$ the
natural logarithm.

The hypothesis $\ell(\mathcal F) \ge 2$ is not explicit in the paper but is needed: if
$\ell(\mathcal F) = 1$ then $\log \ell(\mathcal F) = 0$, while $p_c(\mathcal F) \in (0, 1)$,
so the inequality cannot hold.

Source: K. Frankston, J. Kahn, B. Narayanan, and J. Park, `Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean Via leanprover/lean-eval@38361be, problem `annals_fractional_expectation_thresholds`.
-/
public theorem_wanted theorem_1_1 (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl𝓕 : 2 ≤ l 𝓕) : p_c 𝓕 ≤ ❰K❱ * q_f 𝓕 * Real.log (l 𝓕)

end FractionalExpectationThresholds

end MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
