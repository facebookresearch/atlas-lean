/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hausdorff moment problem: absolute-continuity criterion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffAbsoluteContinuity` — hausdorff_absolute_continuity (manifest `manifests/problems/hausdorff_absolute_continuity.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted` namespace. Mathematical
statements are unchanged. Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*. Knill, *Some fundamental theorems in mathematics*, §115.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
namespace Analysis.HausdorffAbsoluteContinuity

/-!
# Hausdorff moment problem: absolute-continuity criterion

`hausdorff_absolute_continuity`: a positive probability measure `μ` on the unit
cube is uniformly absolutely continuous with respect to Lebesgue measure iff its
moment differences are dominated by those of Lebesgue measure. This is the third
statement of §115 of the Knill survey (the moment realizability and positivity
criteria are the companion lean-eval problems). The trusted helpers (`cube`,
`monomial`, `momentOf`, `multiChoose`, `diff`, `UniformlyAbsolutelyContinuous`)
are non-holes. Mathlib has `SignedMeasure`, finite measures, and set integrals
but no moment-problem machinery.

Category-(b) candidate from §115 of the Knill survey (additional statement 2).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- **Closed unit cube.** For $d \in \mathbb{N}$, the closed unit cube $I^d = [0,1]^d$ is the
set of points $x \in \mathbb{R}^d$ with $0 \le x_i \le 1$ for every coordinate $i$. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- **Multivariate monomial.** For a multi-index $n = (n_1, \dots, n_d) \in \mathbb{N}^d$ and a
point $x \in \mathbb{R}^d$, the monomial $x^n$ is the real number $\prod_{i=1}^{d} x_i^{n_i}$. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i)

/-- **Moments of a measure on the unit cube.** For a measure $\mu$ on $\mathbb{R}^d$ and a
multi-index $n \in \mathbb{N}^d$, the $n$-th moment of $\mu$ is the real number
$\int_{I^d} x^n \, d\mu(x)$, the integral over the closed unit cube $I^d = [0,1]^d$ of the
monomial $x^n = \prod_{i=1}^{d} x_i^{n_i}$, taken to be $0$ when the monomial is not
$\mu$-integrable on $I^d$. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- **Multi-index binomial coefficient.** For multi-indices $n, k \in \mathbb{N}^d$, the
binomial coefficient $\binom{n}{k}$ is the natural number $\prod_{i=1}^{d} \binom{n_i}{k_i}$. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- **Iterated backward difference of a multi-sequence.** For a function
$a : \mathbb{N}^d \to \mathbb{R}$ and multi-indices $k, n \in \mathbb{N}^d$,
$$(\Delta^k a)_n = \sum_{j \le k} (-1)^{|k| - |j|} \binom{k}{j} \, a_{n - j},$$
where $j$ runs over the multi-indices with $j_i \le k_i$ for every $i$, $|k| = \sum_i k_i$,
$\binom{k}{j} = \prod_i \binom{k_i}{j_i}$ is the multi-index binomial coefficient, and $n - j$
is taken coordinatewise, with $n_i - j_i$ replaced by $0$ when $j_i > n_i$.

When $k \le n$ coordinatewise, $\Delta^k$ is the composite of $k_i$ applications of
$(\Delta_i a)_n = a_{n - e_i} - a_n$ in each coordinate $i$, where $e_i$ is the $i$-th unit
multi-index. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- **Uniformly absolutely continuous measures.** A measure $\mu$ on $\mathbb{R}^d$ is uniformly
absolutely continuous with respect to a measure $\nu$ on $\mathbb{R}^d$ if there is a real
constant $C \ge 0$ with $\mu(S) \le C \, \nu(S)$ for every measurable set $S$.

When $\nu$ is $\sigma$-finite, this says that $\mu$ has an essentially bounded Radon–Nikodym
density with respect to $\nu$. -/
def UniformlyAbsolutelyContinuous {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℝ≥0, μ ≤ C • ν

/- **Absolute continuity criterion (Hausdorff moment problem).** A positive
probability measure `μ` on the cube is uniformly absolutely continuous w.r.t.
Lebesgue measure iff there is `C` with `(Δᵏμ)ₙ ≤ C·(Δᵏν)ₙ` for all `k ≤ n`. -/
/-- **Hausdorff's absolute continuity criterion.** Let $\mu$ be a probability measure on
$\mathbb{R}^d$ with $\mu(\mathbb{R}^d \setminus I^d) = 0$, where $I^d = [0,1]^d$ is the closed
unit cube, and let $\lambda$ be Lebesgue measure restricted to $I^d$. For a measure $\rho$ write
$m_\rho(n) = \int_{I^d} x^n \, d\rho(x)$ for its moments, indexed by multi-indices
$n \in \mathbb{N}^d$. Then $\mu$ is uniformly absolutely continuous with respect to $\lambda$ if
and only if there is a real constant $C$ such that
$(\Delta^k m_\mu)_n \le C \, (\Delta^k m_\lambda)_n$ for all multi-indices $k \le n$
(coordinatewise), where $\Delta^k$ is the iterated backward difference.

Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*. Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_absolute_continuity`. -/
public theorem_wanted hausdorff_absolute_continuity {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube d))) k n

end Analysis.HausdorffAbsoluteContinuity

end MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
