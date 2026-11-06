/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hausdorff–Hildebrandt–Schoenberg moment theorem, The Hausdorff positivity (complete-monotonicity) criterion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffMoments` — hausdorff_hildebrandt_schoenberg (manifest `manifests/problems/hausdorff_hildebrandt_schoenberg.toml`, rev 1, submitter Kim Morrison, status archived); hausdorff_positivity_criterion (manifest `manifests/problems/hausdorff_positivity_criterion.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffMomentsWanted` namespace. Mathematical
statements are unchanged. Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On linear functional operations and the moment problem for a finite interval in one or several dimensions*, Ann. of Math. 34 (1933). Knill, *Some fundamental theorems in mathematics*, §115. F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921). Knill, *Some fundamental theorems in mathematics*, §115.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.HausdorffMomentsWanted
namespace Analysis

/-!
# The Hausdorff moment problem on the cube

`hausdorff_hildebrandt_schoenberg` is the Hausdorff–Hildebrandt–Schoenberg
theorem (1933): a multi-indexed real sequence is the moment sequence of a
signed bounded-variation Borel measure on the unit cube `Iᵈ = [0,1]ᵈ` iff it is
*Hausdorff bounded*. `hausdorff_positivity` is the Hausdorff positivity
criterion (1921): it comes from a *positive* finite measure iff it is completely
monotone (all iterated backward differences nonnegative).

A signed bounded-variation measure is encoded by its Jordan decomposition (a
difference of two finite positive measures); the moment integrals are taken over
the cube, so only the restriction to `Iᵈ` matters; the iterated backward
difference `Δᵏ` is given in closed form (the `ℕ`-subtraction `n − j` is genuine
in the `k ≤ n` regime the criteria use).

Mathlib has `SignedMeasure`, Jordan decomposition, finite measures, and set
integrals — enough to *state* the theorem — but no moment-problem machinery
(no Hausdorff/Hamburger/Stieltjes moment problem, no completely-monotone
sequences). The helper definitions below (`cube`, `monomial`, `momentOf`,
`IsMomentConfiguration`, `multiChoose`, `diff`, `HausdorffBounded`,
`IsPositiveMomentConfiguration`) are trusted (non-holes).

These are category-(b) candidates from §115 of the Knill survey
(`sections/115-moments.md`).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- **Unit cube of the Hausdorff moment problem.** For $d \in \mathbb{N}$, the closed unit cube
$I^d = [0,1]^d$ is the set of points $x \in \mathbb{R}^d$ with $0 \le x_i \le 1$ for every
coordinate $i$. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- **Multi-index monomial.** For a multi-index $n \in \mathbb{N}^d$, the monomial $x^n$ is the
real function on $\mathbb{R}^d$ given by $x^n = \prod_i x_i^{n_i}$. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, (x i) ^ (n i)

/-- **Moments on the unit cube.** For a measure $\mu$ on $\mathbb{R}^d$ and a multi-index
$n \in \mathbb{N}^d$, the $n$-th moment of $\mu$ on the unit cube is the real number
$\int_{[0,1]^d} x^n \, d\mu(x)$, where $x^n = \prod_i x_i^{n_i}$.

When $x^n$ is not $\mu$-integrable on $[0,1]^d$, this integral is taken to be $0$. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- **Moment sequences of signed measures on the cube.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a moment configuration if there are finite measures $\mu$ and $\nu$ on
$\mathbb{R}^d$ such that for every multi-index $n \in \mathbb{N}^d$,
$$a_n = \int_{[0,1]^d} x^n \, d\mu(x) - \int_{[0,1]^d} x^n \, d\nu(x),$$
where $x^n = \prod_i x_i^{n_i}$.

This encodes a signed measure of bounded variation on the cube by its Jordan decomposition
$\mu - \nu$. -/
def IsMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
    ∀ n, a n = momentOf μ n - momentOf ν n

/-- **Multi-index binomial coefficient.** For multi-indices $n, k \in \mathbb{N}^d$, the binomial
coefficient $\binom{n}{k}$ is the natural number $\prod_i \binom{n_i}{k_i}$. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- **Iterated backward difference.** For a real sequence $a$ indexed by $\mathbb{N}^d$ and
multi-indices $k, n \in \mathbb{N}^d$, the iterated backward difference of $a$ is the real number
$$(\Delta^k a)_n = \sum_{j \le k} (-1)^{|k| - |j|} \binom{k}{j} a_{n - j},$$
where $j$ ranges over the multi-indices with $j \le k$ coordinatewise, $|j| = \sum_i j_i$,
$\binom{k}{j} = \prod_i \binom{k_i}{j_i}$, and $n - j$ is computed coordinatewise in $\mathbb{N}$,
with $n_i - j_i = 0$ when $j_i > n_i$.

For $k \le n$ no truncation occurs, and $\Delta^k a$ is the iterate of the backward partial
differences $(\Delta_i a)_n = a_{n - e_i} - a_n$, applied $k_i$ times in each coordinate $i$,
where $e_i \in \mathbb{N}^d$ is the $i$-th unit multi-index. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- **Hausdorff-bounded sequences.** A real sequence $a$ indexed by $\mathbb{N}^d$ is Hausdorff
bounded if there is a real constant $M$ such that for every multi-index $n \in \mathbb{N}^d$,
$$\sum_{k \le n} \left| \binom{n}{k} (\Delta^k a)_n \right| \le M,$$
where $k$ ranges over the multi-indices with $k \le n$ coordinatewise,
$\binom{n}{k} = \prod_i \binom{n_i}{k_i}$ is the multi-index binomial coefficient, and
$\Delta^k a$ is the iterated backward difference of $a$. -/
def HausdorffBounded {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : Fin d → ℕ,
    ∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C

/-- **Moment sequences of positive measures on the cube.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a positive moment configuration if there is a finite measure $\mu$ on
$\mathbb{R}^d$ such that $a_n = \int_{[0,1]^d} x^n \, d\mu(x)$ for every multi-index
$n \in \mathbb{N}^d$, where $x^n = \prod_i x_i^{n_i}$. -/
def IsPositiveMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ ∀ n, a n = momentOf μ n

/- **Hausdorff–Hildebrandt–Schoenberg theorem.** A multi-indexed real sequence
is the moment sequence of a signed bounded-variation measure on the unit cube
`Iᵈ` iff its moments are Hausdorff bounded. -/
/-- **Hausdorff–Hildebrandt–Schoenberg moment theorem.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a moment configuration, that is, there are finite measures $\mu$ and $\nu$ on
$\mathbb{R}^d$ with $a_n = \int_{[0,1]^d} x^n \, d\mu(x) - \int_{[0,1]^d} x^n \, d\nu(x)$ for every
multi-index $n \in \mathbb{N}^d$, where $x^n = \prod_i x_i^{n_i}$, if and only if $a$ is Hausdorff
bounded.

Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On linear functional operations and the moment problem for a finite interval in one or several dimensions*, Ann. of Math. 34 (1933). Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_hildebrandt_schoenberg`. -/
public theorem_wanted hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a

/- **Hausdorff positivity criterion** (Hausdorff 1921). A moment configuration
comes from a positive measure iff all its iterated backward differences are
nonnegative — i.e. the sequence is *completely monotone*: `(Δᵏa)ₙ ≥ 0` for all
`k ≤ n`. -/
/-- **Hausdorff positivity criterion.** A real sequence $a$ indexed by $\mathbb{N}^d$ is a positive
moment configuration, that is, there is a finite measure $\mu$ on $\mathbb{R}^d$ with
$a_n = \int_{[0,1]^d} x^n \, d\mu(x)$ for every multi-index $n \in \mathbb{N}^d$, where
$x^n = \prod_i x_i^{n_i}$, if and only if $(\Delta^k a)_n \ge 0$ for all multi-indices $k, n$ with
$k \le n$ coordinatewise, where $\Delta^k a$ is the iterated backward difference of $a$.

Source: F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921). Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_positivity_criterion`. -/
public theorem_wanted hausdorff_positivity {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔ ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n

end Analysis

end MathlibExt.Analysis.HausdorffMomentsWanted
