/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bourgain's polynomial ergodic theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.BourgainErgodic` — bourgain_polynomial_ergodic (manifest `manifests/problems/bourgain_polynomial_ergodic.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.BourgainErgodicWanted` namespace. Mathematical
statements are unchanged. Source: J. Bourgain, *Pointwise ergodic theorems for arithmetic sets*, Publ. Math. IHÉS 69 (1989). Knill, *Some fundamental theorems in mathematics*, §173.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.BourgainErgodicWanted
namespace Dynamics.BourgainErgodic

/-!
# Bourgain's polynomial ergodic theorem

`bourgain_polynomial_ergodic`: for every integer-polynomial iterate sequence and
every `L^p` (`p > 1`) function, the polynomial ergodic averages
`(1/n) ∑_{k<n} f(T^[a k] x)` converge pointwise almost everywhere. Trusted
helpers (`IsIntegerPolynomialSequence`, `polynomialErgodicAverage`) are
non-holes. Mathlib has Birkhoff's ergodic theorem but not Bourgain's polynomial
extension. Category-(b) candidate from §173 of the Knill survey.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Integer polynomial sequences.** A sequence $a : \mathbb{N} \to \mathbb{N}$ is an integer
polynomial sequence if there is a polynomial $P$ with integer coefficients such that
$P(n) \ge 0$ and $a(n) = P(n)$ for every $n \in \mathbb{N}$. -/
def IsIntegerPolynomialSequence (a : ℕ → ℕ) : Prop :=
  ∃ P : Polynomial ℤ,
    ∀ n : ℕ, 0 ≤ P.eval (n : ℤ) ∧ a n = Int.toNat (P.eval (n : ℤ))

/-- **Polynomial ergodic averages.** Given a sequence $a : \mathbb{N} \to \mathbb{N}$, a map
$T : X \to X$, a function $f : X \to \mathbb{R}$, $n \in \mathbb{N}$ and $x \in X$, the $n$-th
polynomial ergodic average of $f$ at $x$ is

$$\frac{1}{n} \sum_{k=0}^{n-1} f\bigl(T^{a(k)}(x)\bigr),$$

where $T^{a(k)}$ is the $a(k)$-fold iterate of $T$; for $n = 0$ the average is $0$. -/
noncomputable def polynomialErgodicAverage (a : ℕ → ℕ) (T : X → X) (f : X → ℝ)
    (n : ℕ) (x : X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, f (T^[a k] x)

/- Bourgain's polynomial ergodic theorem: for every integer-polynomial
iterate sequence and every `L^p`, `p > 1`, function, the polynomial ergodic
averages converge pointwise almost everywhere. -/
/-- **Bourgain's polynomial ergodic theorem.** Let $(X, \mu)$ be a probability space, let
$T : X \to X$ be a measure-preserving map, let $a : \mathbb{N} \to \mathbb{N}$ be an integer
polynomial sequence, and let $f : X \to \mathbb{R}$ be a function in $L^p(\mu)$ for some
$p$ with $1 < p < \infty$. Then there is a function $F : X \to \mathbb{R}$ such that for
$\mu$-almost every $x \in X$ the polynomial ergodic averages
$\frac{1}{n} \sum_{k=0}^{n-1} f(T^{a(k)}(x))$, $n \ge 1$, where $T^{a(k)}$ is the $a(k)$-fold
iterate of $T$, converge to $F(x)$ as $n \to \infty$.

Source: J. Bourgain, *Pointwise ergodic theorems for arithmetic sets*, Publ. Math. IHÉS 69 (1989). Knill, *Some fundamental theorems in mathematics*, §173. Via leanprover/lean-eval@38361be, problem `bourgain_polynomial_ergodic`. -/
public theorem_wanted bourgain_polynomial_ergodic
    [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 < p) (hp_ne_top : p ≠ ∞)
    {T : X → X} (hT : MeasurePreserving T μ μ)
    {a : ℕ → ℕ} (ha : IsIntegerPolynomialSequence a)
    {f : X → ℝ} (hf : MemLp f p μ) :
    ∃ F : X → ℝ,
      ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => polynomialErgodicAverage a T f (n + 1) x) atTop (𝓝 (F x))

end Dynamics.BourgainErgodic

end MathlibExt.Dynamics.BourgainErgodicWanted
