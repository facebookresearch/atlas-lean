/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kolmogorov–Arnold superposition theorem (non-universal Lorentz form)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.KolmogorovArnold` — kolmogorov_arnold_superposition (manifest `manifests/problems/kolmogorov_arnold_superposition.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.KolmogorovArnoldWanted` namespace. Mathematical
statements are unchanged. Source: A. N. Kolmogorov, *On the representation of continuous functions of several variables by superposition of continuous functions of one variable and addition*, Doklady Akad. Nauk SSSR 114 (1957), 953-956. V. I. Arnold, *On functions of three variables*, Doklady Akad. Nauk SSSR 114 (1957), 679-681. G. G. Lorentz, *Metric entropy, widths, and superpositions of functions*, Amer. Math. Monthly 69 (1962), 469-485 (single-outer-function refinement). Listed as §80 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.KolmogorovArnoldWanted
namespace Analysis

/-!
# Kolmogorov–Arnold superposition theorem (non-universal existence form)

For every continuous `f` on the unit cube `[0, 1]ⁿ` (with `n ≥ 1`),
there exist continuous one-variable inner functions `φ_{k,l} : ℝ → ℝ`
and a single continuous outer function `g : ℝ → ℝ` such that

  `f(x₁, …, xₙ) = ∑_{k=0}^{2n} g(∑_{l=1}^{n} φ_{k,l}(x_l))`.

This is the Lorentz (1962) single-outer-function form. Both `g` and the
`φ_{k,l}` are allowed to depend on `f` — weaker than the universal-
inner-functions formulation, since here the inner functions may depend
on `f`. The two-variable function used to combine the layers is just
addition, resolving the continuous form of Hilbert's 13th problem.

The inner and outer functions are stated as globally continuous maps
`ℝ → ℝ`. This is a harmless strengthening of versions stated on
compact subsets: the inner functions are only evaluated on `[0, 1]`,
and the outer function is only evaluated on the compact set of inner
sums, so Tietze extension gives global continuous representatives.
-/

open scoped BigOperators

/- **Kolmogorov–Arnold superposition theorem (non-universal Lorentz
form).** For `n ≥ 1`, every continuous `f` on the unit cube `[0, 1]ⁿ`
admits a representation
`f(x) = ∑_{k=0}^{2n} g(∑_{l=1}^{n} φ_{k,l}(x_l))` with a single
continuous outer function `g : ℝ → ℝ` and continuous inner functions
`φ_{k,l} : ℝ → ℝ`. -/
/-- **Kolmogorov–Arnold superposition with a single outer function.** Let $n \ge 1$ and let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuous on the unit cube $[0, 1]^n$. Then there exist a
continuous function $g : \mathbb{R} \to \mathbb{R}$ and continuous functions
$\varphi_{k,l} : \mathbb{R} \to \mathbb{R}$ for $0 \le k \le 2n$ and $0 \le l < n$ such that for
every $x = (x_0, \dots, x_{n-1}) \in [0, 1]^n$,

$$f(x) = \sum_{k=0}^{2n} g\left(\sum_{l=0}^{n-1} \varphi_{k,l}(x_l)\right).$$

Both $g$ and the $\varphi_{k,l}$ may depend on $f$, so this is weaker than the form in which the
inner functions are universal.

Source: A. N. Kolmogorov, *On the representation of continuous functions of several variables by superposition of continuous functions of one variable and addition*, Doklady Akad. Nauk SSSR 114 (1957), 953-956. V. I. Arnold, *On functions of three variables*, Doklady Akad. Nauk SSSR 114 (1957), 679-681. G. G. Lorentz, *Metric entropy, widths, and superpositions of functions*, Amer. Math. Monthly 69 (1962), 469-485 (single-outer-function refinement). Listed as §80 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `kolmogorov_arnold_superposition`. -/
public theorem_wanted kolmogorov_arnold (n : ℕ) (_hn : 1 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (_hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l))

end Analysis

end MathlibExt.Analysis.KolmogorovArnoldWanted
