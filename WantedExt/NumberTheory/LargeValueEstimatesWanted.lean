/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# New large value estimates for Dirichlet polynomials

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.LargeValueEstimates` — annals_large_value_estimates (manifest `manifests/problems/annals_large_value_estimates.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.LargeValueEstimatesWanted` namespace. Mathematical
statements are unchanged. Source: L. Guth and J. Maynard, `New large value estimates for Dirichlet polynomials`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-LargeValueEstimates.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.LargeValueEstimatesWanted
/-!
# Main Statement from New large value estimates for Dirichlet polynomials

We formalise the statement of the main result from L. Guth and J. Maynard,
`New large value estimates for Dirichlet polynomials`, Annals of Math, 203 (2) 2026.
-/

set_option autoImplicit false

namespace LargeValueEstimates

open Asymptotics Complex

/-- **The Guth–Maynard large values bound.** For a natural number $N$ and real numbers $V$ and
$T$, this is the real number $N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}$, the factor
multiplying $T^{o(T)}$ on the right-hand side of the Guth–Maynard large values estimate for
Dirichlet polynomials. Here $V^{-2}$ and $V^{-4}$ are read as $0$ when $V = 0$. -/
noncomputable def bound (N : ℕ) (V T : ℝ) : ℝ :=
  N ^ 2 * V ^ (- 2 : ℤ) + N ^ (18 / 5 : ℝ) * V ^ (- 4 : ℤ) + T * N ^ (12 / 5 : ℝ) * V ^ (- 4 : ℤ)

/--
**Guth–Maynard large values estimate.** There is a function $o : \mathbb{R} \to \mathbb{R}$
with $o(T) \to 0$ as $T \to \infty$ such that the following holds. Let $(b_n)_{n \ge 0}$ be
complex numbers with $|b_n| \le 1$ for all $n$, let $N \ge 1$ and $R$ be natural numbers,
let $V > 0$ and $T > 1$ be real numbers, and let $t_0, \dots, t_{R-1}$ be points of $[0, T]$
with $|t_r - t_s| \ge 1$ whenever $r \ne s$. Suppose that, with $i$ the imaginary unit,

$$\left|\sum_{n=N}^{2N} b_n n^{i t_r}\right| \ge V$$

for every $r < R$. Then

$$R \le T^{o(T)} \left(N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}\right).$$

The hypotheses $N \ge 1$, $V > 0$ and $T > 1$ are not stated in the paper; the inequality may
be false at $T = 1$.

Source: L. Guth and J. Maynard, `New large value estimates for Dirichlet polynomials`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-LargeValueEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_large_value_estimates`.
-/
public theorem_wanted theorem_1_1 : ∃ o : ℝ → ℝ, o =o[Filter.atTop] (1 : ℝ → ℝ) ∧
    ∀ (b : ℕ → ℂ) (_hb : ∀ n, ‖b n‖ ≤ 1) (N : ℕ) (V : ℝ) (T : ℝ) (R : ℕ) (t : Fin R → ℝ),
    N > 0 → V > 0 → T > 1 → -- these assumptions are necessary but not stated in the paper
    (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
    (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
    R ≤ T ^ (o T) * bound N V T

end LargeValueEstimates

end MathlibExt.NumberTheory.LargeValueEstimatesWanted
