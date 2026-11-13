/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cauchy–Kovalevskaya theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.CauchyKovalevskaya` — cauchy_kovalevskaya (manifest `manifests/problems/cauchy_kovalevskaya.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.CauchyKovalevskayaWanted` namespace. Mathematical
statements are unchanged. Source: A.-L. Cauchy (1842) and S. Kovalevskaya (1875). Listed as §32 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.CauchyKovalevskayaWanted
namespace Analysis

/-!
# Cauchy–Kovalevskaya theorem

§32 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For
analytic data `F`, `f`, `u₀`, the quasi-linear scalar Cauchy problem

  `uₜ(x, t) = F(x, t, u(x,t)) · ∇ₓu(x, t) + f(x, t, u(x, t))`,
  `u(x, 0) = u₀(x)`

has a unique local analytic solution near every point of the initial
hypersurface `t = 0`.

The statement uses only off-the-shelf mathlib (`AnalyticOnNhd`, `fderiv`,
`EuclideanSpace`); mathlib has no Cauchy–Kovalevskaya theorem. The PDE is
encoded through the Fréchet derivative: `fderiv ℝ u p (0, 1)` is `∂u/∂t`
and `fderiv ℝ u p (v, 0)` is the spatial directional derivative along `v`,
so `fderiv ℝ u p (F-data, 0)` is `F · ∇ₓu`. Locality and uniqueness are
folded into a single `∀ x₀, ∃ U …` statement.
-/

open Set

/-- **Model space $\mathbb{R}^d$ of the Cauchy–Kovalevskaya problem.** For a natural number $d$,
this is the real Euclidean space $\mathbb{R}^d$ of dimension $d$, with the Euclidean inner product
and norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/- **Cauchy–Kovalevskaya theorem.** For analytic data `F`, `f`, `u₀`, the
quasi-linear Cauchy problem

  `uₜ(x, t) = F(x, t, u(x,t)) · ∇ₓu(x, t) + f(x, t, u(x, t))`,
  `u(x, 0) = u₀(x)`

has a unique local analytic solution: for every `x₀ ∈ ℝᵈ` there is an open
neighborhood `U` of `(x₀, 0)` and an analytic function `u : E d × ℝ → ℝ`
satisfying the PDE and the initial condition on `U`, and `u` is unique among
analytic functions on `U` with the same initial data. -/
/-- **Cauchy–Kovalevskaya theorem.** Let $d$ be a natural number, write $\mathbb{R}^d$ for real
Euclidean $d$-space, and let $F : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to
\mathbb{R}^d$, $f : \mathbb{R}^d \times \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and
$u_0 : \mathbb{R}^d \to \mathbb{R}$ be real analytic at every point. Then for every
$x_0 \in \mathbb{R}^d$ there are an open set $U \subseteq \mathbb{R}^d \times \mathbb{R}$
containing $(x_0, 0)$ and a function $u : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$, real
analytic on $U$, such that $u(x, 0) = u_0(x)$ whenever $(x, 0) \in U$ and

$$\partial_t u(x, t) = F(x, t, u(x, t)) \cdot \nabla_x u(x, t) + f(x, t, u(x, t))$$

for every $(x, t) \in U$, where $\partial_t u$ is the partial derivative of $u$ in $t$ and
$\nabla_x u$ is its gradient in $x$. Moreover, every function
$v : \mathbb{R}^d \times \mathbb{R} \to \mathbb{R}$ that is real analytic on $U$, satisfies
$v(x, 0) = u_0(x)$ whenever $(x, 0) \in U$, and satisfies the same equation at every point of
$U$ agrees with $u$ on $U$.

Source: A.-L. Cauchy (1842) and S. Kovalevskaya (1875). Listed as §32 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `cauchy_kovalevskaya`. -/
public theorem_wanted cauchy_kovalevskaya {d : ℕ}
    (F : E d × ℝ × ℝ → E d) (f : E d × ℝ × ℝ → ℝ) (u₀ : E d → ℝ)
    (_hF : AnalyticOnNhd ℝ F univ) (_hf : AnalyticOnNhd ℝ f univ)
    (_hu₀ : AnalyticOnNhd ℝ u₀ univ) (x₀ : E d) :
    ∃ (U : Set (E d × ℝ)) (u : E d × ℝ → ℝ),
      (x₀, (0 : ℝ)) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℝ u U ∧
      (∀ x : E d, (x, (0 : ℝ)) ∈ U → u (x, 0) = u₀ x) ∧
      (∀ p ∈ U,
        fderiv ℝ u p ((0 : E d), (1 : ℝ)) =
          fderiv ℝ u p (F (p.1, p.2, u p), (0 : ℝ)) + f (p.1, p.2, u p)) ∧
      (∀ v : E d × ℝ → ℝ, AnalyticOnNhd ℝ v U →
        (∀ x : E d, (x, (0 : ℝ)) ∈ U → v (x, 0) = u₀ x) →
        (∀ p ∈ U,
          fderiv ℝ v p ((0 : E d), (1 : ℝ)) =
            fderiv ℝ v p (F (p.1, p.2, v p), (0 : ℝ)) + f (p.1, p.2, v p)) →
        ∀ p ∈ U, u p = v p)

end Analysis

end MathlibExt.Analysis.CauchyKovalevskayaWanted
