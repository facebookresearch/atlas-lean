/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Euler–Lagrange equation

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.EulerLagrange` — euler_lagrange_equation (manifest `manifests/problems/euler_lagrange_equation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.EulerLagrangeWanted` namespace. Mathematical
statements are unchanged. Source: L. Euler (1744) and J.-L. Lagrange (1755). Listed as §44 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.EulerLagrangeWanted
namespace Analysis

/-!
# Euler–Lagrange equation

§44 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (the additional
statement of the calculus-of-variations section). A sufficiently regular
stationary path `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt` satisfies
the Euler–Lagrange equation `∂L/∂x = (d/dt)(∂L/∂x')` pointwise on `(a, b)`.

mathlib has the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and neighbours), but it
has no notion of a variational extremum of an action functional and no
Euler–Lagrange theorem (`grep -i 'euler.*lagrange'` in mathlib finds nothing in
the analytic sense). Here a path is a variational extremum when the first
variation of the action vanishes against every smooth compactly supported
perturbation, and the conclusion is the classical pointwise equation for `C²`
data.
-/

open MeasureTheory Set
open scoped ContDiff

/-- **Partial derivative of the Lagrangian in position.** For a real function $L(t, y, v)$
of three real variables, a function $x : \mathbb{R} \to \mathbb{R}$ and a real number $t$, this
is the value $\frac{\partial L}{\partial y}(t, x(t), x'(t))$, the derivative at $y = x(t)$ of
the function $y \mapsto L(t, y, x'(t))$.

By convention, a derivative that does not exist is taken to be $0$, both for $x'(t)$ and for
the derivative in $y$. -/
noncomputable def lagrangianPartialX
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun y => L t y (deriv x t)) (x t)

/-- **Partial derivative of the Lagrangian in velocity.** For a real function $L(t, y, v)$
of three real variables, a function $x : \mathbb{R} \to \mathbb{R}$ and a real number $t$, this
is the value $\frac{\partial L}{\partial v}(t, x(t), x'(t))$, the derivative at $v = x'(t)$ of
the function $v \mapsto L(t, x(t), v)$.

By convention, a derivative that does not exist is taken to be $0$, both for $x'(t)$ and for
the derivative in $v$. -/
noncomputable def lagrangianPartialV
    (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun z => L t (x t) z) (deriv x t)

/-- **Variational extremum.** Let $a, b$ be real numbers and let $L(t, y, v)$
be a real function of three real variables. A function $x : \mathbb{R} \to \mathbb{R}$ is a
variational extremum of the action of $L$ on $(a, b)$ if $x$ is continuously differentiable and,
for every infinitely differentiable function $h : \mathbb{R} \to \mathbb{R}$ of compact support
whose closed support lies in the open interval $(a, b)$, the derivative at $\varepsilon = 0$ of
$$
\varepsilon \mapsto \int_{(a, b)}
L\big(t, x(t) + \varepsilon h(t), x'(t) + \varepsilon h'(t)\big)\,dt
$$
is $0$.

By convention, a derivative that does not exist is taken to be $0$, and so is the integral of a
function that is not integrable. -/
def IsVariationalExtremum
    (a b : ℝ) (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 x ∧
  ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
    tsupport h ⊆ Set.Ioo a b →
    deriv (fun ε : ℝ => ∫ t in Set.Ioo a b,
        L t (x t + ε * h t) (deriv x t + ε * deriv h t)) 0 = 0

/- **Euler–Lagrange equation** (§44). On an interval `a < b`, every `C²`
variational extremum `x` of the action `I(y) = ∫_a^b L(t, y(t), y'(t)) dt`, with
`C²` Lagrangian `L`, satisfies the pointwise equation
`∂L/∂x (t, x(t), x'(t)) = (d/dt)(∂L/∂x' (t, x(t), x'(t)))` on `(a, b)`. -/
/-- **Euler–Lagrange equation.** Let $a < b$ be real numbers, let $L(t, y, v)$ be a real function
of three real variables that is twice continuously differentiable on $\mathbb{R}^3$, and let
$x : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable. Write
$\partial L / \partial y$ and $\partial L / \partial v$ for the partial derivatives of $L$ in its
second and third arguments. If $x$ is a variational extremum of the action of $L$ on $(a, b)$,
then for every $t \in (a, b)$
$$
\frac{\partial L}{\partial y}(t, x(t), x'(t))
= \frac{d}{ds}\Big|_{s = t} \frac{\partial L}{\partial v}(s, x(s), x'(s)).
$$

Source: L. Euler (1744) and J.-L. Lagrange (1755). Listed as §44 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `euler_lagrange_equation`. -/
public theorem_wanted euler_lagrange_equation
    {a b : ℝ} (L : ℝ → ℝ → ℝ → ℝ) (x : ℝ → ℝ) (_hab : a < b)
    (_hL : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => L p.1 p.2.1 p.2.2))
    (_hx : ContDiff ℝ 2 x)
    (_hxe : IsVariationalExtremum a b L x) :
    ∀ t ∈ Set.Ioo a b,
      lagrangianPartialX L x t = deriv (lagrangianPartialV L x) t

end Analysis

end MathlibExt.Analysis.EulerLagrangeWanted
