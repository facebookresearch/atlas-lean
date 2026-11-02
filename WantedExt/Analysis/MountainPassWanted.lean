/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mountain Pass Theorem (Ambrosetti–Rabinowitz 1973)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.MountainPass` — mountain_pass (manifest `manifests/problems/mountain_pass.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.MountainPassWanted` namespace. Mathematical
statements are unchanged. Source: A. Ambrosetti and P.H. Rabinowitz, 'Dual variational methods in critical point theory and applications', J. Funct. Anal. 14 (1973) 349–381. Listed as §119 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.MountainPassWanted
namespace Analysis
namespace MountainPassProblem

/-!
# Mountain Pass Theorem (Ambrosetti–Rabinowitz 1973)

A `C¹` functional `f` on a real Banach space `E` satisfying the
Palais–Smale compactness condition and having a *mountain range*
geometry separating two points `a, b` admits a critical point at the
mini-max level `c = inf_γ sup_t f(γ t)`, and `c ≥ ε > 0`.
Ambrosetti–Rabinowitz 1973. The statement is listed as §119 in Knill's
*Some Fundamental Theorems in Mathematics*.

Knill writes the far point condition as "`f(b) ≤ 0` for some `|b| > ε`".
The radius of the sphere is `r`, not `ε`, so `|b| > ε` is a
transcription slip for `r < ‖b − a‖`. The faithful condition encoded
here is the translated Ambrosetti–Rabinowitz geometry: `f a = 0`,
`f ≥ ε` on `Metric.sphere a r`, and `r < ‖b − a‖`.
-/

open scoped unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Critical point.** Let $E$ be a real Banach space and $f : E \to \mathbb{R}$. A point
$x \in E$ is a critical point of $f$ when the Fréchet derivative of $f$ at $x$ vanishes,
$f'(x) = 0$. Here $f'(x)$ is taken to be $0$ when $f$ is not differentiable at $x$, so such
points are critical as well. -/
def IsCriticalPoint (f : E → ℝ) (x : E) : Prop :=
  fderiv ℝ f x = 0

/-- **Palais–Smale condition.** Let $E$ be a real Banach space. A function $f : E \to \mathbb{R}$
satisfies the Palais–Smale condition when every sequence $(u_k)$ in $E$ such that $(f(u_k))$ is
bounded and the Fréchet derivatives $f'(u_k)$ tend to $0$ in operator norm has a subsequence
converging in $E$. Here $f'(x)$ is taken to be $0$ at points where $f$ is not differentiable. -/
def PalaisSmale (f : E → ℝ) : Prop :=
  ∀ u : ℕ → E, (∃ M : ℝ, ∀ k, |f (u k)| ≤ M) →
      Filter.Tendsto (fun k => fderiv ℝ f (u k)) Filter.atTop (nhds 0) →
      ∃ (x : E) (φ : ℕ → ℕ), StrictMono φ ∧
        Filter.Tendsto (u ∘ φ) Filter.atTop (nhds x)

/-- **Mountain range.** Let $E$ be a real Banach space, $f : E \to \mathbb{R}$, $a, b \in E$ and
$\varepsilon, r \in \mathbb{R}$. The points $a$ and $b$ are separated by a mountain range of $f$
at height $\varepsilon$ and radius $r$ when $f(a) = 0$, $\varepsilon > 0$, $r > 0$,
$f(y) \ge \varepsilon$ for every $y \in E$ with $\|y - a\| = r$, $\|b - a\| > r$ and
$f(b) \le 0$. -/
def MountainRange (f : E → ℝ) (a b : E) (ε r : ℝ) : Prop :=
  f a = 0 ∧ 0 < ε ∧ 0 < r ∧
    (∀ y ∈ Metric.sphere a r, ε ≤ f y) ∧ r < ‖b - a‖ ∧ f b ≤ 0

/-- **Mountain pass level.** Let $E$ be a real Banach space, $f : E \to \mathbb{R}$ and
$a, b \in E$. The mountain pass level of $f$ between $a$ and $b$ is
$$
c = \inf_{\gamma} \sup_{t \in [0, 1]} f(\gamma(t)),
$$
the infimum taken over all continuous paths $\gamma : [0, 1] \to E$ with $\gamma(0) = a$ and
$\gamma(1) = b$. Suprema and infima are taken in $\mathbb{R}$, where a family that is unbounded
on the relevant side has supremum or infimum $0$ by convention. -/
noncomputable def mountainPassLevel (f : E → ℝ) (a b : E) : ℝ :=
  ⨅ γ : Path a b, ⨆ t : I, f (γ t)

/- **Mountain Pass Theorem** (Ambrosetti–Rabinowitz 1973). A `C¹`
functional on a real Banach space satisfying Palais–Smale with mountain
range geometry has a critical point at the mini-max level
`c ≥ ε > 0`. -/
/-- **Mountain pass theorem.** Let $E$ be a real Banach space and let $f : E \to \mathbb{R}$ be
continuously differentiable and satisfy the Palais–Smale condition. Let $a, b \in E$ and let
$\varepsilon, r$ be real numbers such that $a$ and $b$ are separated by a mountain range of $f$
at height $\varepsilon$ and radius $r$: $f(a) = 0$, $\varepsilon > 0$, $r > 0$,
$f(y) \ge \varepsilon$ for every $y$ with $\|y - a\| = r$, $\|b - a\| > r$ and $f(b) \le 0$.
Then the mountain pass level $c$ of $f$ between $a$ and $b$ satisfies $c \ge \varepsilon$, and
$f$ has a critical point $x$ with $f(x) = c$.

Source: A. Ambrosetti and P.H. Rabinowitz, 'Dual variational methods in critical point theory and applications', J. Funct. Anal. 14 (1973) 349–381. Listed as §119 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `mountain_pass`. -/
public theorem_wanted mountain_pass (f : E → ℝ) (_hf : ContDiff ℝ 1 f) (_hps : PalaisSmale f)
    {a b : E} {ε r : ℝ} (_hmr : MountainRange f a b ε r) :
    ∃ x : E, IsCriticalPoint f x ∧
      f x = mountainPassLevel f a b ∧ ε ≤ mountainPassLevel f a b

end MountainPassProblem
end Analysis

end MathlibExt.Analysis.MountainPassWanted
