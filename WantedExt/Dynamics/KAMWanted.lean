/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KAM persistence of an invariant curve

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.KAM` — kam_invariant_curve (manifest `manifests/problems/kam_invariant_curve.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.KAMWanted` namespace. Mathematical
statements are unchanged. Source: A. N. Kolmogorov (1954); V. I. Arnold (1963); J. Moser, *On invariant curves of area-preserving mappings of an annulus*, Nachr. Akad. Wiss. Göttingen (1962). Knill, *Some fundamental theorems in mathematics*, §83.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.KAMWanted
namespace Dynamics

/-!
# KAM persistence of an invariant curve of a twist map

`kam_invariant_curve` is the Kolmogorov–Arnold–Moser theorem in the
twist-map setting: for Diophantine rotation number `α` and a real-analytic,
`1`-periodic, non-constant, mean-zero `f`, the invariant curve `q₀(t) = t` of
the integrable case `c = 0` persists, for small `|c|`, as a smooth strictly
increasing solution `q` (with `q − id` periodic) of the functional equation
`q(t+α) − 2q(t) + q(t−α) = c·f(q(t))`.

The linearisation at `c = 0` is not invertible (`L̂₀ = 0`), so the implicit
function theorem fails and one faces small divisors `[2cos(2πnα)−2]⁻¹`; the
Diophantine condition makes the Newton/Nash–Moser scheme converge. The trusted
helper `IsDiophantine` (a non-hole) fixes the arithmetic condition. Mathlib has
no KAM theory (no twist maps, invariant curves, small divisors, or Nash–Moser).

This is a category-(b) candidate from §83 of the Knill survey
(`sections/083-kam.md`). (The Poincaré–Siegel linearisation companion is not
included here.)
-/

open scoped ContDiff

/-- **Diophantine number.** A real number $\alpha$ is Diophantine (with exponent $2$, as used in
KAM theory) if there is $C > 0$ such that $C / q^2 \le |\alpha - p/q|$ for all integers $p$ and
$q$ with $q \neq 0$. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p q : ℤ, q ≠ 0 →
    C / (q : ℝ) ^ 2 ≤ |α - (p : ℝ) / (q : ℝ)|

/- **KAM theorem (persistence of an invariant curve).** For real-analytic,
`1`-periodic, non-constant, mean-zero `f` and Diophantine `α`, for all small
`|c|` the twist-map functional equation
`q(t+α) − 2q(t) + q(t−α) = c·f(q(t))` has a smooth strictly increasing solution
`q` with `q − id` periodic — the `c = 0` curve `q₀(t) = t` persists as a smooth
invariant curve of rotation number `α`. -/
/-- **KAM theorem for twist maps (persistence of an invariant curve).** Let $\alpha$ be a
Diophantine real number and let $f : \mathbb{R} \to \mathbb{R}$ be real-analytic, $1$-periodic and
not constant, with $\int_0^1 f(x)\,dx = 0$. Then there is $c_0 > 0$ such that for every real $c$
with $|c| < c_0$ there is a $C^\infty$, strictly increasing function $q : \mathbb{R} \to \mathbb{R}$
such that $t \mapsto q(t) - t$ is $1$-periodic and, for every real $t$,

$$q(t + \alpha) - 2q(t) + q(t - \alpha) = c\, f(q(t)).$$

Source: A. N. Kolmogorov (1954); V. I. Arnold (1963); J. Moser, *On invariant curves of area-preserving mappings of an annulus*, Nachr. Akad. Wiss. Göttingen (1962). Knill, *Some fundamental theorems in mathematics*, §83. Via leanprover/lean-eval@38361be, problem `kam_invariant_curve`. -/
public theorem_wanted kam_invariant_curve
    (α : ℝ) (_hα : IsDiophantine α)
    (f : ℝ → ℝ)
    (_hf_analytic : AnalyticOnNhd ℝ f Set.univ)
    (_hf_per : Function.Periodic f 1)
    (_hf_nonconst : ¬ ∃ k : ℝ, ∀ x, f x = k)
    (_hf_mean : ∫ x in (0 : ℝ)..1, f x = 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, |c| < c₀ →
      ∃ q : ℝ → ℝ,
        ContDiff ℝ ∞ q ∧ StrictMono q ∧
        Function.Periodic (fun t => q t - t) 1 ∧
        ∀ t : ℝ, q (t + α) - 2 * q t + q (t - α) = c * f (q t)

end Dynamics

end MathlibExt.Dynamics.KAMWanted
