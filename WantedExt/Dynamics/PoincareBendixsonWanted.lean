/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Poincaré–Bendixson theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.PoincareBendixson` — poincare_bendixson (manifest `manifests/problems/poincare_bendixson.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.PoincareBendixsonWanted` namespace. Mathematical
statements are unchanged. Source: H. Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, Journal de Mathématiques 7 (1881), 8 (1882), 1 (1885), 2 (1886); I. Bendixson, *Sur les courbes définies par des équations différentielles*, Acta Mathematica 24 (1901), 1-88. Listed as §63 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). The Isabelle/HOL/AFP entry by Fabian Immler and Yong Kiam Tan (https://www.isa-afp.org/entries/Poincare_Bendixson.html) uses John Harrison's Jordan curve theorem.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.PoincareBendixsonWanted
namespace Dynamics

/-!
# Poincaré–Bendixson theorem

§63 of Knill's *Some Fundamental Theorems in Mathematics*. For a `C¹`
autonomous vector field `F : ℝ² → ℝ²` and a forward integral curve `γ`
on `[0, ∞)`, one of three alternatives holds: the forward orbit is
unbounded; the ω-limit set `⋂ s, closure (γ '' [s, ∞))` contains an
equilibrium of `F`; or the ω-limit set equals the range of a
non-constant periodic integral curve of `F`.

The bounded branch uses "ω-limit contains an equilibrium" rather than
"γ converges to an equilibrium": planar orbits in a bounded forward-
invariant region may accumulate on continua of equilibria or polycycles
without converging to any single point. The non-degeneracy `F (β 0) ≠ 0`
excludes a constant equilibrium curve from vacuously satisfying the
periodic branch. The periodic-branch conclusion is range-of-periodic-
orbit; "limit cycle" in the strict sense (isolated, attracting nearby
trajectories) is not asserted.
-/

open Filter Topology Set

/-- **The Euclidean plane.** The ambient space is the plane $\mathbb{R}^2$ with its Euclidean
inner product and norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/- **Poincaré–Bendixson theorem.** For a `C¹` autonomous vector field
`F : ℝ² → ℝ²` and a forward integral curve `γ` on `[0, ∞)`, either the
forward orbit is unbounded, or the ω-limit set contains an equilibrium
of `F`, or the ω-limit set equals the range of a non-constant periodic
integral curve of `F`. -/
/-- **Poincaré–Bendixson theorem.** Let $F \colon \mathbb{R}^2 \to \mathbb{R}^2$ be a continuously
differentiable vector field on the Euclidean plane, and let
$\gamma \colon \mathbb{R} \to \mathbb{R}^2$ be a curve such that for every $t \ge 0$ the derivative
of $\gamma$ at $t$ within $[0, \infty)$ is $F(\gamma(t))$. Let
$\omega(\gamma) = \bigcap_{s \in \mathbb{R}} \overline{\gamma([s, \infty))}$ be the $\omega$-limit
set of $\gamma$. Then at least one of the following holds: the forward orbit
$\gamma([0, \infty))$ is unbounded; $\omega(\gamma)$ contains a point $x_0$ with $F(x_0) = 0$; or
there are a real number $T > 0$ and a curve $\beta \colon \mathbb{R} \to \mathbb{R}^2$ with
$\beta'(t) = F(\beta(t))$ and $\beta(t + T) = \beta(t)$ for every real $t$ and with
$F(\beta(0)) \ne 0$, such that $\omega(\gamma)$ equals the range of $\beta$.

Source: H. Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, Journal de Mathématiques 7 (1881), 8 (1882), 1 (1885), 2 (1886); I. Bendixson, *Sur les courbes définies par des équations différentielles*, Acta Mathematica 24 (1901), 1-88. Listed as §63 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). The Isabelle/HOL/AFP entry by Fabian Immler and Yong Kiam Tan (https://www.isa-afp.org/entries/Poincare_Bendixson.html) uses John Harrison's Jordan curve theorem. Via leanprover/lean-eval@38361be, problem `poincare_bendixson`. -/
public theorem_wanted poincare_bendixson
    (F : Plane → Plane) (_hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane)
    (_hγ : IsIntegralCurveOn γ (fun _ x => F x) (Set.Ici 0)) :
    ¬ Bornology.IsBounded (γ '' Set.Ici 0)
    ∨ (∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s))
    ∨ (∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x => F x) ∧
        (∀ t, β (t + T) = β t) ∧
        F (β 0) ≠ 0 ∧
        (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β)

end Dynamics

end MathlibExt.Dynamics.PoincareBendixsonWanted
