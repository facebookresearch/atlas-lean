/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fáry–Milnor theorem (knot total curvature ≤ 4π implies unknotted)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.FaryMilnor` — fary_milnor (manifest `manifests/problems/fary_milnor.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.FaryMilnorWanted` namespace. Mathematical
statements are unchanged. Source: I. Fáry, 'Sur la courbure totale d'une courbe gauche faisant un nœud', Bull. Soc. Math. France 77 (1949) 128–138; J. Milnor, 'On the total curvature of knots', Ann. of Math. (2) 52 (1950) 248–257. §161 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.FaryMilnorWanted
namespace Geometry
namespace FaryMilnorProblem

/-!
# Fary–Milnor theorem

A smooth knot in `ℝ³` whose total curvature is at most `4π` is
unknotted. István Fáry (1949) and John Milnor (1950), independently.
§161 in Knill's *Some Fundamental Theorems in Mathematics*.

A knot is a smooth, regular, simple, `2π`-periodic curve `r : ℝ → ℝ³`,
simple on one half-open fundamental interval `[0, 2π)`. Its curvature
is `κ(t) = ‖r'(t) × r''(t)‖ / ‖r'(t)‖³`; total curvature is the
arc-length integral `∫₀^{2π} κ(t) · ‖r'(t)‖ dt`. Unknottedness is
encoded as a smooth isotopy through smooth (parametrised) knots from
`r` to the standard unit circle — every intermediate stage is itself a
smooth knot. By the smooth isotopy-extension theorem this is
classically equivalent to ambient isotopy of `ℝ³` (the form encoded by
the existing `LeanEval.KnotTheory.Prelude` `AmbientIsotopy`), but the
parametrised form is the natural data-level statement at this section.

Mathlib has `deriv`, interval integrals, `ContDiff`, `crossProduct`,
and the Euclidean norm, but no knot-total-curvature or unknottedness
API.
-/

noncomputable section

open Set
open scoped Real
open WithLp

/-- **Euclidean 3-space for the Fáry–Milnor theorem.** Euclidean 3-space is the real vector
space $\mathbb{R}^3$ with the Euclidean inner product and norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- **Period of a parametrised knot.** The period used for parametrised knots is the real number
$2\pi$. -/
def period : ℝ := 2 * Real.pi

/-- **Velocity of a space curve.** For a curve $r \colon \mathbb{R} \to \mathbb{R}^3$ and a real
number $t$, the velocity of $r$ at $t$ is its derivative $r'(t)$, taken to be $0$ when $r$ is not
differentiable at $t$. -/
def velocity (r : ℝ → Space) (t : ℝ) : Space :=
  deriv r t

/-- **Acceleration of a space curve.** For a curve $r \colon \mathbb{R} \to \mathbb{R}^3$ and a real
number $t$, the acceleration of $r$ at $t$ is the derivative at $t$ of its velocity
$s \mapsto r'(s)$, that is $r''(t)$, where a derivative that does not exist is taken to be $0$. -/
def acceleration (r : ℝ → Space) (t : ℝ) : Space :=
  deriv (velocity r) t

/-- **Curvature of a space curve.** For a curve $r \colon \mathbb{R} \to \mathbb{R}^3$ with velocity
$r'$ and acceleration $r''$, the curvature of $r$ at a real number $t$ is
$\kappa(t) = \lVert r'(t) \times r''(t) \rVert / \lVert r'(t) \rVert^3$, where $\times$ is the cross
product and $\lVert \cdot \rVert$ is the Euclidean norm; the quotient is $0$ when $r'(t) = 0$. -/
def curvature (r : ℝ → Space) (t : ℝ) : ℝ :=
  ‖toLp 2 (crossProduct (ofLp (velocity r t)) (ofLp (acceleration r t)))‖ /
    ‖velocity r t‖ ^ 3

/-- **Total curvature of a space curve.** For a curve $r \colon \mathbb{R} \to \mathbb{R}^3$ with
velocity $r'$ and curvature $\kappa$, the total curvature of $r$ is the arc-length integral
$\int_0^{2\pi} \kappa(t) \, \lVert r'(t) \rVert \, dt$ over one period, where the integral is taken
to be $0$ if the integrand is not integrable. -/
def totalCurvature (r : ℝ → Space) : ℝ :=
  ∫ t in (0 : ℝ)..period, curvature r t * ‖velocity r t‖

/-- **Standard circle.** The standard circle is the curve $\mathbb{R} \to \mathbb{R}^3$ given by
$t \mapsto (\cos t, \sin t, 0)$: the unit circle centred at the origin in the $xy$-plane. -/
def standardCircle (t : ℝ) : Space :=
  toLp 2 ![Real.cos t, Real.sin t, 0]

/-- **Smooth knot.** A curve $r \colon \mathbb{R} \to \mathbb{R}^3$ is a smooth knot when it is
real-analytic, periodic with period $2\pi$, injective on $[0, 2\pi)$, and regular, that is, its
velocity $r'(t)$ is nonzero for every real number $t$. -/
structure IsSmoothKnot (r : ℝ → Space) : Prop where
  smooth : ContDiff ℝ ⊤ r
  periodic : Function.Periodic r period
  injective_on_period : Set.InjOn r (Set.Ico (0 : ℝ) period)
  regular : ∀ t : ℝ, velocity r t ≠ 0

/-- **Unknotted curve.** A curve $r \colon \mathbb{R} \to \mathbb{R}^3$ is unknotted when there is
a real-analytic map $R \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}^3$ such that
$R(t, 0) = r(t)$ and $R(t, 1) = (\cos t, \sin t, 0)$, the standard circle, for every real
number $t$, and for every $s \in [0, 1]$ the curve $t \mapsto R(t, s)$ is a smooth knot. -/
def IsUnknotted (r : ℝ → Space) : Prop :=
  ∃ R : ℝ → ℝ → Space,
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => R p.1 p.2) ∧
      (∀ t : ℝ, R t 0 = r t) ∧
      (∀ t : ℝ, R t 1 = standardCircle t) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, IsSmoothKnot (fun t : ℝ => R t s)

/- **Fáry–Milnor theorem** (Fáry 1949 / Milnor 1950). A smooth knot
with total curvature at most `4π` is unknotted. -/
/-- **Fáry–Milnor theorem.** Let $r \colon \mathbb{R} \to \mathbb{R}^3$ be a smooth knot, that is,
a real-analytic, $2\pi$-periodic curve that is injective on $[0, 2\pi)$ and has nonzero velocity
everywhere. If the total curvature of $r$ is at most $4\pi$, then $r$ is unknotted: there is a
real-analytic isotopy from $r$ to the standard circle through smooth knots.

Source: I. Fáry, 'Sur la courbure totale d'une courbe gauche faisant un nœud', Bull. Soc. Math. France 77 (1949) 128–138; J. Milnor, 'On the total curvature of knots', Ann. of Math. (2) 52 (1950) 248–257. §161 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fary_milnor`. -/
public theorem_wanted fary_milnor_total_curvature
    {r : ℝ → Space} (_hknot : IsSmoothKnot r)
    (_hK : totalCurvature r ≤ 4 * Real.pi) :
    IsUnknotted r

end

end FaryMilnorProblem
end Geometry

end MathlibExt.Geometry.FaryMilnorWanted
