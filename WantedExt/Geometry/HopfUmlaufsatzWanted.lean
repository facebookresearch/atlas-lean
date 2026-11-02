/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hopf Umlaufsatz (theorem of turning tangents)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.HopfUmlaufsatz` — hopf_umlaufsatz (manifest `manifests/problems/hopf_umlaufsatz.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.HopfUmlaufsatzWanted` namespace. Mathematical
statements are unchanged. Source: H. Hopf, *Über die Drehung der Tangenten...*, Compositio Math. 2 (1935). Knill, §170.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.HopfUmlaufsatzWanted
namespace Geometry.HopfUmlaufsatz

/-!
# The Hopf Umlaufsatz (theorem of turning tangents)

`hopf_umlaufsatz`: a positively oriented simple closed unit-speed plane curve
has total signed curvature `2π`. Trusted helpers (`signedArea`, `signedCurvature`,
`totalCurvature`, `IsPositiveSimpleClosedUnitSpeedCurve`, `IsTangentAngleLift`,
…) are non-holes. Mathlib has no turning-tangents theorem.
Category-(b) candidate from §170 of the Knill survey.
-/

/-- **Euclidean plane for the Umlaufsatz.** The Euclidean plane is the space $\mathbb{R}^2$ of
pairs of real numbers with the Euclidean inner product and norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Parameter period for the Umlaufsatz.** The parameter period of the closed curves in the
Hopf Umlaufsatz is the real number $2\pi$. -/
noncomputable def period : ℝ := 2 * Real.pi

/-- **Velocity of a plane curve.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean
plane and $t \in \mathbb{R}$, the velocity of $r$ at $t$ is its derivative $r'(t) \in \mathbb{R}^2$,
taken to be $0$ where $r$ is not differentiable. -/
noncomputable def velocity (r : ℝ → Plane) (t : ℝ) : Plane := deriv r t

/-- **Planar determinant for the Umlaufsatz.** For vectors $u = (u_0, u_1)$ and
$v = (v_0, v_1)$ in the Euclidean plane $\mathbb{R}^2$, $\det(u, v) = u_0 v_1 - u_1 v_0$, the
signed area of the parallelogram spanned by $u$ and $v$. -/
def det2 (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- **Signed area of a closed plane curve.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$, the
signed area is $\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt$, where $r'$ is the velocity of
$r$ and $\det(u, v) = u_0 v_1 - u_1 v_0$ (Green's normalization). Its sign fixes the orientation
convention. -/
noncomputable def signedArea (r : ℝ → Plane) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..period, det2 (r t) (velocity r t)

/-- **Positively oriented simple closed unit-speed curve.** A curve
$r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean plane is a positively oriented simple closed
unit-speed curve when it is continuously differentiable, periodic with period $2\pi$, injective on
$[0, 2\pi)$, has velocity of norm $\lVert r'(t) \rVert = 1$ for every $t \in \mathbb{R}$, and has
positive signed area $\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt > 0$, where
$\det(u, v) = u_0 v_1 - u_1 v_0$. -/
structure IsPositiveSimpleClosedUnitSpeedCurve (r : ℝ → Plane) : Prop where
  smooth : ContDiff ℝ 1 r
  periodic : Function.Periodic r period
  injective_on_period : Set.InjOn r (Set.Ico (0 : ℝ) period)
  unit_speed : ∀ t : ℝ, ‖velocity r t‖ = 1
  positive_orientation : 0 < signedArea r

/-- **Tangent-angle lift.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean plane,
a function $\alpha : \mathbb{R} \to \mathbb{R}$ is a tangent-angle lift of $r$ when $\alpha$ is
continuously differentiable and the velocity of $r$ satisfies
$r'(t) = (\cos \alpha(t), \sin \alpha(t))$ for every $t \in \mathbb{R}$. -/
structure IsTangentAngleLift (r : ℝ → Plane) (α : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 1 α
  velocity_eq : ∀ t : ℝ,
    velocity r t = !₂[Real.cos (α t), Real.sin (α t)]

/-- **Signed curvature.** For a function $\alpha : \mathbb{R} \to \mathbb{R}$ and
$t \in \mathbb{R}$, the signed curvature of $\alpha$ at $t$ is the derivative $\alpha'(t)$, taken
to be $0$ where $\alpha$ is not differentiable at $t$.

When $\alpha$ is a tangent-angle lift of a unit-speed plane curve, this is the signed curvature
of the curve at $t$. -/
noncomputable def signedCurvature (α : ℝ → ℝ) (t : ℝ) : ℝ := deriv α t

/-- **Total signed curvature of a tangent-angle lift.** For a function
$\alpha : \mathbb{R} \to \mathbb{R}$, the total signed curvature is $\int_0^{2\pi} \alpha'(t)\,dt$,
the integral of the signed curvature $\alpha'$ over one parameter period $[0, 2\pi]$. -/
noncomputable def totalCurvature (α : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..period, signedCurvature α t

/- **Hopf Umlaufsatz.** A positively oriented simple closed unit-speed plane
curve has total signed curvature `2π`. -/
/-- **Hopf's Umlaufsatz.** Let $r : \mathbb{R} \to \mathbb{R}^2$ be a positively oriented simple
closed unit-speed plane curve: $r$ is continuously differentiable and $2\pi$-periodic, injective
on $[0, 2\pi)$, satisfies $\lVert r'(t) \rVert = 1$ for all $t$, and has positive signed area
$\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt > 0$, where $\det(u, v) = u_0 v_1 - u_1 v_0$.
Let $\alpha : \mathbb{R} \to \mathbb{R}$ be a continuously differentiable tangent-angle lift of
$r$, that is, $r'(t) = (\cos \alpha(t), \sin \alpha(t))$ for all $t$. Then the total signed
curvature over one period is $2\pi$: $\int_0^{2\pi} \alpha'(t)\,dt = 2\pi$.

Source: H. Hopf, *Über die Drehung der Tangenten...*, Compositio Math. 2 (1935). Knill, §170. Via leanprover/lean-eval@38361be, problem `hopf_umlaufsatz`. -/
public theorem_wanted hopf_umlaufsatz
    {r : ℝ → Plane} {α : ℝ → ℝ}
    (_hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (_hα : IsTangentAngleLift r α) :
    totalCurvature α = 2 * Real.pi

end Geometry.HopfUmlaufsatz

end MathlibExt.Geometry.HopfUmlaufsatzWanted
