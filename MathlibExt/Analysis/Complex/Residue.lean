/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The residue of a function at an isolated singularity

We define the residue `Res_{z=a} f(z)` of a function `f : ℂ → E` at `a` without reference to a
particular circle (`Complex.residue`), and show that it equals the normalized circle integral
`(2πi)⁻¹ ∮_{|z-a|=r} f(z) dz` on every circle `|z - a| = r`, `r > 0`, whose closed disc lies in a
set `Ω` on which `f` is holomorphic away from `a` (`Complex.residue_eq_circleIntegral`). In
particular this integral does not depend on the circle. The codomain `E` is any complex normed
space.

The residue is the limit, as `r` decreases to `0`, of the normalized circle integral. By Cauchy's
theorem on an annulus (`circleIntegral_eq_of_differentiable_on_annulus_off_countable`), this
integral is constant on `(0, r]` for every admissible `r`, so the limit exists and equals it.
Mathlib has the circle integral and Cauchy's theorem on an annulus, but no complex-analytic
residue; MathlibExt has residue computations for rectangle contours but no general definition.

The source defines `Res_{z=a} f(z) = (2πi)⁻¹ ∫_C f(z) dz` for "any circle `C` contained in `Ω`
with center `a`", where `f` is holomorphic in `Ω' = Ω - a`. We read "circle contained in `Ω`" as
"closed disc contained in `Ω`" (`closedBall a r ⊆ Ω`); see `Complex.residue_eq_circleIntegral` for
why the literal reading makes the definition ill-posed.

Rubric-guided revision of v1 ComplexVariables target 18 (`residue` in
`v1/Atlas/ComplexVariables/code/Lecture14.lean` at commit
6191bf1ba03d204784385ef5be2472be88035b93). The archived definition took the radius as an explicit
argument, so `residue f a R` was not an invariant of `(f, a)`; it carried no holomorphy condition,
returned junk for `R ≤ 0` or a bad circle, and left every consumer to choose a radius and supply
the side conditions; independence of the radius was proved only separately, for two given radii
bounding an annulus. It was also a root-namespace name without a docstring and used
`(2 * ↑Real.pi * I)⁻¹ * ∮` instead of `(2 * π * I)⁻¹ • ∮`. Here the residue depends on `f` and `a`
only, and the source formula holds on every admissible circle. The archived formalization and its
original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Metric Set Topology
open scoped Real

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The residue `Res_{z=a} f(z)` of `f` at `a`: the limit, as the radius `r` decreases to `0`, of
the normalized circle integral `(2πi)⁻¹ ∮_{|z-a|=r} f(z) dz`.

If `f` is holomorphic on a punctured neighbourhood of `a`, this integral is constant for all small
`r`, and `Complex.residue_eq_circleIntegral` shows that the residue equals it on every circle about
`a` whose closed disc lies in a set on which `f` is holomorphic away from `a`. For other `f` the
value carries no meaning. -/
@[expose] public noncomputable def residue (f : ℂ → E) (a : ℂ) : E :=
  limUnder (𝓝[>] 0) fun r : ℝ => (2 * π * I)⁻¹ • ∮ z in C(a, r), f z

/-- The residue is the normalized integral over any circle about `a`: if `f` is holomorphic on
`Ω \ {a}` and the closed disc of radius `r > 0` about `a` lies in `Ω`, then
`Res_{z=a} f(z) = (2πi)⁻¹ ∮_{|z-a|=r} f(z) dz`.

This is the source's defining formula, with its "circle `C` contained in `Ω`" read as the closed
disc bounded by `C` lying in `Ω`. Asking only for the circle itself to lie in `Ω` would make the
definition ill-posed: for `b ≠ a`, `Ω = ℂ \ {b}` and `f z = (z - b)⁻¹`, every circle about `a`
avoiding `b` lies in `Ω`, but the normalized integral is `0` on those of radius `< ‖b - a‖` and `1`
on those of radius `> ‖b - a‖`. When `Ω` is a disc about `a` the two readings agree.

`Ω` need not be open; for open `Ω`, `hf` says that `f` is holomorphic on `Ω' = Ω \ {a}`. -/
public theorem residue_eq_circleIntegral {f : ℂ → E} {a : ℂ} {Ω : Set ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Ω \ {a})) (hr : 0 < r) (hΩ : closedBall a r ⊆ Ω) :
    residue f a = (2 * π * I)⁻¹ • ∮ z in C(a, r), f z := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  -- The closed annulus `s ≤ |z - a| ≤ r` lies in `Ω \ {a}`, so the two circle integrals agree.
  have hsub : closedBall a r \ ball a s ⊆ Ω \ {a} := fun z hz =>
    ⟨hΩ hz.1, fun hza => hz.2 (hza ▸ mem_ball_self hs.1)⟩
  congr 1
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hs.1 hs.2.le
    countable_empty (hf.continuousOn.mono hsub) fun z hz => hf.differentiableAt ?_
  have hopen : IsOpen (ball a r \ closedBall a s) := isOpen_ball.sdiff isClosed_closedBall
  exact mem_of_superset (hopen.mem_nhds hz.1) fun w hw =>
    hsub ⟨ball_subset_closedBall hw.1, fun hws => hw.2 (ball_subset_closedBall hws)⟩

end Complex
