/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gleason's theorem (finite-dimensional), Gleason's theorem (separable Hilbert space)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.Gleason` — gleason_theorem_finite (manifest `manifests/problems/gleason_theorem_finite.toml`, rev 1, submitter Kim Morrison, status archived); gleason_theorem_separable (manifest `manifests/problems/gleason_theorem_separable.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.GleasonWanted` namespace. Mathematical
statements are unchanged. Source: A. M. Gleason, Measures on the closed subspaces of a Hilbert space, J. Math. Mech. 6 (1957), 885-893. A. M. Gleason, Measures on the closed subspaces of a Hilbert space, J. Math. Mech. 6 (1957), 885-893.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

namespace MathlibExt.Analysis.GleasonWanted
namespace Analysis

/-!
Gleason's theorem (1957).

Let `H` be a complex Hilbert space of dimension at least `3`. Every non-negative function
on the orthogonal projections of `H` that is countably additive on orthogonal families and
sends the identity to `1` is given by `P ↦ Tr(ρ P)` for a unique density operator `ρ`
(positive trace-class operator with trace `1`).

This file states two versions:

1. `gleason_theorem_finite`: `H` is finite-dimensional. The trace-class condition is
   automatic, additivity on orthogonal pairs already implies countable additivity, and
   the conclusion uses the standard finite trace `LinearMap.trace`.

2. `gleason_theorem_separable`: `H` is separable. Stated in Gleason's original "frame
   function on the unit sphere" form: a non-negative function on the unit sphere that
   sums to `1` along every Hilbert basis is given by `x ↦ re ⟨x, ρ x⟩` for some positive
   bounded operator `ρ`. (The Lean conclusion does not assert that `ρ` is trace-class
   with `Tr ρ = 1`; stating that would require trace-class infrastructure not yet at
   this Mathlib pin. It is recoverable by combining the conclusion with `f.basis_sum`.)
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Orthogonal projection.** A continuous linear operator $P$ on a complex Hilbert space $H$ is
an orthogonal projection if it is idempotent, $P^2 = P$, and self-adjoint, $P^* = P$. -/
def IsOrthProj (P : H →L[ℂ] H) : Prop :=
  IsIdempotentElem P ∧ IsSelfAdjoint P

/-- **Frame function on projections.** Let $H$ be a complex Hilbert space. A frame function on
the projection lattice of $H$ is a function $\mu$ from the continuous linear operators on $H$ to
$\mathbb{R}$ such that $\mu(P) \ge 0$ for every orthogonal projection $P$ on $H$,
$\mu(P + Q) = \mu(P) + \mu(Q)$ for all orthogonal projections $P$ and $Q$ on $H$ with $PQ = 0$,
and $\mu(I) = 1$ for the identity operator $I$ on $H$.

Only the values of $\mu$ on orthogonal projections are constrained. In finite dimensions every
orthogonal family of nonzero projections is finite, so additivity on orthogonal pairs already
yields countable additivity. -/
structure FrameFunction (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  μ : (H →L[ℂ] H) → ℝ
  nonneg : ∀ P : H →L[ℂ] H, IsOrthProj P → 0 ≤ μ P
  additive : ∀ P Q : H →L[ℂ] H, IsOrthProj P → IsOrthProj Q → P * Q = 0 →
    μ (P + Q) = μ P + μ Q
  normalized : μ (1 : H →L[ℂ] H) = 1

/-- **Real part of the trace.** For a continuous linear operator $A$ on a finite-dimensional
complex Hilbert space $H$, let $\operatorname{tr}(A) \in \mathbb{C}$ be the trace of $A$ as a
$\mathbb{C}$-linear map on $H$. The real part of the trace of $A$ is the real number
$\operatorname{Re} \operatorname{tr}(A)$. -/
noncomputable def reTr [FiniteDimensional ℂ H] (A : H →L[ℂ] H) : ℝ :=
  (LinearMap.trace ℂ H A.toLinearMap).re

/- **Gleason's theorem**, finite-dimensional version. For `dim H ≥ 3`, every frame
function on the projection lattice of `H` is given by `P ↦ re Tr(ρ P)` for the unique
density operator `ρ` (positive, `re Tr ρ = 1`). -/
/-- **Gleason's theorem in finite dimensions.** Let $H$ be a finite-dimensional complex Hilbert
space of dimension at least $3$, write $\operatorname{tr}$ for the trace of a $\mathbb{C}$-linear
map on $H$, and let $\mu$ be a frame function on the projection lattice of $H$. Then there is a
unique continuous linear operator $\rho$ on $H$ such that $\rho$ is positive,
$\operatorname{Re} \operatorname{tr}(\rho) = 1$, and
$\mu(P) = \operatorname{Re} \operatorname{tr}(\rho P)$ for every orthogonal projection $P$ on $H$.

Source: A. M. Gleason, Measures on the closed subspaces of a Hilbert space, J. Math. Mech. 6 (1957), 885-893. Via leanprover/lean-eval@38361be, problem `gleason_theorem_finite`. -/
public theorem_wanted gleason_theorem_finite
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (f : FrameFunction H) :
    ∃! ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P)

/-- **Frame function on the unit sphere.** Let $H$ be a complex Hilbert space. A frame function
on the unit sphere of $H$ is a function $f$ from the unit vectors of $H$ to $\mathbb{R}$ such that
$f(x) \ge 0$ for every unit vector $x$ in $H$ and, for every Hilbert basis $(b_i)_{i \in \iota}$
of $H$, the family $(f(b_i))_{i \in \iota}$ is unconditionally summable with sum $1$.

This is Gleason's 1957 notion of a frame function, normalized to weight $1$ and required to be
non-negative. -/
structure SphereFrameFunction (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  f : Metric.sphere (0 : H) 1 → ℝ
  nonneg : ∀ x : Metric.sphere (0 : H) 1, 0 ≤ f x
  basis_sum : ∀ {ι : Type*} (b : HilbertBasis ι ℂ H),
    HasSum
      (fun i : ι => f ⟨b i, mem_sphere_zero_iff_norm.mpr (b.orthonormal.norm_eq_one i)⟩)
      1

/- **Gleason's theorem**, separable Hilbert space version (Gleason's original 1957
formulation). For a separable complex Hilbert space `H` of dimension at least `3`, every
frame function on the unit sphere of `H` is given by `x ↦ re ⟨x, ρ x⟩` for some positive
bounded operator `ρ`. (The Lean conclusion does not separately assert trace-class /
`Tr ρ = 1`; see the file docstring.) -/
/-- **Gleason's theorem for separable Hilbert spaces.** Let $H$ be a separable complex Hilbert
space whose dimension over $\mathbb{C}$ is at least $3$, and let $f$ be a frame function on the
unit sphere of $H$. Then there is a positive continuous linear operator $\rho$ on $H$ such that
$f(x) = \operatorname{Re} \langle x, \rho x \rangle$ for every unit vector $x$ in $H$.

The statement does not assert that $\rho$ is trace class with trace $1$, nor that $\rho$ is
unique.

Source: A. M. Gleason, Measures on the closed subspaces of a Hilbert space, J. Math. Mech. 6 (1957), 885-893. Via leanprover/lean-eval@38361be, problem `gleason_theorem_separable`. -/
public theorem_wanted gleason_theorem_separable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (hdim : 3 ≤ Module.rank ℂ H)
    (f : SphereFrameFunction H) :
    ∃ ρ : H →L[ℂ] H,
      ContinuousLinearMap.IsPositive ρ ∧
      ∀ x : Metric.sphere (0 : H) 1,
        f.f x = (inner ℂ (x : H) (ρ (x : H))).re

end Analysis

end MathlibExt.Analysis.GleasonWanted
