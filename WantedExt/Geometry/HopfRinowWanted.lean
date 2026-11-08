/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hopf–Rinow theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.HopfRinow` — hopf_rinow (manifest `manifests/problems/hopf_rinow.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.HopfRinowWanted` namespace. Mathematical
statements are unchanged. Source: H. Hopf and W. Rinow, *Ueber den Begriff der vollständigen differentialgeometrischen Fläche*, Comment. Math. Helv. 3 (1931), 209-225. Listed as §93 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.HopfRinowWanted
open scoped Manifold ENNReal ContDiff
open Bundle

namespace Geometry

/-!
# Hopf–Rinow theorem

For a connected, locally compact, finite-dimensional smooth Riemannian
manifold `M`, metric completeness and geodesic completeness are
equivalent.

The problem ships two helper definitions: `IsGeodesic` (a path with
locally linear `edist` — a metric formulation of affinely parametrised
local minimising geodesics, avoiding any Levi-Civita / connection
infrastructure) and `IsGeodesicallyComplete` (every geodesic on a
bounded open interval extends to all of `ℝ`, the metric analogue of
"the exponential map extends to the whole tangent bundle").

Finite dimensionality is essential: Hopf–Rinow fails on infinite-
dimensional Riemannian Hilbert manifolds. The `IsRiemannianManifold I M`
hypothesis ties `edist` to `riemannianEDist`.

Smoothness of the metric tensor is also essential, and a bare
`Bundle.RiemannianBundle` does not provide it: it equips each fibre with an
inner product but imposes no regularity across base points, so the metric may
be arbitrarily rough. We therefore require
`[IsContMDiffRiemannianBundle I ∞ E …]` (with its companion
`[IsContinuousRiemannianBundle E …]`). Without it the equivalence is false: a
flat metric cone of apex angle `< 2π` is topologically `ℝ²`, hence a
boundaryless smooth manifold, and is connected, proper, locally compact and
complete; but a radial geodesic running into the apex admits no extension, so
it is metrically complete yet not geodesically complete. The smooth metric is
exactly what lets the proof construct minimising geodesics via Picard–Lindelöf
on the geodesic ODE.

The `[I.Boundaryless]` hypothesis is also essential: on a manifold *with*
boundary the equivalence fails. The closed interval `[0, 1]` (modelled on
`𝓡∂ 1`) is metrically complete but not geodesically complete — a geodesic
running toward an endpoint cannot extend to all of `ℝ` — so the backward
direction `CompleteSpace M → IsGeodesicallyComplete M` breaks without it.

This statement was corrected twice, both times thanks to Lorenzo Luccioli using
Harmonic's Aristotle. On 2026-06-14 the missing `[I.Boundaryless]` was added,
after a formal disproof via the `[0, 1]` counterexample. On 2026-06-18 the
missing metric-smoothness hypotheses were added, after Aristotle flagged the
flat-cone counterexample described above. Thanks to both.
-/

/-- A path `γ : ℝ → M` is a **(constant-speed) geodesic** if there is
some speed `c : ℝ≥0` such that at every parameter `t₀ : ℝ`, the
Riemannian distance is locally linear in the parameter. -/
def IsGeodesic {M : Type*} [EMetricSpace M] (γ : ℝ → M) : Prop :=
  ∃ c : NNReal, ∀ t₀ : ℝ, ∃ δ > (0 : ℝ),
    ∀ s t : ℝ, |s - t₀| < δ → |t - t₀| < δ →
      edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|

/-- The Riemannian manifold `M` is **geodesically complete** if every
geodesic defined on a bounded open interval `(a, b) ⊂ ℝ` extends to a
geodesic defined on all of `ℝ`. -/
def IsGeodesicallyComplete (M : Type*) [EMetricSpace M] : Prop :=
  ∀ (a b : ℝ) (γ : ℝ → M), a < b →
    (∃ c : NNReal, ∀ t₀ ∈ Set.Ioo a b, ∃ δ > (0 : ℝ),
      ∀ s t : ℝ,
        s ∈ Set.Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) →
        t ∈ Set.Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) →
        edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|) →
    ∃ γext : ℝ → M, IsGeodesic γext ∧ ∀ t ∈ Set.Ioo a b, γext t = γ t

/- **Hopf–Rinow theorem.** For a connected, locally compact,
finite-dimensional smooth Riemannian manifold `M` *without boundary*,
metric completeness and geodesic completeness are equivalent. -/
/-- Source: H. Hopf and W. Rinow, *Ueber den Begriff der vollständigen differentialgeometrischen Fläche*, Comment. Math. Helv. 3 (1931), 209-225. Listed as §93 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `hopf_rinow`. -/
public theorem_wanted hopf_rinow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [LocallyCompactSpace M] [ConnectedSpace M] :
    IsGeodesicallyComplete M ↔ CompleteSpace M

end Geometry

end MathlibExt.Geometry.HopfRinowWanted
