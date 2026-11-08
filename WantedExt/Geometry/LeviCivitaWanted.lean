/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fundamental theorem of Riemannian geometry (Levi-Civita)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.LeviCivita` — levi_civita_exists_unique (manifest `manifests/problems/levi_civita_exists_unique.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.LeviCivitaWanted` namespace. Mathematical
statements are unchanged. Source: T. Levi-Civita, Nozione di parallelismo in una varietà qualunque, Rend. Circ. Mat. Palermo 42 (1917). Listed as §38 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.MetricCompatibilityShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.MetricCompatibilityShared

namespace MathlibExt.Geometry.LeviCivitaWanted
namespace Geometry
namespace LeviCivita

/-!
# Fundamental theorem of Riemannian geometry (Levi-Civita)

§38 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. On a `C^∞`
finite-dimensional Riemannian manifold `(M, g)`, there exists a unique
smooth torsion-free covariant derivative on `TM` that is compatible with
the metric — the **Levi-Civita connection**.

mathlib has `CovariantDerivative` on a tangent bundle,
`CovariantDerivative.torsion`, `ContMDiffCovariantDerivative`,
`RiemannianBundle`, `IsContMDiffRiemannianBundle`, and `mvfderiv` — but
no metric-compatibility predicate, no Levi-Civita existence/uniqueness, and
no Koszul formula (`grep -ri LeviCivita\|metric.compatible`: no relevant
hits). One helper definition (`IsMetricCompatible`, ~½ page) and an
"agreement on smooth sections" predicate (`SameOnSmooth`, mathlib's
`CovariantDerivative` is bundled over all sections including non-smooth
ones, so uniqueness is stated on the smooth-section subspace) are added
here.

A `[T2Space M]` hypothesis was added on 2026-06-14. We are not certain the
statement is wrong without it, but it looks suspicious: uniqueness on
smooth sections reduces to global smooth vector fields spanning every
tangent space, which (given how mathlib's bump-function machinery works)
needs `M` Hausdorff, and mathlib does not bundle Hausdorffness into
`IsManifold`. Since the classical Levi-Civita theorem is always stated for
(Hausdorff) manifolds, the original intent is better reflected with
`[T2Space M]`, so we add it now. Lorenzo Luccioli, using Harmonic's
Aristotle, flagged the missing hypothesis. Thanks to both.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

/- A covariant derivative `cov` on `TM` is **compatible with the
Riemannian metric** if `v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all
smooth vector fields `Y, Z` and every point/direction `(x, v)`. -/
/-- Two covariant derivatives **agree on smooth sections** if they produce
the same image on every smooth vector field. mathlib's
`CovariantDerivative` is bundled over all sections; the textbook Levi-Civita
uniqueness statement is uniqueness on the smooth-section subspace, captured
by `SameOnSmooth`. -/
def SameOnSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov cov' : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) →
    ∀ (x : M) (v : TangentSpace I x), cov Y x v = cov' Y x v

/- **Fundamental theorem of Riemannian geometry** (Levi-Civita). On a
`C^∞` finite-dimensional Riemannian manifold there exists a smooth
torsion-free metric-compatible covariant derivative on `TM`, and any other
such connection agrees with it on smooth vector fields. -/
/-- Source: T. Levi-Civita, Nozione di parallelismo in una varietà qualunque, Rend. Circ. Mat. Palermo 42 (1917). Listed as §38 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `levi_civita_exists_unique`. -/
public theorem_wanted levi_civita_exists_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      (ContMDiffCovariantDerivative cov ∞ ∧
        cov.torsion = 0 ∧ IsMetricCompatible cov) ∧
      ∀ cov' : CovariantDerivative I E (TangentSpace I (M := M)),
        (ContMDiffCovariantDerivative cov' ∞ ∧
          cov'.torsion = 0 ∧ IsMetricCompatible cov') →
        SameOnSmooth cov cov'

end LeviCivita
end Geometry

end MathlibExt.Geometry.LeviCivitaWanted
