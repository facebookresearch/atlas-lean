/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized topological Poincaré conjecture in dimensions ≥ 5 (Smale)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.PoincareHighDimTopological` — poincare_high_dim_topological (manifest `manifests/problems/poincare_high_dim_topological.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.PoincareHighDimTopologicalWanted` namespace. Mathematical
statements are unchanged. Source: S. Smale, Generalized Poincaré's conjecture in dimensions greater than four, Ann. of Math. 74 (1961), 391-406. Topological case: M. H. A. Newman, The engulfing theorem for topological manifolds, Ann. of Math. 84 (1966) and E. H. Connell, A topological h-cobordism theorem for n ≥ 5, Illinois J. Math. 11 (1967). Specialization of `proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in Mathlib/Geometry/Manifold/PoincareConjecture.lean.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.PoincareHighDimTopologicalWanted
namespace Topology

/-!
# Generalized topological Poincaré conjecture in dimensions ≥ 5 (Smale)

A specialization of mathlib's generalized `proof_wanted
ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`, restricted to
dimension `n ≥ 5`: every Hausdorff `n`-manifold homotopy-equivalent to the
standard `n`-sphere `𝕊ⁿ` is homeomorphic to `𝕊ⁿ`.

This is **Stephen Smale's 1961 theorem**, originally proved for `n ≥ 5`
assuming a smooth structure on `M` (via the `h`-cobordism theorem). The
**topological** version (no smoothness assumption) was completed by
Newman in 1966 and Connell in 1967. Smale received the Fields Medal in
1966.

mathlib has homotopy equivalences (`≃ₕ`), homeomorphisms (`≃ₜ`),
`ChartedSpace`, and the unit sphere as a topological space — but no
`h`-cobordism theorem, no handle decompositions, and no Poincaré
conjecture in any dimension.
-/

open Metric (sphere)
open ContinuousMap

/- **Generalized topological Poincaré conjecture in dimensions ≥ 5**
(Smale 1961; topological case Newman 1966 / Connell 1967). For `n ≥ 5`,
every Hausdorff `n`-manifold homotopy-equivalent to the standard `n`-sphere
`𝕊ⁿ` is homeomorphic to `𝕊ⁿ`. -/
/-- Source: S. Smale, Generalized Poincaré's conjecture in dimensions greater than four, Ann. of Math. 74 (1961), 391-406. Topological case: M. H. A. Newman, The engulfing theorem for topological manifolds, Ann. of Math. 84 (1966) and E. H. Connell, A topological h-cobordism theorem for n ≥ 5, Illinois J. Math. 11 (1967). Specialization of `proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` in Mathlib/Geometry/Manifold/PoincareConjecture.lean. Via leanprover/lean-eval@38361be, problem `poincare_high_dim_topological`. -/
public theorem_wanted poincare_high_dim_topological
    {n : ℕ} (_h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

end Topology

end MathlibExt.Topology.PoincareHighDimTopologicalWanted
