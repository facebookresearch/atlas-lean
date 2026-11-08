/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Radial symmetry for positive semilinear Poisson solutions

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.PDE.RadialSymmetry` — semilinear_poisson_radial_symmetry (manifest `manifests/problems/semilinear_poisson_radial_symmetry.toml`, rev 1, submitter Yongxi Lin, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RadialSymmetryWanted` namespace. Mathematical
statements are unchanged. Source: B. Gidas, W. M. Ni, and L. Nirenberg, Symmetry and related properties via the maximum principle, Comm. Math. Phys. 68 (1979), 209-243. Also stated as Theorem 2 (Radial symmetry) in L. C. Evans, Partial Differential Equations, Section 9 on nonvariational techniques.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

namespace MathlibExt.Analysis.RadialSymmetryWanted
namespace Analysis
namespace PDE

/-!
# Radial symmetry for a semilinear Poisson equation

Suppose `u` is a positive solution to a semilinear Poisson PDE:

  `-Δ u = f(u)` in the open unit ball,
  `u = 0` on the boundary.

For Lipschitz `f`, every `C^2` solution on the closed ball is radial and
strictly decreasing as a function of the radius.
-/

open Metric
open scoped NNReal

/-- `u` solved a semilinear Poisson problem if `-Δ u = f(u)` in the open unit
ball and `u = 0` on the unit sphere. -/
def SolvesSemilinearPoisson {n : ℕ} (f : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x ∈ ball 0 1, -Laplacian.laplacian u x = f (u x)) ∧ ∀ x ∈ sphere 0 1, u x = 0

/- **Radial symmetry theorem.** Let `u ∈ C^2(closedBall 0 1)` be a positive
solution of the semilinear Poisson problem `-Δ u = f(u)` in the open unit ball,
with zero Dirichlet boundary values on the unit sphere. If `f : ℝ → ℝ` is
Lipschitz, then `u` is radial: `u x = v ‖x‖` for a nonnegative strictly
decreasing radial profile `v` on `[0, 1]`. -/
/-- Source: B. Gidas, W. M. Ni, and L. Nirenberg, Symmetry and related properties via the maximum principle, Comm. Math. Phys. 68 (1979), 209-243. Also stated as Theorem 2 (Radial symmetry) in L. C. Evans, Partial Differential Equations, Section 9 on nonvariational techniques. Via leanprover/lean-eval@38361be, problem `semilinear_poisson_radial_symmetry`. -/
public theorem_wanted semilinear_poisson_radial_symmetry {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℝ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_lipschitz : ∃ K : ℝ≥0, LipschitzWith K f)
    (hu_c2 : ContDiffOn ℝ 2 u (closedBall 0 1))
    (hu_solve : SolvesSemilinearPoisson f u)
    (hu_positive : ∀ x ∈ ball 0 1, 0 < u x) :
    ∃ v : ℝ → ℝ≥0,
      StrictAntiOn v (Set.Icc (0 : ℝ) 1) ∧
        ∀ x ∈ closedBall 0 1, u x = v ‖x‖

end PDE
end Analysis

end MathlibExt.Analysis.RadialSymmetryWanted
