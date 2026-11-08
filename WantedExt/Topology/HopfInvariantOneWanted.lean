/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Adams: S^n is an H-space iff n = 0, 1, 3, 7

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.HopfInvariantOne` — hSpace_sphere_iff (manifest `manifests/problems/hSpace_sphere_iff.toml`, rev 1, submitter Vasily Ilin, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.HopfInvariantOneWanted` namespace. Mathematical
statements are unchanged. Source: J. F. Adams, 'On the non-existence of elements of Hopf invariant one', Ann. of Math. 72 (1960), 20-104; J. F. Adams and M. F. Atiyah, 'K-theory and the Hopf invariant', Quart. J. Math. Oxford 17 (1966), 31-38. See also A. Hatcher, 'Algebraic Topology', Section 4.B.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.HopfInvariantOneWanted
namespace Topology.HopfInvariantOne

/-!
# Hopf invariant one: the spheres that are H-spaces

Adams' Hopf-invariant-one theorem, in its H-space formulation: the sphere
`𝕊ⁿ` admits an H-space structure if and only if `n` is `0`, `1`, `3`, or `7`.

We use Mathlib's `HSpace`: a continuous multiplication with a basepoint `e`
satisfying `μ (e, e) = e` strictly and two-sided units up to based homotopy.
The reverse direction transports the multiplications on the unit spheres of
the reals, complexes, quaternions, and octonions; the forward direction is
Adams' theorem.
-/

/- **Adams' Hopf-invariant-one theorem** (H-space form). The sphere `𝕊ⁿ`
admits an H-space structure if and only if `n = 0`, `1`, `3`, or `7`. -/
/-- Source: J. F. Adams, 'On the non-existence of elements of Hopf invariant one', Ann. of Math. 72 (1960), 20-104; J. F. Adams and M. F. Atiyah, 'K-theory and the Hopf invariant', Quart. J. Math. Oxford 17 (1966), 31-38. See also A. Hatcher, 'Algebraic Topology', Section 4.B. Via leanprover/lean-eval@38361be, problem `hSpace_sphere_iff`. -/
public theorem_wanted hSpace_sphere_iff (n : ℕ) :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ↔
      n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7

end Topology.HopfInvariantOne

end MathlibExt.Topology.HopfInvariantOneWanted
