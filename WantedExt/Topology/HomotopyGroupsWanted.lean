/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# pi_1 of the circle is Z, pi_3 of the 2-sphere is Z, pi_(n+1) of S^n is Z/2 for n at least 3, pi_n of the n-sphere is Z

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.HomotopyGroups` — pi1_circle_mulEquiv_int (manifest `manifests/problems/pi1_circle_mulEquiv_int.toml`, rev 1, submitter Kim Morrison, status archived); pi3_sphere_two_mulEquiv_int (manifest `manifests/problems/pi3_sphere_two_mulEquiv_int.toml`, rev 1, submitter Kim Morrison, status archived); pi_succ_sphere_n_mulEquiv_zmod_two (manifest `manifests/problems/pi_succ_sphere_n_mulEquiv_zmod_two.toml`, rev 1, submitter Kim Morrison, status archived); pin_sphere_n_mulEquiv_int (manifest `manifests/problems/pin_sphere_n_mulEquiv_int.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.HomotopyGroupsWanted` namespace. The three sphere statements from the same upstream module are consolidated with the canonical sphere API in `WantedExt/Topology/Homotopy/SphereGroupsWanted.lean` (with a shared basepoint-transport lemma) rather than duplicated here. Mathematical
statements are unchanged. Source: Classical theorem in algebraic topology. Classical theorem in algebraic topology. Classical theorem in unstable homotopy theory. Classical theorem in algebraic topology.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace MathlibExt.Topology.HomotopyGroupsWanted
namespace Topology

/-!
Benchmark statements for classical unstable homotopy groups of spheres.

We use explicit basepoints throughout. This keeps the statements close to Mathlib's current APIs,
where homotopy groups are based.
-/

/- The fundamental group of the complex unit circle is infinite cyclic. -/
/-- **The fundamental group of the circle is infinite cyclic.** The fundamental group of the unit
circle in $\mathbb{C}$ based at $1$ is isomorphic, as a group, to the additive group $\mathbb{Z}$.

Source: Classical theorem in algebraic topology. Via leanprover/lean-eval@38361be, problem `pi1_circle_mulEquiv_int`. -/
public theorem_wanted pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ)

/- The sphere entries from the same upstream module (`pi3_sphere_two`,
`pin_sphere_n`, `pi_succ_sphere_n`) are consolidated in
`WantedExt/Topology/Homotopy/SphereGroupsWanted.lean`. -/
end Topology

end MathlibExt.Topology.HomotopyGroupsWanted
