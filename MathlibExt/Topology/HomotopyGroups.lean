/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Topology/HomotopyGroups.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `pi1_circle_mulEquiv_int`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0. You may use these portions in compliance with
the License, available at https://www.apache.org/licenses/LICENSE-2.0.

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

The adapted portions are the theorem statement, its original docstring (retained as the plain
comment above the theorem), and the module paragraph on explicit basepoints.

Modification notice (Apache License 2.0, Section 4). ATLAS replaced `EvalTools.Markers`
with `Batteries.Util.ProofWanted`, converted the `@[eval_problem]` theorem to a `theorem_wanted`,
and placed it in the `MathlibExt.Topology.HomotopyGroupsWanted` namespace. ATLAS subsequently
proved the theorem and moved it from `WantedExt/Topology/HomotopyGroupsWanted.lean` to this
module, preserving its full name and statement.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section

/-!
# The fundamental group of the circle

The fundamental group of the unit circle in `ℂ` based at `1` is isomorphic, as a
group, to the additive group `ℤ`. The proof identifies the circle with the
additive circle of period `2π` via the complex exponential and applies Mathlib's
winding-number isomorphism for the additive circle.

We use explicit basepoints throughout. This keeps the statements close to Mathlib's
current APIs, where homotopy groups are based.
-/

namespace MathlibExt.Topology.HomotopyGroupsWanted
namespace Topology

namespace Pi1Circle

/-- The fundamental groups of the two circles are isomorphic, via the
exponential homeomorphism. -/
private noncomputable def fundamentalGroupCircleMulEquiv :
    FundamentalGroup (AddCircle (2 * Real.pi)) ((0 : ℝ) : AddCircle (2 * Real.pi)) ≃*
      FundamentalGroup Circle (1 : Circle) := by
  let eqv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    AddCircle.homeomorphCircle'.toHomotopyEquiv
  let ff : eqv.functor.FullyFaithful := eqv.fullyFaithfulFunctor
  have hobj : eqv.functor.obj
      (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi))) =
      FundamentalGroupoid.mk (1 : Circle) := by
    change FundamentalGroupoid.mk (AddCircle.homeomorphCircle' (0 : ℝ)) =
      FundamentalGroupoid.mk (1 : Circle)
    rw [AddCircle.homeomorphCircle'_apply_mk, Circle.exp_zero]
  change CategoryTheory.End (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi))) ≃*
    CategoryTheory.End (FundamentalGroupoid.mk (1 : Circle))
  exact hobj ▸ CategoryTheory.Functor.FullyFaithful.mulEquivEnd ff
    (FundamentalGroupoid.mk ((0 : ℝ) : AddCircle (2 * Real.pi)))

end Pi1Circle

set_option linter.dupNamespace false in
/- The fundamental group of the complex unit circle is infinite cyclic. -/
/-- **The fundamental group of the circle is infinite cyclic.** The fundamental group of the unit
circle in $\mathbb{C}$ based at $1$ is isomorphic, as a group, to the additive group $\mathbb{Z}$.

Source: Classical theorem in algebraic topology. Via leanprover/lean-eval@38361be, problem
`pi1_circle_mulEquiv_int`. -/
public theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    (Pi1Circle.fundamentalGroupCircleMulEquiv.symm.trans
      (AddCircle.windingNumberIso ((0 : ℝ) : AddCircle (2 * Real.pi))))⟩

end Topology

end MathlibExt.Topology.HomotopyGroupsWanted
