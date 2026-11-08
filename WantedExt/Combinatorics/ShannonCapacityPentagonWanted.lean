/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shannon capacity of the pentagon

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.ShannonCapacityPentagon` — shannon_capacity_pentagon (manifest `manifests/problems/shannon_capacity_pentagon.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.ShannonCapacityPentagonWanted` namespace. Mathematical
statements are unchanged. Source: Knill, *Some fundamental theorems in mathematics*, §238.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.ShannonCapacityPentagonWanted
namespace Combinatorics.ShannonCapacityPentagon

/-!
# Shannon capacity of the pentagon (Lovász)

`shannon_capacity_pentagon`: the Shannon capacity of the five-cycle `C₅` is
`√5`. Trusted helpers `IsIndependent`, `independenceNumber`, `strongPower`,
`HasShannonCapacity` (non-holes). Mathlib has simple graphs and cycle graphs but
no Shannon capacity, strong graph powers, or Lovász number. Category-(b)
candidate from §238 of the Knill survey.
-/

open Filter
open scoped Topology


/-- The strong graph power on length-`k` words.  Two words are confusable
when they are distinct and every coordinate is either equal or confusable in
the base graph. -/
def strongPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm.symm x y := by
    rintro ⟨hxy, hcoord⟩
    exact ⟨hxy.symm, fun i => (hcoord i).imp Eq.symm SimpleGraph.Adj.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The Shannon capacity of `G` is `θ` if the normalized independence
numbers of the strong powers tend to `θ`. -/
noncomputable def HasShannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) (θ : ℝ) :
    Prop :=
  Tendsto
    (fun k : ℕ =>
      Real.rpow
        ((strongPower G (k + 1)).indepNum : ℝ)
        ((k + 1 : ℝ)⁻¹))
    atTop (𝓝 θ)

/- **Lovász's theorem on Shannon capacity of the pentagon** (§238).
The Shannon capacity of the five-cycle is `√5`. -/
/-- Source: Knill, *Some fundamental theorems in mathematics*, §238. Via leanprover/lean-eval@38361be, problem `shannon_capacity_pentagon`. -/
public theorem_wanted shannon_capacity_pentagon :
    HasShannonCapacity (SimpleGraph.cycleGraph 5) (Real.sqrt 5)

end Combinatorics.ShannonCapacityPentagon

end MathlibExt.Combinatorics.ShannonCapacityPentagonWanted
