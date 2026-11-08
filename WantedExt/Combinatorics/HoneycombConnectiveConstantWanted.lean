/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connective constant of the honeycomb lattice

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.HoneycombConnectiveConstant` — honeycomb_connective_constant (manifest `manifests/problems/honeycomb_connective_constant.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted` namespace. Mathematical
statements are unchanged. Source: H. Duminil-Copin and S. Smirnov, 'The connective constant of the honeycomb lattice equals sqrt(2 + sqrt 2)', Ann. of Math. 175 (2012), 1653-1665, https://doi.org/10.4007/annals.2012.175.3.14.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted
namespace Combinatorics.HoneycombConnectiveConstant

/-!
# The connective constant of the honeycomb lattice

Duminil-Copin and Smirnov proved Nienhuis's prediction that the connective
constant of the honeycomb (hexagonal) lattice is `sqrt (2 + sqrt 2)`.

The lattice is represented in bipartite integer coordinates. A vertex
`(x, y, false)` is adjacent to `(x, y, true)`, `(x - 1, y, true)`, and
`(x, y - 1, true)`; the reverse moves apply on the other side. Thus a
finite direction word determines a walk, and injectivity of its sequence
of visited vertices is exactly the self-avoiding condition.
-/

open Filter Topology

/-- Bipartite integer coordinates for the vertices of the honeycomb lattice. -/
structure HoneycombVertex where
  x : ℤ
  y : ℤ
  side : Bool
deriving DecidableEq

/-- Take one of the three incident edges at a honeycomb-lattice vertex. -/
def step (v : HoneycombVertex) (direction : Fin 3) : HoneycombVertex :=
  if v.side then
    match direction.1 with
    | 0 => ⟨v.x, v.y, false⟩
    | 1 => ⟨v.x + 1, v.y, false⟩
    | _ => ⟨v.x, v.y + 1, false⟩
  else
    match direction.1 with
    | 0 => ⟨v.x, v.y, true⟩
    | 1 => ⟨v.x - 1, v.y, true⟩
    | _ => ⟨v.x, v.y - 1, true⟩

/-- Traversing the same locally labelled edge twice returns to the starting
vertex. In particular, the coordinate model defines an undirected graph. -/
@[simp]
theorem step_step (v : HoneycombVertex) (direction : Fin 3) :
    step (step v direction) direction = v := by
  rcases v with ⟨x, y, side⟩
  fin_cases direction
  all_goals cases side
  all_goals simp [step]

/-- The three direction labels at a vertex select three distinct neighbors. -/
theorem step_injective (v : HoneycombVertex) : Function.Injective (step v) := by
  intro direction₁ direction₂ h
  rcases v with ⟨x, y, side⟩
  cases side
  all_goals fin_cases direction₁
  all_goals fin_cases direction₂
  all_goals simp [step] at h ⊢
  all_goals omega

/-- A fixed origin in the vertex-transitive honeycomb lattice. -/
def origin : HoneycombVertex := ⟨0, 0, false⟩

/-- The endpoint reached by following a finite word of directions from the origin. -/
def endpoint (directions : List (Fin 3)) : HoneycombVertex :=
  directions.foldl step origin

/-- The vertex visited after the first `i` steps of a direction word. -/
def vertexAt {n : ℕ} (directions : Fin n → Fin 3) (i : Fin (n + 1)) :
    HoneycombVertex :=
  endpoint ((List.ofFn directions).take i.1)

/-- The finite set of vertices visited by a direction word, including the origin. -/
def visitedVertices {n : ℕ} (directions : Fin n → Fin 3) : Finset HoneycombVertex :=
  Finset.univ.image (vertexAt directions)

/-- A direction word is self-avoiding when its `n + 1` visited vertices are distinct. -/
def IsSelfAvoiding {n : ℕ} (directions : Fin n → Fin 3) : Prop :=
  (visitedVertices directions).card = n + 1

instance {n : ℕ} (directions : Fin n → Fin 3) : Decidable (IsSelfAvoiding directions) := by
  unfold IsSelfAvoiding
  infer_instance

/-- The number of `n`-step self-avoiding walks on the honeycomb lattice
starting at the origin. -/
def walkCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun directions : Fin n → Fin 3 =>
    IsSelfAvoiding directions).card

/-- A small computable check of the lattice encoding: there are twelve
three-step self-avoiding walks from a fixed honeycomb vertex. -/
theorem walkCount_three : walkCount 3 = 12 := by
  decide

/-- At six steps the first hexagonal cycle appears; the standard count is `90`.
The `+kernel` evaluation keeps the enumeration of all `3 ^ 6` direction words in
the kernel; reducing it in the elaborator costs several times the default
heartbeat budget. -/
theorem walkCount_six : walkCount 6 = 90 := by
  decide +kernel

/- **Duminil-Copin-Smirnov honeycomb connective-constant theorem.** The
exponential growth rate of the number of self-avoiding walks is
`sqrt (2 + sqrt 2)`. -/
/-- Source: H. Duminil-Copin and S. Smirnov, 'The connective constant of the honeycomb lattice equals sqrt(2 + sqrt 2)', Ann. of Math. 175 (2012), 1653-1665, https://doi.org/10.4007/annals.2012.175.3.14. Via leanprover/lean-eval@38361be, problem `honeycomb_connective_constant`. -/
public theorem_wanted honeycomb_connective_constant :
    Tendsto
      (fun n ↦ (walkCount n : ℝ) ^ (1 / n : ℝ))
      atTop
      (nhds (Real.sqrt (2 + Real.sqrt 2)))

end Combinatorics.HoneycombConnectiveConstant

end MathlibExt.Combinatorics.HoneycombConnectiveConstantWanted
