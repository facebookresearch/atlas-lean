/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kirk's normal-structure fixed point theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.KirkNormalStructure` — kirk_normal_structure (manifest `manifests/problems/kirk_normal_structure.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.KirkNormalStructureWanted` namespace. Mathematical
statements are unchanged. Source: W. A. Kirk, A fixed point theorem for mappings which do not increase distances, Amer. Math. Monthly 72 (1965). Listed as §228 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §228.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.KirkNormalStructureWanted
namespace Topology.KirkNormalStructure

/-!
# Kirk's normal-structure fixed point theorem

`kirk_normal_structure`: a nonexpansive self-map of a nonempty bounded closed
convex subset of a reflexive Banach space with normal structure has a fixed
point. Reflexivity is genuine Banach-space reflexivity (surjectivity of the
canonical embedding into the bidual), avoiding the collapse to the
finite-dimensional case caused by algebraic reflexivity. Helpers
`metricDiameter`, `pointRadiusIn`, `IsDiametralPoint`, `HasNormalStructure`
and `IsNonexpansiveSelfMap` express the geometric hypotheses. Category-(b)
candidate from §228 of the Knill survey.
-/

open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diameter of a set, as a real supremum of all pairwise distances inside
the set.  This keeps the normal-structure statement in ordinary metric
language. -/
noncomputable def metricDiameter (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, dist x y = r}

/-- Radius of a point relative to a set, i.e. the supremum of its distances to
points of the set. -/
noncomputable def pointRadiusIn (x : E) (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ s, dist x y = r}

/-- A point is diametral in `s` if its radius in `s` is the diameter of `s`. -/
def IsDiametralPoint (s : Set E) (x : E) : Prop :=
  x ∈ s ∧ pointRadiusIn x s = metricDiameter s

/-- A bounded convex set has normal structure if every nontrivial convex subset
contains a non-diametral point. -/
def HasNormalStructure (K : Set E) : Prop :=
  ∀ H : Set E,
    H ⊆ K →
      Convex ℝ H →
        H.Nontrivial →
          ∃ x ∈ H, ¬ IsDiametralPoint H x

/-- A self-map of a set is nonexpansive when it is `1`-Lipschitz for the
subtype metric. -/
def IsNonexpansiveSelfMap (K : Set E) (T : K → K) : Prop :=
  LipschitzWith 1 T

/- **Kirk's normal-structure fixed-point theorem** (§228).  A nonexpansive
self-map of a nonempty bounded closed convex subset of a reflexive Banach
space with normal structure has a fixed point. -/
/-- Source: W. A. Kirk, A fixed point theorem for mappings which do not increase distances, Amer. Math. Monthly 72 (1965). Listed as §228 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §228. Via leanprover/lean-eval@38361be, problem `kirk_normal_structure`. -/
public theorem_wanted kirk_normal_structure [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    (hK_normal : HasNormalStructure K) (T : K → K)
    (hT : IsNonexpansiveSelfMap K T) :
    ∃ x : K, IsFixedPt T x

end Topology.KirkNormalStructure

end MathlibExt.Topology.KirkNormalStructureWanted
