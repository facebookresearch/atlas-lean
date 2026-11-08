/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hurewicz theorem in degree 1 (H₁ = abelianization of π₁)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.Hurewicz` — hurewicz_h1_abelianization (manifest `manifests/problems/hurewicz_h1_abelianization.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.HurewiczWanted` namespace. Mathematical
statements are unchanged. Source: W. Hurewicz (1935); see Hatcher, *Algebraic Topology*, Theorem 2A.1. Knill, *Some fundamental theorems in mathematics*, §153.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.HurewiczWanted
namespace Topology.Hurewicz

/-!
# Hurewicz theorem (degree 1): H₁ is the abelianization of π₁

`hurewicz_h1_abelianization`: for a path-connected space, the first integral
singular homology group is the abelianization of the fundamental group. Trusted
helper `IntegralHomology` (non-hole). Path-connectedness is essential. Mathlib
has singular homology and the fundamental group but not the degree-1 Hurewicz
isomorphism.
Category-(b) candidate from §153 of the Knill survey.
-/

open CategoryTheory AlgebraicTopology

/-- Integral singular homology in degree `n`, as an additive group. -/
noncomputable abbrev IntegralHomology (n : ℕ) (X : Type) [TopologicalSpace X] : AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

/- **Hurewicz (n = 1).** For a path-connected space `X`, `H₁(X;ℤ)` is the
abelianization of `π₁(X, x)`. -/
/-- Source: W. Hurewicz (1935); see Hatcher, *Algebraic Topology*, Theorem 2A.1. Knill, *Some fundamental theorems in mathematics*, §153. Via leanprover/lean-eval@38361be, problem `hurewicz_h1_abelianization`. -/
public theorem_wanted hurewicz_h1_abelianization
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Nonempty (Additive (Abelianization (FundamentalGroup X x)) ≃+
      (IntegralHomology 1 X : Type))

end Topology.Hurewicz

end MathlibExt.Topology.HurewiczWanted
