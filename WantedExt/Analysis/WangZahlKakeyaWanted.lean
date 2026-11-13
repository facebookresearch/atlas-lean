/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wang-Zahl: the three-dimensional Kakeya conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.WangZahlKakeya` — wang_zahl_kakeya_dimH (manifest `manifests/problems/wang_zahl_kakeya_dimH.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.WangZahlKakeyaWanted` namespace. Mathematical
statements are unchanged. Source: H. Wang and J. Zahl, 'Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions', Theorem 1.1, arXiv:2502.17655 (2025), https://arxiv.org/abs/2502.17655. The proof builds on their 'Sticky Kakeya sets and the sticky Kakeya conjecture', arXiv:2210.09581, and 'The Assouad dimension of Kakeya sets in R^3', arXiv:2401.12337.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.WangZahlKakeyaWanted
namespace Analysis.WangZahlKakeya

/-!
# The three-dimensional Kakeya conjecture

Hong Wang and Joshua Zahl proved that every Kakeya set in three-dimensional
Euclidean space has Hausdorff dimension `3`. A Kakeya set is compact and
contains a unit line segment pointing in every direction.

The helper `IsKakeya` below includes compactness and makes both "unit"
conditions explicit: the direction vector has norm `1`, and the parameter of
the line segment ranges over `[0, 1]`. It is trusted scaffolding rather than a
benchmark hole.
-/

open MeasureTheory

/-- **Three-dimensional Euclidean space.** The space $\mathbb{R}^3$ with the Euclidean inner
product. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- **Kakeya set.** A Kakeya set is a compact subset $K$ of three-dimensional Euclidean space
that contains a unit line segment in every direction: for every unit vector $v$ there is a
point $x$ with $x + t v \in K$ for all $t \in [0, 1]$. -/
def IsKakeya (K : Set Space) : Prop :=
  IsCompact K ∧
    ∀ v : Space, ‖v‖ = 1 →
      ∃ x : Space, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • v ∈ K

/- **Wang--Zahl's three-dimensional Kakeya theorem.** Every Kakeya set in
three-dimensional Euclidean space has full Hausdorff dimension. -/
/-- **Wang–Zahl theorem: the Kakeya conjecture in three dimensions.** Every Kakeya set in
three-dimensional Euclidean space has Hausdorff dimension $3$.

Source: H. Wang and J. Zahl, 'Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions', Theorem 1.1, arXiv:2502.17655 (2025), https://arxiv.org/abs/2502.17655. The proof builds on their 'Sticky Kakeya sets and the sticky Kakeya conjecture', arXiv:2210.09581, and 'The Assouad dimension of Kakeya sets in R^3', arXiv:2401.12337. Via leanprover/lean-eval@38361be, problem `wang_zahl_kakeya_dimH`. -/
public theorem_wanted wang_zahl_kakeya_dimH {K : Set Space} (hK : IsKakeya K) :
    dimH K = 3

end Analysis.WangZahlKakeya

end MathlibExt.Analysis.WangZahlKakeyaWanted
