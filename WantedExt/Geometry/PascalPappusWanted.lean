/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pascal's theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.PascalPappus` — pascal (manifest `manifests/problems/pascal.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.PascalPappusWanted` namespace. Mathematical
statements are unchanged. Source: B. Pascal, *Essay pour les coniques* (1640). Knill, *Some fundamental theorems in mathematics*, §146.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.PascalPappusWanted
namespace Geometry.PascalPappus

/-!
# Pascal's theorem and Pappus's hexagon theorem

`pascal` (Pascal 1639): six points on a non-singular conic give three collinear
intersection points. `pappus` (Pappus, c. 320 AD): the degenerate-conic case
with the six points on two lines. Trusted helpers (`SamePoint`, `OnConic`,
`meet`, `Collinear3`) are non-holes. Mathlib has the cross product `⨯₃` and
projective vocabulary but neither theorem.
Category-(b) candidates from §146 of the Knill survey.
-/

open Matrix

/-- Two homogeneous coordinate vectors represent the same projective point. -/
def SamePoint (v w : Fin 3 → ℝ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ w = c • v

/-- `[v]` lies on the conic `xᵀ M x = 0`. -/
def OnConic (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : Prop :=
  v ⬝ᵥ (M *ᵥ v) = 0

/-- Intersection (meet) of line `[a][b]` and line `[c][d]`. -/
def meet (a b c d : Fin 3 → ℝ) : Fin 3 → ℝ := (a ⨯₃ b) ⨯₃ (c ⨯₃ d)

/-- Three projective points are collinear (vanishing triple product). -/
def Collinear3 (p q r : Fin 3 → ℝ) : Prop := p ⬝ᵥ (q ⨯₃ r) = 0

/- **Pascal's theorem.** Six distinct points on a non-singular conic determine
three collinear intersection points `Aᵢ Bⱼ ∩ Aⱼ Bᵢ`. -/
/-- Source: B. Pascal, *Essay pour les coniques* (1640). Knill, *Some fundamental theorems in mathematics*, §146. Via leanprover/lean-eval@38361be, problem `pascal`. -/
public theorem_wanted pascal
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hMsymm : M.IsSymm) (hMdet : M.det ≠ 0)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Fin 3 → ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hdist : [a₁, a₂, a₃, b₁, b₂, b₃].Pairwise (fun v w => ¬ SamePoint v w))
    (hA₁ : OnConic M a₁) (hA₂ : OnConic M a₂) (hA₃ : OnConic M a₃)
    (hB₁ : OnConic M b₁) (hB₂ : OnConic M b₂) (hB₃ : OnConic M b₃) :
    Collinear3 (meet a₁ b₂ a₂ b₁) (meet a₁ b₃ a₃ b₁) (meet a₂ b₃ a₃ b₂)

end Geometry.PascalPappus

end MathlibExt.Geometry.PascalPappusWanted
