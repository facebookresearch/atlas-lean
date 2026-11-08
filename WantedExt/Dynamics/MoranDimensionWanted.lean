/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Moran's equality for affine-symmetric iterated function systems

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.MoranDimension` — moran_equality_affine (manifest `manifests/problems/moran_equality_affine.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.MoranDimensionWanted` namespace. Mathematical
statements are unchanged. Source: P. A. P. Moran, *Additive functions of intervals and Hausdorff measure*, Proc. Cambridge Philos. Soc. 42 (1946); J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981). Knill, *Some fundamental theorems in mathematics*, §105.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.MoranDimensionWanted
namespace Dynamics

/-!
# Moran's equality for affine-symmetric iterated function systems

`moran_equality_affine` is the equality case of the Moran–Hutchinson dimension
theorem (Moran 1946, Hutchinson 1981): for an iterated function system on `ℝᵈ`
whose maps are affine with a common contraction factor `λ ∈ (0,1)` and
orthogonal linear parts, satisfying the open set condition, the Hausdorff
dimension of the attractor equals the similarity dimension — here
`−log n / log λ`.

The trusted helper definitions (`IsAttractor`, `IsAffineSymmetricIFS`,
`OpenSetCondition`) are non-holes. Mathlib has `dimH`, `μH[d]`,
`ContractingWith`, and the Hausdorff (e)metric on compacts, but no iterated
function systems, Hutchinson operator, attractor, or similarity dimension.

This is a category-(b) candidate from §105 of the Knill survey
(`sections/105-fractals.md`). (The general Moran–Hutchinson *inequality* and the
Cantor-set example, the section's other statements, are not included here.)
-/

open scoped Topology ENNReal NNReal
open MeasureTheory

/-- A set `S ⊆ X` is an **attractor** of the IFS `f : Fin n → X → X` if it is
nonempty compact and fixed by the Hutchinson operator `H(A) = ⋃ᵢ fᵢ(A)`. -/
def IsAttractor {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : Fin n → X → X) (S : Set X) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ S = ⋃ i, f i '' S

/-- An IFS on `ℝᵈ` is **affine-symmetric** with common contraction factor
`λ ∈ (0,1)` if each map is `fᵢ(x) = λ · Aᵢ(x) + βᵢ` with `Aᵢ` a linear isometry
(orthogonal transformation) and `βᵢ` a translation. -/
def IsAffineSymmetricIFS {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Prop :=
  0 < lam ∧ lam < 1 ∧
  ∃ A : Fin n → (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)),
    ∃ β : Fin n → EuclideanSpace ℝ (Fin d),
      ∀ i x, f i x = lam • A i x + β i

/-- The **open set condition**: a nonempty open `G` with `fᵢ(G) ⊆ G` for all `i`
and the images `fᵢ(G)` pairwise disjoint. -/
def OpenSetCondition {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ G : Set (EuclideanSpace ℝ (Fin d)), IsOpen G ∧ G.Nonempty ∧
    (∀ i, f i '' G ⊆ G) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (f i '' G) (f j '' G))

/- **Moran's equality for affine-symmetric IFS.** For an affine-symmetric IFS
on `ℝᵈ` with common contraction factor `λ ∈ (0,1)`, orthogonal linear parts, and
the open set condition, the Hausdorff dimension of the attractor is
`−log n / log λ` (positive since `λ < 1`). -/
/-- Source: P. A. P. Moran, *Additive functions of intervals and Hausdorff measure*, Proc. Cambridge Philos. Soc. 42 (1946); J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981). Knill, *Some fundamental theorems in mathematics*, §105. Via leanprover/lean-eval@38361be, problem `moran_equality_affine`. -/
public theorem_wanted moran_equality_affine
    {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h_aff : IsAffineSymmetricIFS f lam)
    (h_osc : OpenSetCondition f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsAttractor f S) :
    dimH S = ENNReal.ofReal (- Real.log n / Real.log lam)

end Dynamics

end MathlibExt.Dynamics.MoranDimensionWanted
