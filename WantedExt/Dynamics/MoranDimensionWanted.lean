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

/-- **Attractor of an iterated function system.** Let $X$ be a topological space and let
$(f_i)_{i < n}$ be a finite family of maps $X \to X$. A set $S \subseteq X$ is an attractor of the
family if it is nonempty and compact and is fixed by the Hutchinson operator, that is,
$S = \bigcup_{i < n} f_i(S)$. -/
def IsAttractor {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : Fin n → X → X) (S : Set X) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ S = ⋃ i, f i '' S

/-- **Affine-symmetric iterated function system.** Let $(f_i)_{i < n}$ be a finite family of maps
$f_i \colon \mathbb{R}^d \to \mathbb{R}^d$ on Euclidean space. The family is affine-symmetric with
common contraction factor $\lambda$ if $0 < \lambda < 1$ and there are linear isometries
$A_i \colon \mathbb{R}^d \to \mathbb{R}^d$ (orthogonal transformations) and vectors
$\beta_i \in \mathbb{R}^d$ such that $f_i(x) = \lambda A_i(x) + \beta_i$ for every $i < n$ and every
$x \in \mathbb{R}^d$. -/
def IsAffineSymmetricIFS {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Prop :=
  0 < lam ∧ lam < 1 ∧
  ∃ A : Fin n → (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)),
    ∃ β : Fin n → EuclideanSpace ℝ (Fin d),
      ∀ i x, f i x = lam • A i x + β i

/-- **Open set condition.** A finite family of maps $f_i \colon \mathbb{R}^d \to \mathbb{R}^d$,
$i < n$, satisfies the open set condition if there is a nonempty open set $G \subseteq \mathbb{R}^d$
such that $f_i(G) \subseteq G$ for every $i < n$ and the images $f_i(G)$ and $f_j(G)$ are disjoint
whenever $i \neq j$. -/
def OpenSetCondition {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ G : Set (EuclideanSpace ℝ (Fin d)), IsOpen G ∧ G.Nonempty ∧
    (∀ i, f i '' G ⊆ G) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (f i '' G) (f j '' G))

/- **Moran's equality for affine-symmetric IFS.** For an affine-symmetric IFS
on `ℝᵈ` with common contraction factor `λ ∈ (0,1)`, orthogonal linear parts, and
the open set condition, the Hausdorff dimension of the attractor is
`−log n / log λ` (positive since `λ < 1`). -/
/-- **Moran's equality for affine-symmetric iterated function systems.** Let $n \ge 1$ and let
$(f_i)_{i < n}$ be an affine-symmetric iterated function system on $\mathbb{R}^d$ with common
contraction factor $\lambda \in (0,1)$ that satisfies the open set condition. Then every attractor
$S \subseteq \mathbb{R}^d$ of the system has Hausdorff dimension
$$\dim_H S = -\frac{\log n}{\log \lambda}.$$

Source: P. A. P. Moran, *Additive functions of intervals and Hausdorff measure*, Proc. Cambridge Philos. Soc. 42 (1946); J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981). Knill, *Some fundamental theorems in mathematics*, §105. Via leanprover/lean-eval@38361be, problem `moran_equality_affine`. -/
public theorem_wanted moran_equality_affine
    {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h_aff : IsAffineSymmetricIFS f lam)
    (h_osc : OpenSetCondition f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsAttractor f S) :
    dimH S = ENNReal.ofReal (- Real.log n / Real.log lam)

end Dynamics

end MathlibExt.Dynamics.MoranDimensionWanted
