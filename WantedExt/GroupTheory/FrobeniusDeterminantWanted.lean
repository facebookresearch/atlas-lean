/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Frobenius determinant theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.FrobeniusDeterminant` — frobenius_group_determinant (manifest `manifests/problems/frobenius_group_determinant.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.FrobeniusDeterminantWanted` namespace. Mathematical
statements are unchanged. Source: Knill, *Some fundamental theorems in mathematics*, §171.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusDeterminantWanted
namespace RepresentationTheory.FrobeniusDeterminant

/-!
# Frobenius determinant theorem (Dedekind's group determinant)

`frobenius_group_determinant`: the group determinant `Θ(G) = det(A)` of the
group matrix `A_{gh} = x_{gh}` factors into irreducible polynomials, each to the
power of its own total degree, with the factors pairwise non-associated and
their number equal to the number of conjugacy classes of `G`. Trusted helpers
`groupMatrix`, `groupDeterminant` (non-holes). Category-(b) candidate from §171
of the Knill survey.
-/

open MvPolynomial Matrix


/-- **Group matrix.** For a finite group $G$, the group matrix of Dedekind and Frobenius is the
$G \times G$ matrix over the polynomial ring $\mathbb{C}[x_g : g \in G]$ whose entry at $(g, h)$ is
the variable $x_{gh}$. -/
noncomputable def groupMatrix (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Matrix G G (MvPolynomial G ℂ) :=
  fun g h => MvPolynomial.X (g * h)

/-- **Group determinant.** For a finite group $G$, the group determinant $\Theta(G)$ is the
determinant of the group matrix of $G$, the $G \times G$ matrix over $\mathbb{C}[x_g : g \in G]$
whose entry at $(g, h)$ is the variable $x_{gh}$; it is a polynomial in these variables. -/
noncomputable def groupDeterminant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    MvPolynomial G ℂ :=
  (groupMatrix G).det

/-- **Frobenius determinant theorem.** Let $G$ be a finite group and let $r$ be the number of
conjugacy classes of $G$. Then there exist polynomials $p_1, \dots, p_r$ in
$\mathbb{C}[x_g : g \in G]$ such that each $p_j$ is irreducible, $p_i$ and $p_j$ are not associated
for $i \neq j$, and the group determinant of $G$ equals $\prod_{j=1}^{r} p_j^{\deg p_j}$, where
$\deg p_j$ is the total degree of $p_j$.

Source: Knill, *Some fundamental theorems in mathematics*, §171. Via leanprover/lean-eval@38361be, problem `frobenius_group_determinant`.
-/
public theorem_wanted frobenius_group_determinant
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (r : ℕ) (p : Fin r → MvPolynomial G ℂ),
      r = Nat.card (ConjClasses G) ∧
      (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, (p j) ^ (p j).totalDegree

end RepresentationTheory.FrobeniusDeterminant

end MathlibExt.GroupTheory.FrobeniusDeterminantWanted
