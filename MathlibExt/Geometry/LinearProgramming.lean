/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ConvexGeometry/LinearProgramming.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `lp_maximum_principle`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/lp_maximum_principle.toml`, rev 1, submitter Kim Morrison, status archived):
the structure `LinearProgram`, the definitions `LinearProgram.feasible` and
`LinearProgram.objective` and the statement of `simplex_algorithm`, with the docstrings and
comments they had in the wanted module `WantedExt/Geometry/LinearProgrammingWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Geometry.LinearProgrammingWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): `simplex_algorithm` was proved and moved from
`WantedExt/Geometry/LinearProgrammingWanted.lean` to this `MathlibExt` module, together with the
structure and the two definitions its statement uses, with unchanged names, statements and
docstrings; the imports of `Batteries.Util.ProofWanted` and of all of Mathlib were replaced by
narrower Mathlib imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`simplex_algorithm`, the lemmas and the auxiliary definition it uses, and the module
documentation.
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Optimal vertices of linear programs

A linear program in standard inequality form maximises the objective `c ⬝ᵥ x` over its feasible
region `{x | A *ᵥ x ≤ b ∧ 0 ≤ x}` in `Fin m → ℝ`. This file proves `simplex_algorithm`: if the
feasible region is nonempty and bounded, the objective attains its maximum on the region at an
extreme point (a vertex) of the region. This is the existence statement behind Dantzig's simplex
algorithm, which looks for an optimal solution among the vertices of the feasible region.

## Main results

* `LinearProgram.isClosed_feasible`, `LinearProgram.convex_feasible`: the feasible region is a
  closed convex set.
* `LinearProgram.isCompact_feasible`: a bounded feasible region is compact.
* `simplex_algorithm`: a linear program with a nonempty bounded feasible region has an optimal
  solution that is an extreme point of the feasible region.

## Proof outline

The feasible region `P` is an intersection of closed half-spaces, so it is closed, and compact
when it is bounded. The objective is a continuous linear functional `f`, so it attains its maximum
on `P`, and the set `F = {x ∈ P | ∀ y ∈ P, f y ≤ f x}` of maximisers is a nonempty exposed subset
of `P`. Hence `F` is compact and an extreme subset of `P`. By the Krein–Milman lemma
(`IsCompact.extremePoints_nonempty`), `F` has an extreme point, and an extreme point of an extreme
subset of `P` is an extreme point of `P`.

## Implementation notes

The structure, the two definitions and the theorem keep the full names they had in the wanted
module `WantedExt/Geometry/LinearProgrammingWanted.lean`, so their namespace still reads
`LinearProgrammingWanted`.

## References

* G. B. Dantzig (1947), simplex algorithm; O. Knill, *Some Fundamental Theorems in Mathematics*,
  arXiv:1807.08416v4, §101 (Linear programming). This is the source cited by problem
  `lp_maximum_principle` of the lean-eval benchmark (leanprover/lean-eval), from which the
  definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Geometry.LinearProgrammingWanted
namespace ConvexGeometry

open Matrix

/-- **Linear program.** A linear program in standard inequality form with $m$ variables and
$n$ constraints is given by an objective vector $c \in \mathbb{R}^m$, a right-hand side
$b \in \mathbb{R}^n$ and an $n \times m$ real constraint matrix $A$; it stands for the problem
of maximising $c \cdot x$ over $x \in \mathbb{R}^m$ subject to $A x \le b$ and $x \ge 0$. -/
structure LinearProgram (m n : ℕ) where
  /-- Coefficient vector of the objective `c · x`. -/
  c : Fin m → ℝ
  /-- Right-hand side of the inequality constraints `A x ≤ b`. -/
  b : Fin n → ℝ
  /-- Constraint matrix. -/
  A : Matrix (Fin n) (Fin m) ℝ

namespace LinearProgram

variable {m n : ℕ}

/-- **Feasible region of a linear program.** The feasible region of a linear program with
$m$ variables, constraint matrix $A$ and right-hand side $b$ is the set of vectors
$x \in \mathbb{R}^m$ with $A x \le b$ and $x \ge 0$, both inequalities holding componentwise.
It is a convex polyhedron in $\mathbb{R}^m$. -/
def feasible (lp : LinearProgram m n) : Set (Fin m → ℝ) :=
  {x | lp.A *ᵥ x ≤ lp.b ∧ 0 ≤ x}

/-- **Objective function of a linear program.** The objective function of a linear program
with $m$ variables and objective vector $c \in \mathbb{R}^m$ is the map
$f \colon \mathbb{R}^m \to \mathbb{R}$ given by $f(x) = c \cdot x = \sum_i c_i x_i$. -/
def objective (lp : LinearProgram m n) (x : Fin m → ℝ) : ℝ :=
  lp.c ⬝ᵥ x

/-- The feasible region of a linear program is closed: it is cut out by the non-strict
inequalities `A *ᵥ x ≤ b` and `0 ≤ x` between continuous functions of `x`. -/
theorem isClosed_feasible (lp : LinearProgram m n) : IsClosed lp.feasible :=
  (isClosed_le (continuous_const.matrix_mulVec continuous_id) continuous_const).inter
    (isClosed_le continuous_const continuous_id)

/-- The feasible region of a linear program is convex. -/
theorem convex_feasible (lp : LinearProgram m n) : Convex ℝ lp.feasible := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, add_nonneg (smul_nonneg ha hx.2) (smul_nonneg hb hy.2)⟩
  calc lp.A *ᵥ (a • x + b • y) = a • (lp.A *ᵥ x) + b • (lp.A *ᵥ y) := by
        rw [mulVec_add, mulVec_smul, mulVec_smul]
    _ ≤ a • lp.b + b • lp.b :=
        add_le_add (smul_le_smul_of_nonneg_left hx.1 ha) (smul_le_smul_of_nonneg_left hy.1 hb)
    _ = lp.b := by rw [← add_smul, hab, one_smul]

/-- A bounded feasible region of a linear program is compact. -/
theorem isCompact_feasible (lp : LinearProgram m n) (h : Bornology.IsBounded lp.feasible) :
    IsCompact lp.feasible :=
  Metric.isCompact_of_isClosed_isBounded lp.isClosed_feasible h

/-- The objective function of a linear program, as a continuous linear functional. -/
private def objectiveCLM (lp : LinearProgram m n) : StrongDual ℝ (Fin m → ℝ) where
  toFun := lp.objective
  map_add' := dotProduct_add lp.c
  map_smul' r x := dotProduct_smul r lp.c x
  cont := continuous_const.dotProduct continuous_id

end LinearProgram

/-- A continuous linear functional attains its maximum on a nonempty compact set at an extreme
point of the set. The maximisers form a nonempty compact exposed subset, whose extreme points
(given by the Krein–Milman lemma) are extreme points of the whole set. -/
private theorem exists_isMaxOn_mem_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (l : StrongDual ℝ E) : ∃ x ∈ s, IsMaxOn l s x ∧ x ∈ s.extremePoints ℝ := by
  have hexp : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, l y ≤ l x} := fun _ => ⟨l, rfl⟩
  obtain ⟨z, hz, hzmax⟩ := hs.exists_isMaxOn hne l.continuous.continuousOn
  obtain ⟨x, hx⟩ := (hexp.isCompact hs).extremePoints_nonempty ⟨z, hz, hzmax⟩
  exact ⟨x, hx.1.1, hx.1.2, hexp.isExtreme.extremePoints_subset_extremePoints hx⟩

/- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
/-- **Optimal vertices of linear programs.** Consider a linear program with $m$ variables and
objective vector $c \in \mathbb{R}^m$, and let $P \subseteq \mathbb{R}^m$ be its feasible region
and $f(x) = c \cdot x$ its objective function. If $P$ is nonempty and bounded, then some
$x \in P$ maximises $f$ on $P$ and is an extreme point of $P$, that is, $x$ does not lie in the
open segment between two distinct points of $P$.

Source: G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `lp_maximum_principle`. -/
theorem simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (hfeas : lp.feasible.Nonempty) (hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible :=
  exists_isMaxOn_mem_extremePoints (lp.isCompact_feasible hbdd) hfeas lp.objectiveCLM

end ConvexGeometry

end MathlibExt.Geometry.LinearProgrammingWanted
