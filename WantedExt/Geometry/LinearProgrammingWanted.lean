/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear programming: maximum principle and vertex optimality

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ConvexGeometry.LinearProgramming` — lp_maximum_principle (manifest `manifests/problems/lp_maximum_principle.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.LinearProgrammingWanted` namespace. Mathematical
statements are unchanged. Source: G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.LinearProgrammingWanted
namespace ConvexGeometry

/-!
# Linear programming: maximum principle and vertex optimality

§101 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Maximum principle** (main): a local maximiser of a linear program's
  objective on the feasible region is automatically a global maximiser, and
  whenever the objective is non-constant (`c ≠ 0`) the maximiser lies on the
  topological frontier of the feasible region.
* **Vertex optimality** (additional, the existence content of Dantzig's simplex
  algorithm): every linear program with a nonempty bounded feasible region
  attains its optimum at an extreme point (vertex) of that region.

The program is the standard inequality form `maximise c · x` subject to
`A x ≤ b` and `0 ≤ x`. mathlib has the convex-geometry primitives used here
(`IsLocalMaxOn`, `IsMaxOn`, `frontier`, `Set.extremePoints`, Krein–Milman) but
neither the LP maximum principle nor the existence of an optimal vertex as named
results.
-/

open Matrix

/-- A **linear program** in standard inequality form on `ℝ^m` with `n`
constraints: maximise `c · x` subject to `A x ≤ b` and `0 ≤ x`. -/
structure LinearProgram (m n : ℕ) where
  /-- Coefficient vector of the objective `c · x`. -/
  c : Fin m → ℝ
  /-- Right-hand side of the inequality constraints `A x ≤ b`. -/
  b : Fin n → ℝ
  /-- Constraint matrix. -/
  A : Matrix (Fin n) (Fin m) ℝ

namespace LinearProgram

variable {m n : ℕ}

/-- The **feasible region** of `lp`: the vectors `x ∈ ℝ^m` with `A x ≤ b` and
`0 ≤ x`, a convex polyhedron in `ℝ^m`. -/
def feasible (lp : LinearProgram m n) : Set (Fin m → ℝ) :=
  {x | lp.A *ᵥ x ≤ lp.b ∧ 0 ≤ x}

/-- The **objective** `f(x) = c · x`. -/
def objective (lp : LinearProgram m n) (x : Fin m → ℝ) : ℝ :=
  lp.c ⬝ᵥ x

end LinearProgram

/- **Maximum principle for linear programming** (§101). A local maximiser of
the LP objective on the feasible region is automatically a global maximiser; and
whenever the objective is non-constant (`c ≠ 0`), the maximiser lies on the
topological frontier of the feasible region. -/
/-- Source: G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `lp_maximum_principle`. -/
public theorem_wanted lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible)

/- **Vertex optimality** (§101; the existence content of Dantzig's 1947 simplex
algorithm). Every linear program with a nonempty bounded feasible region admits a
global maximiser that is an extreme point (vertex) of the feasible region. -/
/-- Source: G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `lp_maximum_principle`. -/
public theorem_wanted simplex_algorithm {m n : ℕ} (lp : LinearProgram m n)
    (_hfeas : lp.feasible.Nonempty) (_hbdd : Bornology.IsBounded lp.feasible) :
    ∃ x ∈ lp.feasible, IsMaxOn lp.objective lp.feasible x ∧
      x ∈ Set.extremePoints ℝ lp.feasible

end ConvexGeometry

end MathlibExt.Geometry.LinearProgrammingWanted
