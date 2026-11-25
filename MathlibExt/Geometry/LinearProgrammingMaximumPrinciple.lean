/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ConvexGeometry/LinearProgramming.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), at commit 38361be884302c7edce1908c4aef8296eb2cb27e:
the statement and source attribution of `lp_maximum_principle`, via
`WantedExt/Geometry/LinearProgrammingWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

ATLAS moved the statement to this module and supplied the proof.
-/

module

public import MathlibExt.Geometry.LinearProgramming
public import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Convex.Extrema
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Maximum principle for linear programming

The theorem `lp_maximum_principle` shows that a feasible local maximiser of a linear program is
global. If the objective vector is nonzero, the maximiser lies on the frontier of the feasible
region.
-/

public section

namespace MathlibExt.Geometry.LinearProgrammingWanted.ConvexGeometry

open Matrix Set

/-- **Maximum principle for linear programming.** Consider a linear program with $m$ variables
and objective vector $c \in \mathbb{R}^m$, let $P \subseteq \mathbb{R}^m$ be its feasible region
and $f(x) = c \cdot x$ its objective function, and let $x \in P$ be a local maximiser of $f$ on
$P$, that is, $f(y) \le f(x)$ for all $y \in P$ in some neighbourhood of $x$. Then $x$ is a
global maximiser of $f$ on $P$, and if $c \ne 0$ then $x$ lies on the topological boundary of
$P$ in $\mathbb{R}^m$.

Source: G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `lp_maximum_principle`. -/
theorem lp_maximum_principle {m n : ℕ} (lp : LinearProgram m n)
    (x : Fin m → ℝ) (_hx : x ∈ lp.feasible)
    (_hlocal : IsLocalMaxOn lp.objective lp.feasible x) :
    IsMaxOn lp.objective lp.feasible x ∧
      (lp.c ≠ 0 → x ∈ frontier lp.feasible) := by
  let f := dotProductBilin ℝ ℝ lp.c
  refine ⟨IsMaxOn.of_isLocalMaxOn_of_concaveOn _hx _hlocal
    (f.concaveOn lp.convex_feasible), ?_⟩
  intro hc
  refine (mem_frontier_iff_notMem_interior _hx).2 fun hint => ?_
  have hlocal : IsLocalMax f x := _hlocal.isLocalMax (mem_interior_iff_mem_nhds.1 hint)
  have hle := IsMaxOn.of_isLocalMax_of_convex_univ hlocal (f.concaveOn convex_univ) (x + lp.c)
  have hpos : 0 < f lp.c := by
    change 0 < lp.c ⬝ᵥ lp.c
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (lp.c i))
      (fun h => hc (dotProduct_self_eq_zero.mp h.symm))
  rw [map_add] at hle
  exact (not_lt_of_ge hle) (lt_add_of_pos_right _ hpos)

end MathlibExt.Geometry.LinearProgrammingWanted.ConvexGeometry
