/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook151Wanted

/-- **The closed cube $[-1, 1]^3$.** The closed cube $[-1, 1]^3$ in $\mathbb{R}^3$: the set of
points of three-dimensional Euclidean space all of whose coordinates lie in $[-1, 1]$. -/
def Cube : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- **Edges of the cube $[-1, 1]^3$.** The union of the edges of the cube $[-1, 1]^3$ in
$\mathbb{R}^3$: the set of points $x$ with every coordinate in $[-1, 1]$ such that at least two
distinct coordinates $x_i$ and $x_j$ are each equal to $1$ or $-1$. -/
def CubeEdges : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∃ i j, i ≠ j ∧ (x i = 1 ∨ x i = -1) ∧ (x j = 1 ∨ x j = -1)}

/--
**Scottish Book Problem 151: a harmonic function vanishing on the edges of a cube.** There
exist an open set $U \subseteq \mathbb{R}^3$ whose interior contains the closed cube
$[-1, 1]^3$ and a function $f : \mathbb{R}^3 \to \mathbb{R}$ that is harmonic at every point of
$U$, vanishes at every point of the edges of the cube $[-1, 1]^3$, and satisfies $f(x) \neq 0$
for some $x \in U$.

Source: R. Wavre, Problem 151 of the Scottish Book; the affirmative answer
is given by I. Vasilyev, "On the zero sets of harmonic polynomials",
arXiv:2506.24116, Theorem 1, as reported in the 2026 survey "90+ years of
the Scottish Book" (arXiv:2603.27867). The typescript notes a prize of a
"fondue" in Geneva.
-/
theorem_wanted harmonicFunctionVanishesOnCubeEdges :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      IsOpen U ∧ Cube ⊆ interior U ∧ InnerProductSpace.HarmonicOnNhd f U ∧
        (∀ x ∈ CubeEdges, f x = 0) ∧ ∃ x ∈ U, f x ≠ 0

end MathlibExt.Analysis.ScottishBook151Wanted
