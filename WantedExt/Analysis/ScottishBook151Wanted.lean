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

/-- The closed cube `[-1, 1]³` in `ℝ³`. -/
def Cube : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}

/-- The union of the edges of the cube `[-1, 1]³`: points of the cube with
at least two coordinates equal to `1` or `-1`. -/
def CubeEdges : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∃ i j, i ≠ j ∧ (x i = 1 ∨ x i = -1) ∧ (x j = 1 ∨ x j = -1)}

/--
There is a nonzero harmonic function, defined in a region containing a cube
in its interior, which vanishes on all the edges of the cube. The function
is harmonic on an open region `U` whose interior contains the cube
`[-1, 1]³`, vanishes on every point of the cube's edges, and is nonzero
somewhere in `U`.
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
