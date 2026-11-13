/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Steinhaus' lattice point problem (Erdős Problem 215)

Erdős Problem 215 (Steinhaus): is there `S ⊆ ℝ²` such that every set congruent to `S` (after a
translation and rotation) contains exactly one point of `ℤ²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace MathlibExt.Geometry.SteinhausLatticeSetErdosProblem215Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #215, https://www.erdosproblems.com/215 (status PROVED
(LEAN)). UnsolvedMath record UM-30006770 (`EP-215`), dataset ulamai/UnsolvedMath v1.8.0.

The plane is `ℂ`, a rotation followed by a translation is `w ↦ u w + t` with `|u| = 1`, and `ℤ²` is
`{a + b i : a, b ∈ ℤ}`. Compared with the formal-conjectures statement `ErdosProblems/215.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 215 (Steinhaus): there is `S ⊆ ℝ²`, viewed as `ℂ`, such that every image of `S`
under a rotation and translation `w ↦ u w + t` (`|u| = 1`) contains exactly one point of `ℤ²`. -/
def steinhausLatticeSetExists : Prop :=
  ∃ S : Set ℂ, ∀ u t : ℂ, ‖u‖ = 1 →
    ∃! z : ℂ, z ∈ (fun w => u * w + t) '' S ∧ ∃ a b : ℤ, z = a + b * Complex.I

/--
Resolved true: Jackson and Mauldin constructed, using the axiom of choice, a set `S ⊆ ℝ²` meeting
every isometric copy of `ℤ²` in exactly one point; then every rotated and translated copy of `S`
contains exactly one lattice point. erdosproblems.com/215 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #215, https://www.erdosproblems.com/215 (status PROVED (LEAN));
resolution: S. Jackson and R. D. Mauldin, On a lattice problem of H. Steinhaus, J. Amer. Math. Soc.
15 (2002), 817-856, main theorem: a set meeting every isometric copy of ℤ² in exactly one point,
constructed with the axiom of choice (erdosproblems.com/215),
https://doi.org/10.1090/S0894-0347-02-00400-9.
-/
public theorem_wanted steinhausLatticeSetExists_holds : steinhausLatticeSetExists

end MathlibExt.Geometry.SteinhausLatticeSetErdosProblem215Wanted
