/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gallai triangles in line arrangements (Erdős Problem 209)

Erdős Problem 209: let `A` be a finite family of `d ≥ 4` pairwise non-parallel lines in `ℝ²` with no
point on four or more of them. Must there be a Gallai triangle: three lines of `A` meeting pairwise
in three points, each of which lies on exactly two lines of `A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.GallaiTriangleLineArrangementErdosProblem209Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #209, https://www.erdosproblems.com/209 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006766 (`EP-209`), dataset ulamai/UnsolvedMath v1.8.0.

Lines are affine subspaces of `ℝ²` with one-dimensional direction; the multiplicity of a point is
the number of lines of `A` through it. The target is stated for some `d ≥ 4` (the strongest true
form, existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation asserts
a counterexample for every `d ≥ 4`: stronger than the source's negative answer, which needs one `d`,
and what Escudero proves. Escudero's configurations `A_{d,k}` are lines of the real plane given by
parametric equations, every two of which meet (his Lemma 1), so they are pairwise non-parallel and
all their vertices are points of `ℝ²`; his Gallai triangles (three lines whose three intersection
points have multiplicity `2`) are the ones defined here. Compared with the formal-conjectures
statement `ErdosProblems/209.lean` (there the weaker `¬ ∀ d`; no code imported).
-/

/-- `L` is a line: an affine subspace of `ℝ²` with one-dimensional direction. -/
def IsLine (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ L.direction = 1

open Classical in
/-- The number of lines of `A` through `p`. -/
noncomputable def lineMultiplicity (A : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (p : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (A.filter (fun L => p ∈ L)).card

/-- `A` has a Gallai triangle: three distinct lines of `A` meeting pairwise in three distinct
points, each of which lies on exactly two lines of `A`. -/
def HasGallaiTriangle (A : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A, L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁ p₂ p₃ : EuclideanSpace ℝ (Fin 2), p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
      p₁ ∈ L₂ ∧ p₁ ∈ L₃ ∧ p₂ ∈ L₁ ∧ p₂ ∈ L₃ ∧ p₃ ∈ L₁ ∧ p₃ ∈ L₂ ∧
      lineMultiplicity A p₁ = 2 ∧ lineMultiplicity A p₂ = 2 ∧ lineMultiplicity A p₃ = 2

/-- Erdős Problem 209, stated for some `d ≥ 4`: every family of `d` pairwise non-parallel lines in
`ℝ²` with no point on four or more of them has a Gallai triangle. -/
def lineArrangementHasGallaiTriangle : Prop :=
  ∃ d : ℕ, 4 ≤ d ∧ ∀ A : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))), A.card = d →
    (∀ L ∈ A, IsLine L) → (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬ L₁.Parallel L₂) →
    (∀ p, lineMultiplicity A p ≤ 3) → HasGallaiTriangle A

/--
Resolved false: Füredi and Palásti constructed, for `d ≥ 4` not divisible by `9`, arrangements of
`d` lines with no point on four lines and no Gallai triangle. Escudero's configurations of `d` lines
in the plane, any two of which meet and no four of which are concurrent (Lemma 1), have no Gallai
triangle (Theorem 1), which answers the question negatively for every `d ≥ 4`; erdosproblems.com/209
lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #209,
https://www.erdosproblems.com/209 (status DISPROVED (LEAN)); resolution: Z. Füredi and I. Palásti,
Arrangements of lines with a large number of triangles, Proc. Amer. Math. Soc. 92 (1984), 561-566 (d
not divisible by 9); J. G. Escudero, Gallai triangles in configurations of lines in the projective
plane, C. R. Math. Acad. Sci. Paris 354 (2016), 551-554 (all d ≥ 4), Escudero, Lemma 1 and Theorem
1: for each d ≥ 4, configurations of d lines in the plane, any two meeting, with no vertex on more
than three lines and no Gallai triangle; erdosproblems.com/209: false when 9 ∤ d (Füredi-Palásti)
and for all d ≥ 4 (Escudero), https://doi.org/10.1016/j.crma.2016.03.003.
-/
public theorem_wanted lineArrangementHasGallaiTriangle_refuted : ¬ lineArrangementHasGallaiTriangle

end MathlibExt.Geometry.GallaiTriangleLineArrangementErdosProblem209Wanted
