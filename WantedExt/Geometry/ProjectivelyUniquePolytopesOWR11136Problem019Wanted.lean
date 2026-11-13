/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely many projectively unique d-polytopes? (Oberwolfach Reports 44/2011)

Oberwolfach workshop Discrete Geometry (2011), G. M. Ziegler (joint work with K. Adiprasito),
Polytopes with low-dimensional realization spaces, Question 1: "Is it true that, up to projective
transformations, there are only finitely many combinatorial types of `d`-dimensional convex
polytopes?" (conjectured by Shephard and McMullen). Read, as in the report's Section 2 and in
Adiprasito-Ziegler's Problem P-S: for each `d`, are there only finitely many combinatorial types of
projectively unique `d`-polytopes?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.ProjectivelyUniquePolytopesOWR11136Problem019Wanted

/-!
Source: G. M. Ziegler (joint work with K. Adiprasito), Polytopes with low-dimensional realization
spaces, in Discrete Geometry, Oberwolfach Reports 8 (2011), Report 44/2011, pp. 2522-2525, Question
1, DOI 10.4171/OWR/2011/44. UnsolvedMath record UM-30001891 (`OWR-11136-019`), dataset
ulamai/UnsolvedMath v1.8.0.

Question 1 as printed omits "projectively unique" (literally every `d ≥ 2` has infinitely many
combinatorial types, e.g. `n`-gons); the report's definitions and its answer for `d ≤ 3` (finitely
many: the triangle, the square and four 3-polytopes) fix the intended question, which is Problem P-S
of Perles and Shephard in Adiprasito-Ziegler's paper (that paper cites this report as [Zie11] for
Question 2, its Problem L-S, and presents its Theorem II as the solution of Problem P-S). A
`d`-polytope is given by its vertex set (finite, affinely spanning `ℝ^d`, in convex position in the
sense of Mathlib's `ConvexIndependent`); facets are the vertex sets cut out by supporting
hyperplanes that span a hyperplane; a combinatorial equivalence is a bijection of vertex sets
mapping facets exactly onto facets. A polytope is projectively unique when every combinatorial
equivalence onto another `d`-polytope is induced by an admissible projective transformation
(invertible `(d + 1) × (d + 1)` matrix, denominator positive on the polytope): this is the report's
"`PGL(ℝ^d)` acts transitively on `R₀(P)`" for labeled realizations. Report Question 2 (growth of the
realization space dimension) is not formalized.
-/

/-- `V` is the vertex set of a `d`-dimensional convex polytope in `ℝ^d`: a finite set whose affine
span is all of `ℝ^d` and which is in convex position (Mathlib's `ConvexIndependent`: no point of `V`
lies in the convex hull of the others). -/
def IsPolytopeVertexSet {d : ℕ} (V : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  affineSpan ℝ (V : Set (EuclideanSpace ℝ (Fin d))) = ⊤ ∧
    ConvexIndependent ℝ ((↑) : ↥(V : Set (EuclideanSpace ℝ (Fin d))) → EuclideanSpace ℝ (Fin d))

/-- `F` is the vertex set of a facet of the polytope with vertex set `V`: the points of `V` on
which some nonzero linear functional attains its maximum over `V`, spanning an affine subspace of
dimension `d - 1`. -/
def IsFacetVertexSet {d : ℕ} (V F : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  F ⊆ V ∧ (∃ (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ℝ), ℓ ≠ 0 ∧ (∀ v ∈ V, ℓ v ≤ c) ∧
    ∀ v ∈ V, (v ∈ F ↔ ℓ v = c)) ∧
    Module.finrank ℝ (vectorSpan ℝ (F : Set (EuclideanSpace ℝ (Fin d)))) + 1 = d

/-- `f` is a combinatorial equivalence between the polytopes with vertex sets `V` and `W`: a
bijection of vertex sets carrying facets exactly onto facets (vertex-facet incidences determine
the face lattice). -/
def IsCombinatorialEquivalence {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (V W : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  Set.BijOn f V W ∧ ∀ F ⊆ V, (IsFacetVertexSet V F ↔ IsFacetVertexSet W (F.image f))

/-- Homogeneous coordinates `(x, 1) ∈ ℝ^{d+1}` of a point `x ∈ ℝ^d`. -/
def homog {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : Fin (d + 1) → ℝ :=
  Fin.snoc (fun i => x i) 1

/-- The projective transformation of `ℝ^d` given by an invertible `(d+1) × (d+1)` matrix `M`:
`x ↦ (M (x, 1))_{≤ d} / (M (x, 1))_{d+1}`. -/
noncomputable def projMap {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i =>
    (M.mulVec (homog x)) i.castSucc / (M.mulVec (homog x)) (Fin.last d)

/-- The polytope with vertex set `V` is projectively unique: every combinatorial equivalence onto
the vertex set of another `d`-polytope is induced by an admissible projective transformation
(invertible matrix, denominator positive on `V`, hence on the polytope). -/
def IsProjectivelyUnique {d : ℕ} (V : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ (W : Finset (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    IsPolytopeVertexSet W → IsCombinatorialEquivalence f V W →
      ∃ M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ, M.det ≠ 0 ∧
        (∀ v ∈ V, 0 < (M.mulVec (homog v)) (Fin.last d)) ∧ ∀ v ∈ V, projMap M v = f v

/-- Problem of Perles and Shephard (Question 1 of Oberwolfach Report 44/2011): for each fixed
dimension `d`, there are only finitely many combinatorial types of projectively unique
`d`-polytopes, i.e. finitely many of them represent every type. -/
def finitelyManyProjectivelyUniqueTypes : Prop :=
  ∀ d : ℕ, ∃ L : Finset (Finset (EuclideanSpace ℝ (Fin d))),
    ∀ V : Finset (EuclideanSpace ℝ (Fin d)), IsPolytopeVertexSet V → IsProjectivelyUnique V →
      ∃ W ∈ L, ∃ f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        IsCombinatorialEquivalence f V W

/--
Resolved false: Adiprasito and Ziegler constructed, for each `d ≥ 69`, an infinite family of
combinatorially distinct projectively unique `d`-polytopes, answering Problem P-S of Perles and
Shephard negatively; so for `d = 69` there are infinitely many combinatorial types. Source: G. M.
Ziegler (joint work with K. Adiprasito), Polytopes with low-dimensional realization spaces, in
Discrete Geometry, Oberwolfach Reports 8 (2011), Report 44/2011, pp. 2522-2525, Question 1, DOI
10.4171/OWR/2011/44; resolution: K. Adiprasito and G. M. Ziegler, Many projectively unique
polytopes, Invent. Math. 199 (2015), 581-652, arXiv:1212.5812, Theorem II: for each d ≥ 69 there is
an infinite family of distinct d-dimensional polytopes PCCTP_d[n], n ≥ 1, with 12(n + 1) + 60 + d
vertices, all projectively unique (answering Problem P-S: is the number of combinatorial types of
projectively unique d-polytopes finite for each fixed d ≥ 2?), https://arxiv.org/abs/1212.5812.
-/
public theorem_wanted finitelyManyProjectivelyUniqueTypes_refuted :
    ¬ finitelyManyProjectivelyUniqueTypes

end MathlibExt.Geometry.ProjectivelyUniquePolytopesOWR11136Problem019Wanted
