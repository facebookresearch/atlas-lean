/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rational reduced homology of finite abstract simplicial complexes

Shared helper for the UnsolvedMath entries on Stanley's Positivity Problems 5 and 6
(`WantedExt/Combinatorics/AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted.lean` and
`WantedExt/Combinatorics/CohenMacaulayPartitionabilityAMR156Problem0005Wanted.lean`), so both speak
about the same complexes, links and Betti numbers.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-!
A finite abstract simplicial complex on the vertex set `ℕ` is a finite family `K` of finite sets
closed under taking subsets; it contains the empty face unless it is the void complex `∅`. The
reduced rational homology is computed from the augmented simplicial chain complex: the faces with
`k` vertices span the chain group in degree `k - 1` (the empty face spans degree `-1`), and the
boundary of a face sends it to the alternating sum of its codimension-one faces, the sign being
`(-1)^i` when the `i`-th smallest vertex (counting from `0`) is removed.

Mathlib's `PreAbstractSimplicialComplex` is not used: its faces are nonempty, so it cannot tell the
void complex (acyclic) from `{∅}` (not acyclic, `H̃_{-1} = ℚ`), which is the link of a facet; the
acyclic-links condition of Problem 5 needs that distinction.
-/

/-- `K` is closed under taking subsets: a finite abstract simplicial complex on `ℕ`. -/
def IsSimplicialComplex (K : Finset (Finset ℕ)) : Prop :=
  ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

/-- The faces of `K` with exactly `k` vertices (the faces of dimension `k - 1`). -/
def facesOfCard (K : Finset (Finset ℕ)) (k : ℕ) : Finset (Finset ℕ) :=
  K.filter fun σ => σ.card = k

/-- The simplicial boundary matrix from the faces with `k + 1` vertices to the faces with `k`
vertices: the entry at `(τ, σ)` is `(-1)^i` when `τ` is `σ` with its `i`-th smallest vertex
removed, and `0` otherwise. For `k = 0` it is the augmentation (every vertex maps to `∅`). -/
def boundaryMatrix (K : Finset (Finset ℕ)) (k : ℕ) :
    Matrix (facesOfCard K k) (facesOfCard K (k + 1)) ℚ :=
  fun τ σ => ∑ v ∈ σ.1, if σ.1.erase v = τ.1 then (-1) ^ (σ.1.filter (· < v)).card else 0

/-- The reduced rational Betti number `dim H̃_{k-1}(K; ℚ)`, indexed by the number `k` of vertices of
the faces in that degree: `f - rank ∂_out - rank ∂_in`, where `f` is the number of faces with `k`
vertices, `∂_out` the boundary map out of them (zero for `k = 0`) and `∂_in` the boundary map from
the faces with `k + 1` vertices into them. -/
noncomputable def reducedBetti (K : Finset (Finset ℕ)) (k : ℕ) : ℤ :=
  ((facesOfCard K k).card : ℤ) - (if k = 0 then 0 else ((boundaryMatrix K (k - 1)).rank : ℤ)) -
    (boundaryMatrix K k).rank

/-- `K` is acyclic over `ℚ`: all of its reduced rational homology vanishes (the void complex is
acyclic; the complex `{∅}` is not, since `H̃_{-1}({∅}; ℚ) = ℚ`). -/
def IsRationallyAcyclic (K : Finset (Finset ℕ)) : Prop :=
  ∀ k, reducedBetti K k = 0

/-- The link `link_K(F) = {G ∈ K | G ∩ F = ∅, G ∪ F ∈ K}` of a face `F`. -/
def link (K : Finset (Finset ℕ)) (F : Finset ℕ) : Finset (Finset ℕ) :=
  K.filter fun G => Disjoint G F ∧ G ∪ F ∈ K

/-- The largest number of vertices of a face of `K` (`dim K + 1`; `0` for `∅` and `{∅}`). -/
def topCard (K : Finset (Finset ℕ)) : ℕ :=
  K.sup Finset.card

/-- `F` is a facet (a maximal face) of `K`. -/
def IsFacet (K : Finset (Finset ℕ)) (F : Finset ℕ) : Prop :=
  F ∈ K ∧ ∀ G ∈ K, F ⊆ G → G = F

end MathlibExt.Combinatorics.RationalSimplicialHomologyShared
