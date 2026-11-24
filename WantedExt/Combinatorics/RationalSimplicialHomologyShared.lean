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

/-- **Finite abstract simplicial complex.** A finite family $K$ of finite subsets of
$\mathbb{N}$ is a simplicial complex when it is closed under taking subsets: for every
$\sigma \in K$ and every $\tau \subseteq \sigma$, we have $\tau \in K$. -/
def IsSimplicialComplex (K : Finset (Finset ℕ)) : Prop :=
  ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

/-- **Faces with a given number of vertices.** For a finite family $K$ of finite subsets of
$\mathbb{N}$ and $k \in \mathbb{N}$, the faces of $K$ with $k$ vertices are the members
$\sigma \in K$ with exactly $k$ elements (the faces of dimension $k - 1$). -/
def facesOfCard (K : Finset (Finset ℕ)) (k : ℕ) : Finset (Finset ℕ) :=
  K.filter fun σ => σ.card = k

/-- **Simplicial boundary matrix.** For a finite family $K$ of finite subsets of $\mathbb{N}$ and
$k \in \mathbb{N}$, the boundary matrix $\partial_k$ of $K$ is the matrix over $\mathbb{Q}$ whose
rows are indexed by the faces of $K$ with $k$ vertices and whose columns are indexed by the faces
of $K$ with $k + 1$ vertices; its entry at $(\tau, \sigma)$ is $(-1)^i$ when $\tau$ is obtained
from $\sigma$ by removing its $i$-th smallest vertex, counting from $i = 0$, and $0$ otherwise.

It represents the boundary map from the faces with $k + 1$ vertices to the faces with $k$
vertices. For $k = 0$ it is the augmentation: every vertex has entry $1$ in the row of the empty
face. -/
def boundaryMatrix (K : Finset (Finset ℕ)) (k : ℕ) :
    Matrix (facesOfCard K k) (facesOfCard K (k + 1)) ℚ :=
  fun τ σ => ∑ v ∈ σ.1, if σ.1.erase v = τ.1 then (-1) ^ (σ.1.filter (· < v)).card else 0

/-- **Reduced rational Betti numbers.** For a finite family $K$ of finite subsets of $\mathbb{N}$
and $k \in \mathbb{N}$, let $f_k$ be the number of faces of $K$ with $k$ vertices and let
$\partial_k$ be the boundary matrix of $K$ from the faces with $k + 1$ vertices to the faces with
$k$ vertices. The reduced Betti number of $K$ indexed by $k$ is the integer
$f_k - \operatorname{rank} \partial_{k-1} - \operatorname{rank} \partial_k$, with ranks over
$\mathbb{Q}$, where the term $\operatorname{rank} \partial_{k-1}$ is omitted when $k = 0$.

When $K$ is a simplicial complex this is $\dim_{\mathbb{Q}} \tilde H_{k-1}(K; \mathbb{Q})$, the
reduced rational homology in degree $k - 1$, indexed by the number $k$ of vertices of its faces. -/
noncomputable def reducedBetti (K : Finset (Finset ℕ)) (k : ℕ) : ℤ :=
  ((facesOfCard K k).card : ℤ) - (if k = 0 then 0 else ((boundaryMatrix K (k - 1)).rank : ℤ)) -
    (boundaryMatrix K k).rank

/-- **Rationally acyclic complexes.** A finite family $K$ of finite subsets of $\mathbb{N}$ is
rationally acyclic when its reduced Betti number indexed by $k$ is $0$ for every $k \in \mathbb{N}$.

For a simplicial complex this says that all reduced rational homology of $K$ vanishes. The void
complex is acyclic; the complex $\{\emptyset\}$ is not, since
$\tilde H_{-1}(\{\emptyset\}; \mathbb{Q}) = \mathbb{Q}$. -/
def IsRationallyAcyclic (K : Finset (Finset ℕ)) : Prop :=
  ∀ k, reducedBetti K k = 0

/-- **Link.** For a finite family $K$ of finite subsets of $\mathbb{N}$ and a finite set
$F \subseteq \mathbb{N}$, the link of $F$ in $K$ is
$\operatorname{link}_K(F) = \{G \in K \mid G \cap F = \emptyset,\ G \cup F \in K\}$. -/
def link (K : Finset (Finset ℕ)) (F : Finset ℕ) : Finset (Finset ℕ) :=
  K.filter fun G => Disjoint G F ∧ G ∪ F ∈ K

/-- **Largest face size.** For a finite family $K$ of finite subsets of $\mathbb{N}$, the largest
face size of $K$ is the maximum number of elements of a member of $K$, and $0$ when $K$ is empty.

For a nonempty simplicial complex it is $\dim K + 1$; it is $0$ for both the void complex
$\emptyset$ and $\{\emptyset\}$. -/
def topCard (K : Finset (Finset ℕ)) : ℕ :=
  K.sup Finset.card

/-- **Facet.** For a finite family $K$ of finite subsets of $\mathbb{N}$, a finite set
$F \subseteq \mathbb{N}$ is a facet of $K$ when $F \in K$ and $F$ is maximal under inclusion in
$K$: every $G \in K$ with $F \subseteq G$ equals $F$. -/
def IsFacet (K : Finset (Finset ℕ)) (F : Finset ℕ) : Prop :=
  F ∈ K ∧ ∀ G ∈ K, F ⊆ G → G = F

end MathlibExt.Combinatorics.RationalSimplicialHomologyShared
