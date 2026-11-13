/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Platonic classification

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.PlatonicClassification` — platonic_classification (manifest `manifests/problems/platonic_classification.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.PlatonicClassificationWanted` namespace. Mathematical
statements are unchanged. Source: Euclid, Elements, Book XIII (~300 BC, p_3 = 5); L. Schläfli, Theorie der vielfachen Kontinuität (1852, posthumous publication; p_4 = 6, p_d = 3 for d ≥ 5). Listed as §42 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.PlatonicClassificationWanted
namespace Geometry
namespace PlatonicClassification

/-!
# Platonic classification

§42 of Knill's *Some Fundamental Theorems in Mathematics*. The count
`p_d` of regular convex `d`-polytopes (Platonic polytopes) up to
similarity is `p_2 = ∞` (regular polygons), `p_3 = 5` (Euclid XIII —
tetrahedron, cube, octahedron, dodecahedron, icosahedron), `p_4 = 6`
(Schläfli 1850s — 5-cell, 8-cell, 16-cell, 24-cell, 120-cell, 600-cell),
and `p_d = 3` for every `d ≥ 5` (regular simplex, hypercube,
cross-polytope).

mathlib has `convexHull`, `extremePoints`, `IsExposed`, `vectorSpan`,
`AffineIsometryEquiv`, and `Set.encard`, but **no convex-polytope
datatype**, no face lattice, no regular-polytope concept, and none of the
classification counts. The Challenge ships ~1.5 pages of definitions
(`ConvexPolytope`, `dim`, `IsFace`, `Flag`, `isSymmetry`, `IsRegular`,
`Similar`, `regularPolytopes`, `regularSimilar`, `platonicCount`) on top
of mathlib.
-/

open scoped Topology

/-- **Ambient Euclidean space of the Platonic classification.** For a natural number $n$, the real
Euclidean space $\mathbb{R}^n$: $n$-tuples of reals with the standard inner product and norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- **Convex polytope.** A convex polytope in $\mathbb{R}^n$ is given by its vertex set: a finite
nonempty set $V \subseteq \mathbb{R}^n$ that equals the set of extreme points of its convex hull
$\operatorname{conv}(V)$. The polytope itself is the convex set $\operatorname{conv}(V)$. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope

/-- **Underlying set of a convex polytope.** The underlying set of a convex polytope $P$ in
$\mathbb{R}^n$ is the convex hull of its vertex set. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))

/-- **Dimension of a convex polytope.** The dimension of a convex polytope
$P \subseteq \mathbb{R}^n$ is its affine dimension: the dimension of the real vector space
spanned by the differences $x - y$ of points $x, y \in P$. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)

/-- **Full-dimensional convex polytope.** A convex polytope $P \subseteq \mathbb{R}^n$ is
full-dimensional if its dimension equals $n$. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n

/-- **Face of a convex polytope.** A face of a convex polytope $P \subseteq \mathbb{R}^n$ is a
nonempty set of the form $\{x \in P : \ell(y) \le \ell(x) \text{ for all } y \in P\}$ for some
linear functional $\ell$ on $\mathbb{R}^n$, that is, the set of points where $\ell$ attains its
maximum over $P$. Taking $\ell = 0$ shows that $P$ itself is a face. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- **Affine dimension of a set.** For a subset $F \subseteq \mathbb{R}^n$, its affine dimension is
the dimension of the real vector space spanned by the differences $x - y$ with $x, y \in F$.
The empty set and every single point get dimension $0$. -/
noncomputable def faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

/-- **Flag of a convex polytope.** A flag of a convex polytope $P \subseteq \mathbb{R}^n$ is a
sequence $F_0, F_1, \dots, F_{n-1}$ of faces of $P$ such that each $F_k$ has affine dimension $k$
and $F_i \subsetneq F_j$ whenever $i < j$.

The definition applies to every $P$; it is used for full-dimensional $P$. -/
structure Flag {n : ℕ} (P : ConvexPolytope n) where
  face : Fin n → Set (E n)
  isFace : ∀ k, P.IsFace (face k)
  dim_eq : ∀ k : Fin n, faceDim (face k) = k.val
  strict_mono : ∀ i j : Fin n, i < j → face i ⊂ face j

/-- **Rigid motions.** The rigid motions of $\mathbb{R}^n$ are the affine isometric bijections
$\mathbb{R}^n \to \mathbb{R}^n$. -/
abbrev Isom (n : ℕ) := E n ≃ᵃⁱ[ℝ] E n

/-- **Symmetry of a convex polytope.** An affine isometry $\varphi$ of $\mathbb{R}^n$ is a
symmetry of a convex polytope $P \subseteq \mathbb{R}^n$ if $\varphi(P) = P$. -/
def isSymmetry {n : ℕ} (P : ConvexPolytope n) (φ : Isom n) : Prop :=
  ((φ : E n → E n)) '' P.toSet = P.toSet

/-- **Regular convex polytope.** A convex polytope $P \subseteq \mathbb{R}^n$ is regular
(Platonic) if it is full-dimensional and for any two flags $(F_0, \dots, F_{n-1})$ and
$(G_0, \dots, G_{n-1})$ of $P$ there is an affine isometry $\varphi$ of $\mathbb{R}^n$ with
$\varphi(P) = P$ and $\varphi(F_k) = G_k$ for every $k < n$. -/
def IsRegular {n : ℕ} (P : ConvexPolytope n) : Prop :=
  P.IsFullDim ∧
    ∀ F G : P.Flag, ∃ φ : Isom n,
      P.isSymmetry φ ∧
        ∀ k : Fin n, ((φ : E n → E n)) '' F.face k = G.face k

/-- **Similar polytopes.** Two convex polytopes $P$ and $Q$ in $\mathbb{R}^n$ are **similar** when
there are a real number $a > 0$ and an affine isometry $\varphi$ of $\mathbb{R}^n$ such that the
underlying set of $Q$ is $\{a\,\varphi(x) : x \in P\}$. -/
def Similar {n : ℕ} (P Q : ConvexPolytope n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ φ : Isom n,
    Q.toSet = (fun x : E n => a • x) '' ((φ : E n → E n) '' P.toSet)

end ConvexPolytope

/-- **Regular polytopes.** For $d \in \mathbb{N}$, this is the set of regular (Platonic) convex
polytopes in $\mathbb{R}^d$: the convex polytopes in $\mathbb{R}^d$ that are full-dimensional and
whose symmetry group acts transitively on their flags. -/
def regularPolytopes (d : ℕ) : Set (ConvexPolytope d) :=
  {P | P.IsRegular}

/-- **Similarity of regular polytopes.** For regular convex polytopes $P$ and $Q$ in
$\mathbb{R}^d$, $P$ is related to $Q$ when they are similar as convex polytopes, that is, when
there are a real number $a > 0$ and an affine isometry $\varphi$ of $\mathbb{R}^d$ such that the
underlying set of $Q$ is $\{a\,\varphi(x) : x \in P\}$. -/
def regularSimilar (d : ℕ) (P Q : regularPolytopes d) : Prop :=
  ConvexPolytope.Similar (P : ConvexPolytope d) (Q : ConvexPolytope d)

/-- **Number of Platonic polytopes.** For $d \in \mathbb{N}$, $p_d \in \mathbb{N} \cup \{\infty\}$
is the number of similarity classes of regular convex polytopes in $\mathbb{R}^d$, with
$p_d = \infty$ when there are infinitely many classes. -/
noncomputable def platonicCount (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (regularPolytopes d) |
    ∃ P, S = {Q : regularPolytopes d | regularSimilar d P Q}}

/- **Platonic classification.** `p = (p_2, p_3, p_4, p_5, …) = (∞, 5, 6, 3, 3, 3, …)`. -/
/-- **Classification of the Platonic polytopes.** For $d \in \mathbb{N}$ let $p_d \in
\mathbb{N} \cup \{\infty\}$ be the number of regular convex polytopes in $\mathbb{R}^d$ up to
similarity. Then $p_2 = \infty$, $p_3 = 5$, $p_4 = 6$, and $p_d = 3$ for every $d \ge 5$.

Source: Euclid, Elements, Book XIII (~300 BC, p_3 = 5); L. Schläfli, Theorie der vielfachen Kontinuität (1852, posthumous publication; p_4 = 6, p_d = 3 for d ≥ 5). Listed as §42 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `platonic_classification`. -/
public theorem_wanted platonic_classification :
    platonicCount 2 = ⊤ ∧
      platonicCount 3 = 5 ∧
        platonicCount 4 = 6 ∧
          ∀ d, 5 ≤ d → platonicCount d = 3

end PlatonicClassification
end Geometry

end MathlibExt.Geometry.PlatonicClassificationWanted
