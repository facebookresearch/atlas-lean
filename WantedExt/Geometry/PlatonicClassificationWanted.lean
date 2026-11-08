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

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A **convex polytope** in `ℝⁿ`: the convex hull of a finite nonempty set
whose listed vertices are exactly the extreme points of the hull. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope

/-- The underlying convex set of the polytope. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))

/-- The affine dimension of `P`. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)

/-- `P` is **full-dimensional** if `dim P = n`. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n

/-- A **face** of `P` is a nonempty exposed subset. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- The affine dimension of a subset of `ℝⁿ`. -/
noncomputable def faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

/-- A **flag** of a full-dimensional `n`-polytope `P`: a strictly
increasing chain `F_0 ⊂ F_1 ⊂ ⋯ ⊂ F_{n−1}` of faces with `faceDim F_k = k`. -/
structure Flag {n : ℕ} (P : ConvexPolytope n) where
  face : Fin n → Set (E n)
  isFace : ∀ k, P.IsFace (face k)
  dim_eq : ∀ k : Fin n, faceDim (face k) = k.val
  strict_mono : ∀ i j : Fin n, i < j → face i ⊂ face j

/-- Affine isometries of `ℝⁿ` — the rigid motions. -/
abbrev Isom (n : ℕ) := E n ≃ᵃⁱ[ℝ] E n

/-- `φ` is a **symmetry** of `P` if it maps `P` onto itself. -/
def isSymmetry {n : ℕ} (P : ConvexPolytope n) (φ : Isom n) : Prop :=
  ((φ : E n → E n)) '' P.toSet = P.toSet

/-- `P` is **regular** (Platonic) if it is full-dimensional and its
symmetry group acts transitively on its flags. -/
def IsRegular {n : ℕ} (P : ConvexPolytope n) : Prop :=
  P.IsFullDim ∧
    ∀ F G : P.Flag, ∃ φ : Isom n,
      P.isSymmetry φ ∧
        ∀ k : Fin n, ((φ : E n → E n)) '' F.face k = G.face k

/-- Two polytopes are **similar** when related by a positive scaling and an
affine isometry. -/
def Similar {n : ℕ} (P Q : ConvexPolytope n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ φ : Isom n,
    Q.toSet = (fun x : E n => a • x) '' ((φ : E n → E n) '' P.toSet)

end ConvexPolytope

/-- The set of regular (Platonic) polytopes in dimension `d`. -/
def regularPolytopes (d : ℕ) : Set (ConvexPolytope d) :=
  {P | P.IsRegular}

/-- The similarity relation on regular polytopes in dimension `d`. -/
def regularSimilar (d : ℕ) (P Q : regularPolytopes d) : Prop :=
  ConvexPolytope.Similar (P : ConvexPolytope d) (Q : ConvexPolytope d)

/-- `p_d` — count of Platonic polytopes in dimension `d` up to similarity,
in `ℕ∞ = ℕ ∪ {⊤}` so `⊤` records "infinitely many". -/
noncomputable def platonicCount (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (regularPolytopes d) |
    ∃ P, S = {Q : regularPolytopes d | regularSimilar d P Q}}

/- **Platonic classification.** `p = (p_2, p_3, p_4, p_5, …) = (∞, 5, 6, 3, 3, 3, …)`. -/
/-- Source: Euclid, Elements, Book XIII (~300 BC, p_3 = 5); L. Schläfli, Theorie der vielfachen Kontinuität (1852, posthumous publication; p_4 = 6, p_d = 3 for d ≥ 5). Listed as §42 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `platonic_classification`. -/
public theorem_wanted platonic_classification :
    platonicCount 2 = ⊤ ∧
      platonicCount 3 = 5 ∧
        platonicCount 4 = 6 ∧
          ∀ d, 5 ≤ d → platonicCount d = 3

end PlatonicClassification
end Geometry

end MathlibExt.Geometry.PlatonicClassificationWanted
