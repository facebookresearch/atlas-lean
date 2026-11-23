/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.GroupTheory.Index

/-!
# Actual integral affine cells and stable tropical multiplicity sums

Each cell is cut out by finitely many integer-normal affine inequalities.
Its dimension and lattice are computed from its actual affine span. A
weighted complex carries integer weights on the cells of one dimension; it
is not required to be balanced (balancing, which makes it a tropical cycle,
is `BalancedTropicalCycles.Balanced`). The local stable multiplicity is a
literal tangent-star displacement/index sum, with the supplied integer facet
weights. It is not a free intersection map.

References: Osserman--Payne, *Lifting Tropical Intersections*,
1007.1314v3, §§2.4--2.7 and Theorem 5.1.1; Fulton--Sturmfels,
alg-geom/9403002v1, Theorem 3.2. Refinement, balancing and multiplicity
comparison statements are separate proof obligations.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralTropicalCycles

open FiniteToricCoordinates Set
open scoped BigOperators

structure Polyhedron (n : ℕ) where
  count : ℕ
  normal : Fin count → Lattice n
  constant : Fin count → ℝ

variable {n : ℕ}

def Polyhedron.carrier (P : Polyhedron n) : Set (RealSpace n) :=
  {x | ∀ i, P.constant i ≤ character n (P.normal i) x}

def Polyhedron.dimension (P : Polyhedron n) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ P.carrier).direction

def Polyhedron.lattice (P : Polyhedron n) : AddSubgroup (Lattice n) where
  carrier := {v | latticeCast n v ∈ (affineSpan ℝ P.carrier).direction}
  zero_mem' := by simp
  add_mem' ha hb := by simpa using (affineSpan ℝ P.carrier).direction.add_mem ha hb
  neg_mem' ha := by simpa using (affineSpan ℝ P.carrier).direction.neg_mem ha

def IsFace (P Q : Polyhedron n) : Prop :=
  ∃ (u : Lattice n) (b : ℝ),
    (∀ x ∈ P.carrier, b ≤ character n u x) ∧
      Q.carrier = P.carrier ∩ {x | character n u x = b}

structure Complex (n : ℕ) where
  count : ℕ
  cell : Fin count → Polyhedron n
  distinct : Function.Injective fun i ↦ (cell i).carrier
  faces : ∀ i (Q : Polyhedron n), IsFace (cell i) Q → Q.carrier.Nonempty →
    ∃ j, (cell j).carrier = Q.carrier
  intersections : ∀ i j, ∃ r,
    (cell r).carrier = (cell i).carrier ∩ (cell j).carrier ∧
      IsFace (cell i) (cell r) ∧ IsFace (cell j) (cell r)

def Complex.support (C : Complex n) : Set (RealSpace n) := ⋃ i, (C.cell i).carrier

/-- A pure-dimensional weighted integral polyhedral complex: integer weights on the cells of a
fixed dimension (cells of other dimensions, and empty cells, carry weight zero). No balancing
condition is imposed; a tropical cycle is a weighted complex that is balanced along every
codimension-one face (`MathlibExt.AlgebraicGeometry.BalancedTropicalCycles.Balanced`). -/
structure WeightedComplex (n : ℕ) where
  complex : Complex n
  dimension : ℕ
  weight : Fin complex.count → ℤ
  support_dimension : ∀ i,
    (complex.cell i).dimension ≠ dimension → weight i = 0
  empty_weight : ∀ i, (complex.cell i).carrier = ∅ → weight i = 0

def WeightedComplex.support (C : WeightedComplex n) : Set (RealSpace n) :=
  ⋃ i, if C.weight i = 0 then ∅ else (C.complex.cell i).carrier

/-- The actual tangent-star inequalities at a point of the cell. -/
def starDirections (P : Polyhedron n) (w : RealSpace n) : Set (RealSpace n) :=
  {v | ∀ i, character n (P.normal i) w = P.constant i →
    0 ≤ character n (P.normal i) v}

def starsMeet (P Q : Polyhedron n) (w v : RealSpace n) : Prop :=
  ∃ x ∈ starDirections P w, ∃ y ∈ starDirections Q w, x = y + v

def latticeIndex (P Q : Polyhedron n) : ℤ := ((P.lattice ⊔ Q.lattice).index : ℤ)

/-- A displacement `v` is generic at `w` if it avoids the direction sum of every pair of cells of
the weighted supports through `w` whose directions do not span the whole space. Only cells inside
the weighted supports (nonzero-weighted facets and their faces) count: a cell of weight zero
outside the supports does not constrain the displacement, while a face of a weighted facet, such as
a new vertex of a subdivision, still does. -/
def GenericDisplacement (A B : WeightedComplex n) (w v : RealSpace n) : Prop :=
  ∀ i j, (A.complex.cell i).carrier ⊆ A.support → (B.complex.cell j).carrier ⊆ B.support →
    w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
    (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
      (affineSpan ℝ (B.complex.cell j).carrier).direction ≠ ⊤ →
    v ∉ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
      (affineSpan ℝ (B.complex.cell j).carrier).direction

/-- `w` is a regular point for the stable multiplicity of `A` and `B`: every cell of the weighted
support of `A` and every cell of the weighted support of `B` through `w` meet in a set of at least
the expected dimension
`A.dimension + B.dimension - n` (stated without natural subtraction). Equivalently, the cell of
their common refinement having `w` in its relative interior has at least the expected dimension.
Osserman--Payne (Definition 2.6.1) attach the stable multiplicity to faces of the expected
dimension; at a lower-dimensional cell of the common refinement, for instance a new vertex of a
subdivision, the raw displacement sum `stableMultiplicity` adds up several neighbouring faces and
depends on the subdivision and on the displacement. -/
def RegularPoint (A B : WeightedComplex n) (w : RealSpace n) : Prop :=
  ∀ i j, (A.complex.cell i).carrier ⊆ A.support → (B.complex.cell j).carrier ⊆ B.support →
    w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
    A.dimension + B.dimension ≤ n + Module.finrank ℝ
      (affineSpan ℝ ((A.complex.cell i).carrier ∩ (B.complex.cell j).carrier)).direction

/-- The raw local stable multiplicity with exact lattice-index weights: the sum, over pairs of
top-dimensional cells through `w` whose tangent stars meet after displacing one of them by `v`, of
the lattice index times the two weights. It is the stable intersection multiplicity at `w` when `w`
is a `RegularPoint` and `v` is a `GenericDisplacement`. -/
def stableMultiplicity (A B : WeightedComplex n) (w v : RealSpace n) : ℤ := by
  classical
  exact ∑ i, ∑ j,
    if w ∈ (A.complex.cell i).carrier ∧ w ∈ (B.complex.cell j).carrier ∧
      (A.complex.cell i).dimension = A.dimension ∧
      (B.complex.cell j).dimension = B.dimension ∧
      starsMeet (A.complex.cell i) (B.complex.cell j) w v then
      latticeIndex (A.complex.cell i) (B.complex.cell j) * A.weight i * B.weight j
    else 0

/-- A subdivision is given by actual cell containments and covering unions. -/
structure Refinement (A B : WeightedComplex n) where
  dimension : A.dimension = B.dimension
  index : Fin A.complex.count → Fin B.complex.count
  contained : ∀ i, (A.complex.cell i).carrier ⊆ (B.complex.cell (index i)).carrier
  covers : ∀ j, (B.complex.cell j).carrier =
    ⋃ i : {i // index i = j}, (A.complex.cell i.val).carrier
  weights : ∀ i, (A.complex.cell i).dimension = A.dimension →
    A.weight i = B.weight (index i)

end MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
