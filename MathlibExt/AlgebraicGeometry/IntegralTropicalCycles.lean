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
Its dimension and lattice are computed from its actual affine span. The
local stable multiplicity is a literal tangent-star displacement/index sum,
with the supplied integer facet weights. It is not a free intersection map.

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

structure Cycle (n : ℕ) where
  complex : Complex n
  dimension : ℕ
  weight : Fin complex.count → ℤ
  support_dimension : ∀ i,
    (complex.cell i).dimension ≠ dimension → weight i = 0
  empty_weight : ∀ i, (complex.cell i).carrier = ∅ → weight i = 0

def Cycle.support (C : Cycle n) : Set (RealSpace n) :=
  ⋃ i, if C.weight i = 0 then ∅ else (C.complex.cell i).carrier

/-- The actual tangent-star inequalities at a point of the cell. -/
def starDirections (P : Polyhedron n) (w : RealSpace n) : Set (RealSpace n) :=
  {v | ∀ i, character n (P.normal i) w = P.constant i →
    0 ≤ character n (P.normal i) v}

def starsMeet (P Q : Polyhedron n) (w v : RealSpace n) : Prop :=
  ∃ x ∈ starDirections P w, ∃ y ∈ starDirections Q w, x = y + v

def latticeIndex (P Q : Polyhedron n) : ℤ := ((P.lattice ⊔ Q.lattice).index : ℤ)

def GenericDisplacement (A B : Cycle n) (w v : RealSpace n) : Prop :=
  ∀ i j,
    w ∈ (A.complex.cell i).carrier → w ∈ (B.complex.cell j).carrier →
    (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
      (affineSpan ℝ (B.complex.cell j).carrier).direction ≠ ⊤ →
    v ∉ (affineSpan ℝ (A.complex.cell i).carrier).direction ⊔
      (affineSpan ℝ (B.complex.cell j).carrier).direction

/-- The raw local stable multiplicity with exact lattice-index weights. -/
def stableMultiplicity (A B : Cycle n) (w v : RealSpace n) : ℤ := by
  classical
  exact ∑ i, ∑ j,
    if w ∈ (A.complex.cell i).carrier ∧ w ∈ (B.complex.cell j).carrier ∧
      (A.complex.cell i).dimension = A.dimension ∧
      (B.complex.cell j).dimension = B.dimension ∧
      starsMeet (A.complex.cell i) (B.complex.cell j) w v then
      latticeIndex (A.complex.cell i) (B.complex.cell j) * A.weight i * B.weight j
    else 0

/-- A subdivision is given by actual cell containments and covering unions. -/
structure Refinement (A B : Cycle n) where
  dimension : A.dimension = B.dimension
  index : Fin A.complex.count → Fin B.complex.count
  contained : ∀ i, (A.complex.cell i).carrier ⊆ (B.complex.cell (index i)).carrier
  covers : ∀ j, (B.complex.cell j).carrier =
    ⋃ i : {i // index i = j}, (A.complex.cell i.val).carrier
  weights : ∀ i, (A.complex.cell i).dimension = A.dimension →
    A.weight i = B.weight (index i)

end MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
