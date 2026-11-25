/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# Balanced integral affine cycles and normalized subdivision operations

The normals live in the actual cell-direction lattice modulo the face lattice.
Their sign is fixed by tangent inequalities at relative-interior face points.
Weights form the actual additive subgroup cut out by the balancing equations.
Addition and negation are literal weight operations on a fixed complex.
Subdivision pulls the weight of the containing facet to each full-dimensional
subcell; no intersection result is part of its input.

References: Osserman--Payne, *Lifting Tropical Intersections*, 1007.1314v3,
sections 2.4--2.7; Fulton--Sturmfels, alg-geom/9403002v1, section 2.
Native affine-span, lattice-quotient and subgroup constructions are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BalancedTropicalCycles

open FiniteToricCoordinates IntegralTropicalCycles
open scoped BigOperators

variable {n : ℕ} (C : Complex n)

structure FaceNormal (i j : Fin C.count) where
  vector : Lattice n
  in_direction : vector ∈ (C.cell i).lattice
  nonzero : (QuotientAddGroup.mk' (C.cell j).lattice) vector ≠ 0
  primitive : (C.cell i).lattice.map (QuotientAddGroup.mk' (C.cell j).lattice) =
    AddSubgroup.zmultiples ((QuotientAddGroup.mk' (C.cell j).lattice) vector)
  positive : ∀ w ∈ intrinsicInterior ℝ (C.cell j).carrier,
    latticeCast n vector ∈ starDirections (C.cell i) w

structure NormalData where
  normal : ∀ i j, (C.cell j).carrier.Nonempty → IsFace (C.cell i) (C.cell j) →
    (C.cell j).dimension + 1 = (C.cell i).dimension → FaceNormal C i j

variable (N : NormalData C)

def balanceAt (d : ℕ) (w : Fin C.count → ℤ) (j : Fin C.count) :
    Lattice n ⧸ (C.cell j).lattice := by
  classical
  exact ∑ i, if h : (C.cell j).carrier.Nonempty ∧ IsFace (C.cell i) (C.cell j) ∧
      (C.cell j).dimension + 1 = (C.cell i).dimension ∧
      (C.cell i).dimension = d then
    w i • (QuotientAddGroup.mk' (C.cell j).lattice)
      (N.normal i j h.1 h.2.1 h.2.2.1).vector
  else 0

@[simp] theorem balanceAt_zero (d : ℕ) (j : Fin C.count) :
    balanceAt C N d 0 j = 0 := by
  classical
  simp [balanceAt]

theorem balanceAt_add (d : ℕ) (a b : Fin C.count → ℤ) (j : Fin C.count) :
    balanceAt C N d (a + b) j = balanceAt C N d a j + balanceAt C N d b j := by
  classical
  simp only [balanceAt, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [add_zsmul]

theorem balanceAt_neg (d : ℕ) (a : Fin C.count → ℤ) (j : Fin C.count) :
    balanceAt C N d (-a) j = -balanceAt C N d a j := by
  classical
  simp only [balanceAt, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

def weightGroup (d : ℕ) : AddSubgroup (Fin C.count → ℤ) where
  carrier := {w | (∀ i, (C.cell i).dimension ≠ d → w i = 0) ∧
    (∀ i, (C.cell i).carrier = ∅ → w i = 0) ∧
    ∀ j, (C.cell j).carrier.Nonempty →
      (C.cell j).dimension + 1 = d → balanceAt C N d w j = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, he, hb⟩ ⟨hc, hf, hd⟩
    refine ⟨fun i h ↦ by simp [ha i h, hc i h],
      fun i h ↦ by simp [he i h, hf i h], fun j hn h ↦ ?_⟩
    rw [balanceAt_add, hb j hn h, hd j hn h, add_zero]
  neg_mem' := by
    rintro a ⟨ha, he, hb⟩
    refine ⟨fun i h ↦ by simp [ha i h], fun i h ↦ by simp [he i h], fun j hn h ↦ ?_⟩
    rw [balanceAt_neg, hb j hn h, neg_zero]

def toWeightedComplex (d : ℕ) (w : weightGroup C N d) : WeightedComplex n :=
  ⟨C, d, w.val, w.property.1, w.property.2.1⟩

def Balanced (A : WeightedComplex n) (N : NormalData A.complex) : Prop :=
  A.weight ∈ weightGroup A.complex N A.dimension

/-- A subdivision of a weighted complex: a complex whose cells lie in, and cover, the cells of `A`.
An empty cell of the subdivision (the intersection of two disjoint cells, for instance after cutting
the line at two points) may lie under a nonempty cell of `A`. As the empty set has dimension zero,
an empty cell counts as top-dimensional when `A` has dimension zero; its parent then carries weight
zero, so that empty cells keep weight zero. -/
structure Subdivision (A : WeightedComplex n) where
  complex : Complex n
  index : Fin complex.count → Fin A.complex.count
  contained : ∀ i, (complex.cell i).carrier ⊆ (A.complex.cell (index i)).carrier
  covers : ∀ j, (A.complex.cell j).carrier =
    ⋃ i : {i // index i = j}, (complex.cell i.val).carrier
  full_dimension : ∀ i, (complex.cell i).dimension = A.dimension →
    (A.complex.cell (index i)).dimension = A.dimension
  empty_weight : ∀ i, (complex.cell i).carrier = ∅ →
    (complex.cell i).dimension = A.dimension → A.weight (index i) = 0

variable {C N} {A B : WeightedComplex n}

def subdivide (S : Subdivision A) : WeightedComplex n := by
  classical
  exact
    { complex := S.complex
      dimension := A.dimension
      weight := fun i ↦ if (S.complex.cell i).dimension = A.dimension then
        A.weight (S.index i) else 0
      support_dimension := fun i h ↦ by simp [h]
      empty_weight := fun i h ↦ by
        split_ifs with hd
        · exact S.empty_weight i h hd
        · rfl }

def subdivisionRefinement (S : Subdivision A) : Refinement (subdivide S) A where
  dimension := rfl
  index := S.index
  contained := S.contained
  covers := S.covers
  weights := by
    classical
    intro i h
    change (if (S.complex.cell i).dimension = A.dimension then
      A.weight (S.index i) else 0) = A.weight (S.index i)
    exact ite_eq_left h

abbrev WeightedFacet (A : WeightedComplex n) := {i : Fin A.complex.count // A.weight i ≠ 0}

/-- Data exhibiting the weighted complex $A$ as a refinement of $B$ on their cells of nonzero
weight: $A$ and $B$ have the same dimension, each cell of $A$ of nonzero weight is assigned a cell
of $B$ of nonzero weight that contains it and has the same weight, and each cell of $B$ of nonzero
weight is the union of the cells of $A$ assigned to it. Cells of weight zero, in $A$ or in $B$, are
not constrained. -/
structure WeightedRefinement (A B : WeightedComplex n) where
  dimension : A.dimension = B.dimension
  index : WeightedFacet A → WeightedFacet B
  contained : ∀ i, (A.complex.cell i.val).carrier ⊆ (B.complex.cell (index i).val).carrier
  covers : ∀ j : WeightedFacet B, (B.complex.cell j.val).carrier =
    ⋃ i : {i : WeightedFacet A // index i = j}, (A.complex.cell i.val.val).carrier
  weights : ∀ i, A.weight i.val = B.weight (index i).val

structure CommonSubdivision (A B : WeightedComplex n) where
  cycle : WeightedComplex n
  left : WeightedRefinement cycle A
  right : WeightedRefinement cycle B

def WeightedEquivalent (A B : WeightedComplex n) : Prop := Nonempty (CommonSubdivision A B)

def zeroWeightedRefinement (A B : WeightedComplex n) (hA : ∀ i, A.weight i = 0)
    (hB : ∀ i, B.weight i = 0) (hd : A.dimension = B.dimension) : WeightedRefinement A B where
  dimension := hd
  index i := False.elim (i.property (hA i.val))
  contained i := False.elim (i.property (hA i.val))
  covers j := False.elim (j.property (hB j.val))
  weights i := False.elim (i.property (hA i.val))

/-- Equal-degree zero cycles admit a common weighted subdivision even when
their presentations carry different extra zero cells. -/
def zeroCommonSubdivision (A B : WeightedComplex n) (hA : ∀ i, A.weight i = 0)
    (hB : ∀ i, B.weight i = 0) (hd : A.dimension = B.dimension) : CommonSubdivision A B :=
  ⟨A, zeroWeightedRefinement A A hA hA rfl, zeroWeightedRefinement A B hA hB hd⟩

/-- The support of the stable product: the closure of the regular points carrying a nonzero
stable multiplicity for some generic displacement. -/
def stableSupport (A B : WeightedComplex n) : Set (RealSpace n) :=
  closure {w | RegularPoint A B w ∧
    ∃ v, GenericDisplacement A B w v ∧ stableMultiplicity A B w v ≠ 0}

/-- The candidate product is normalized by the computed local displacement
sum at the regular points of every relative facet interior (the other points of a facet interior
lie on finitely many lower-dimensional cells of the common refinement). Balancing is a separate
target. Its dimension is `dim A + dim B - n`, stated without natural subtraction, so a
product only exists in the proper range `n ≤ dim A + dim B`. -/
structure StableProduct (A B : WeightedComplex n) where
  cycle : WeightedComplex n
  dimension : cycle.dimension + n = A.dimension + B.dimension
  support : cycle.support = stableSupport A B
  multiplicity : ∀ i, (cycle.complex.cell i).dimension = cycle.dimension →
    ∀ w ∈ intrinsicInterior ℝ (cycle.complex.cell i).carrier, RegularPoint A B w →
      ∀ v, GenericDisplacement A B w v →
        cycle.weight i = stableMultiplicity A B w v

end MathlibExt.AlgebraicGeometry.BalancedTropicalCycles
