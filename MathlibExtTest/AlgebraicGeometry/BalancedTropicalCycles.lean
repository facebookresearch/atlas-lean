/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BalancedTropicalCycles

/-!
# Tests for weighted complexes, balancing, subdivision and stable products

The real line, cut out by no inequality, is a one-cell complex of dimension one whose lattice is
all of `ℤ`. With weight one it is a balanced weighted complex (it has no codimension-one face),
its stable self-intersection multiplicity is the lattice index `1`, and its trivial subdivision
keeps its weight. Stable products exist only in the proper range of dimensions, and weighted
complexes with zero weights are equivalent.
-/

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
open MathlibExt.AlgebraicGeometry.BalancedTropicalCycles

noncomputable section

namespace MathlibExtTest.BalancedTropicalCycles

/-- The whole real line, cut out by no inequality. -/
private def line : Polyhedron 1 where
  count := 0
  normal := Fin.elim0
  constant := Fin.elim0

private theorem line_carrier : line.carrier = Set.univ := by
  ext x
  simp [Polyhedron.carrier, line]

/-- The line has dimension one. -/
example : line.dimension = 1 := by
  rw [Polyhedron.dimension, line_carrier, AffineSubspace.span_univ, AffineSubspace.direction_top,
    finrank_top, Module.finrank_fin_fun]

private theorem line_lattice : line.lattice = ⊤ := by
  ext v
  simp [Polyhedron.lattice, line_carrier, AffineSubspace.span_univ]

/-- Two copies of the line meet transversally: the lattice index is one. -/
example : latticeIndex line line = 1 := by
  simp [latticeIndex, line_lattice]

/-- A face of the line cut out by a linear form bounded below on it is the whole line. -/
private theorem face_of_line {Q : Polyhedron 1} (h : IsFace line Q) (hQ : Q.carrier.Nonempty) :
    Q.carrier = line.carrier := by
  obtain ⟨u, b, hb, hQc⟩ := h
  rw [line_carrier] at hb ⊢
  have hu : u 0 = 0 := by
    by_contra hu0
    have := hb (fun _ ↦ (b - 1) / (u 0 : ℝ)) (Set.mem_univ _)
    have hu' : (u 0 : ℝ) ≠ 0 := by exact_mod_cast hu0
    norm_num [character, mul_div_cancel₀ _ hu'] at this
  have hc : ∀ x, character 1 u x = 0 := by
    intro x
    simp [character, hu]
  obtain ⟨x, hx⟩ := hQ
  rw [hQc, line_carrier] at hx
  have hb0 : b = 0 := by
    have h2 : character 1 u x = b := hx.2
    rw [hc] at h2
    exact h2.symm
  rw [hQc, line_carrier]
  ext y
  simp [hc, hb0]

private theorem line_isFace_self : IsFace line line :=
  ⟨0, 0, fun x _ ↦ by simp [character], by ext x; simp [line_carrier, character]⟩

/-- The complex with the line as its only cell. -/
private def lineComplex : Complex 1 where
  count := 1
  cell _ := line
  distinct i j _ := Subsingleton.elim i j
  faces i Q h hQ := ⟨0, (face_of_line h hQ).symm⟩
  intersections i j := ⟨0, by simp, line_isFace_self, line_isFace_self⟩

/-- The line with weight one. -/
private def lineWeighted : WeightedComplex 1 where
  complex := lineComplex
  dimension := 1
  weight _ := 1
  support_dimension i h := by
    exfalso
    apply h
    change line.dimension = 1
    rw [Polyhedron.dimension, line_carrier, AffineSubspace.span_univ,
      AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  empty_weight i h := by
    exfalso
    change line.carrier = ∅ at h
    rw [line_carrier] at h
    exact Set.univ_nonempty.ne_empty h

private theorem line_dimension' (i : Fin lineComplex.count) :
    (lineComplex.cell i).dimension = 1 := by
  change line.dimension = 1
  rw [Polyhedron.dimension, line_carrier, AffineSubspace.span_univ, AffineSubspace.direction_top,
    finrank_top, Module.finrank_fin_fun]

/-- The line has no codimension-one face, so its normal data is empty. -/
private def lineNormals : NormalData lineComplex where
  normal i j _ _ h := by
    exfalso
    rw [line_dimension' i, line_dimension' j] at h
    omega

/-- The weighted line is balanced. -/
example : Balanced lineWeighted lineNormals := by
  refine ⟨fun i h ↦ (h (line_dimension' i)).elim, fun i h ↦ ?_, fun j _ h ↦ ?_⟩
  · exact lineWeighted.empty_weight i h
  · change (lineComplex.cell j).dimension + 1 = 1 at h
    rw [line_dimension' j] at h
    omega

/-- Its stable self-intersection at the origin, displaced by zero, has multiplicity one. -/
example : stableMultiplicity lineWeighted lineWeighted 0 0 = 1 := by
  have hmeet : starsMeet line line (0 : RealSpace 1) 0 := ⟨0, by simp [starDirections, line],
    0, by simp [starDirections, line], by simp⟩
  have hidx : latticeIndex line line = 1 := by simp [latticeIndex, line_lattice]
  have h0 : (0 : RealSpace 1) ∈ line.carrier := by simp [line_carrier]
  have hd : line.dimension = 1 := by
    rw [Polyhedron.dimension, line_carrier, AffineSubspace.span_univ,
      AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  simp only [stableMultiplicity, lineWeighted, lineComplex, h0, hd, hmeet, hidx, and_self,
    ite_true, mul_one, Finset.sum_const]
  rfl

/-- The trivial subdivision keeps the weight of the line. -/
private def trivialSubdivision : Subdivision lineWeighted where
  complex := lineComplex
  index := id
  contained _ := subset_rfl
  covers j := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx ↦ ⟨⟨j, rfl⟩, hx⟩, fun ⟨i, hx⟩ ↦ i.property ▸ hx⟩
  full_dimension _ h := h
  empty_parent _ h := h

example (i : Fin lineComplex.count) : (subdivide trivialSubdivision).weight i = 1 := by
  simp [subdivide, trivialSubdivision, line_dimension' i, lineWeighted]

/-- A stable product only exists in the proper range of dimensions. -/
example {n : ℕ} {A B : WeightedComplex n} (P : StableProduct A B) :
    n ≤ A.dimension + B.dimension := by
  have := P.dimension
  omega

/-- Weighted complexes of the same dimension with zero weights are equivalent. -/
example {n : ℕ} (A B : WeightedComplex n) (hA : ∀ i, A.weight i = 0) (hB : ∀ i, B.weight i = 0)
    (hd : A.dimension = B.dimension) : WeightedEquivalent A B :=
  ⟨zeroCommonSubdivision A B hA hB hd⟩

end MathlibExtTest.BalancedTropicalCycles
