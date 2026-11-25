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

Cutting the line at the origin gives two rays of weight one, balanced at their vertex. Against the
whole line, the raw displacement sum at the new vertex is `2` and the vertex is not a regular
point, while at a regular point of a ray the sum is `1`, as for the line. In the plane, the
horizontal axis and the line of slope two meet transversally with lattice index `2`.
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
  empty_weight i h := by
    exfalso
    change line.carrier = ∅ at h
    rw [line_carrier] at h
    exact Set.univ_nonempty.ne_empty h

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

/-! ### The line cut into two rays

Subdividing the line at the origin gives two rays of weight one and their common vertex. The two
rays are balanced at the vertex. At the vertex the raw displacement sum against the whole line is
two, not one: the vertex is not a regular point, which is why multiplicity comparisons are only
requested at regular points. At a regular point of a ray the sum is one, as for the line. -/

private theorem character_one (u : Lattice 1) (x : RealSpace 1) :
    character 1 u x = (u 0 : ℝ) * x 0 := by
  simp [character]

/-- The ray `x ≥ 0`. -/
private def rayPos : Polyhedron 1 where
  count := 1
  normal _ := fun _ ↦ 1
  constant _ := 0

/-- The ray `x ≤ 0`. -/
private def rayNeg : Polyhedron 1 where
  count := 1
  normal _ := fun _ ↦ -1
  constant _ := 0

/-- The origin, cut out by `x ≥ 0` and `x ≤ 0`. -/
private def vertex : Polyhedron 1 where
  count := 2
  normal i := fun _ ↦ if i = 0 then 1 else -1
  constant _ := 0

private theorem rayPos_carrier : rayPos.carrier = {x | 0 ≤ x 0} := by
  ext x
  simp [Polyhedron.carrier, rayPos, character_one]

private theorem rayNeg_carrier : rayNeg.carrier = {x | x 0 ≤ 0} := by
  ext x
  simp [Polyhedron.carrier, rayNeg, character_one]

private theorem eq_zero_of_zero (x : RealSpace 1) (h : x 0 = 0) : x = 0 := by
  funext i
  fin_cases i
  simpa using h

private theorem vertex_carrier : vertex.carrier = {0} := by
  ext x
  simp only [Polyhedron.carrier, vertex, character_one, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [Fin.isValue, ↓reduceIte, Int.cast_one, one_mul, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, Int.cast_neg, neg_mul] at h0 h1
    exact eq_zero_of_zero x (by linarith)
  · rintro rfl i
    simp

/-- A subset of the line containing `0` and `1`, or `0` and `-1`, spans every direction. -/
private theorem direction_eq_top {s : Set (RealSpace 1)} (h0 : (0 : RealSpace 1) ∈ s)
    (h1 : (fun _ ↦ (1 : ℝ)) ∈ s ∨ (fun _ ↦ (-1 : ℝ)) ∈ s) :
    (affineSpan ℝ s).direction = ⊤ := by
  rw [direction_affineSpan, eq_top_iff]
  intro x _
  rcases h1 with h1 | h1
  · have hv : (fun _ ↦ (1 : ℝ)) ∈ vectorSpan ℝ s := by
      simpa using vsub_mem_vectorSpan ℝ h1 h0
    have hx : x = x 0 • (fun _ ↦ (1 : ℝ)) := by
      funext i
      fin_cases i
      simp
    rw [hx]
    exact Submodule.smul_mem _ _ hv
  · have hv : (fun _ ↦ (-1 : ℝ)) ∈ vectorSpan ℝ s := by
      simpa using vsub_mem_vectorSpan ℝ h1 h0
    have hx : x = (-x 0) • (fun _ ↦ (-1 : ℝ)) := by
      funext i
      fin_cases i
      simp
    rw [hx]
    exact Submodule.smul_mem _ _ hv

private theorem rayPos_direction : (affineSpan ℝ rayPos.carrier).direction = ⊤ :=
  direction_eq_top (by simp [rayPos_carrier]) (Or.inl (by simp [rayPos_carrier]))

private theorem rayNeg_direction : (affineSpan ℝ rayNeg.carrier).direction = ⊤ :=
  direction_eq_top (by simp [rayNeg_carrier]) (Or.inr (by simp [rayNeg_carrier]))

private theorem vertex_direction : (affineSpan ℝ vertex.carrier).direction = ⊥ := by
  rw [vertex_carrier, direction_affineSpan, vectorSpan_singleton]

private theorem rayPos_dimension : rayPos.dimension = 1 := by
  rw [Polyhedron.dimension, rayPos_direction, finrank_top, Module.finrank_fin_fun]

private theorem rayNeg_dimension : rayNeg.dimension = 1 := by
  rw [Polyhedron.dimension, rayNeg_direction, finrank_top, Module.finrank_fin_fun]

private theorem vertex_dimension : vertex.dimension = 0 := by
  rw [Polyhedron.dimension, vertex_direction, finrank_bot]

private theorem rayPos_lattice : rayPos.lattice = ⊤ := by
  ext v
  simp [Polyhedron.lattice, rayPos_direction]

private theorem rayNeg_lattice : rayNeg.lattice = ⊤ := by
  ext v
  simp [Polyhedron.lattice, rayNeg_direction]

private theorem vertex_lattice : vertex.lattice = ⊥ := by
  ext v
  simp only [Polyhedron.lattice, vertex_direction, Submodule.mem_bot, AddSubgroup.mem_mk,
    AddSubgroup.mem_bot]
  constructor
  · intro h
    funext i
    have := congrFun h i
    simpa [latticeCast] using this
  · rintro rfl
    simp

/-- The nonempty faces of the ray `x ≥ 0` are the ray and the vertex. -/
private theorem face_of_rayPos {Q : Polyhedron 1} (h : IsFace rayPos Q)
    (hQ : Q.carrier.Nonempty) : Q.carrier = rayPos.carrier ∨ Q.carrier = vertex.carrier := by
  obtain ⟨u, b, hb, hQc⟩ := h
  rw [rayPos_carrier] at hb hQc
  obtain ⟨y, hy⟩ := hQ
  rw [hQc] at hy
  obtain ⟨hy0, hyb⟩ := hy
  simp only [Set.mem_ofPred_eq, character_one] at hy0 hyb hb
  have hb0 : b ≤ 0 := by simpa using hb 0 (by simp)
  have hu : (0 : ℝ) ≤ u 0 := by
    have h2 : b ≤ (u 0 : ℝ) * (y 0 + 1) := hb (fun _ ↦ y 0 + 1) (by
      show (0 : ℝ) ≤ y 0 + 1
      linarith)
    nlinarith
  rw [rayPos_carrier, vertex_carrier, hQc]
  rcases hu.lt_or_eq with hu | hu
  · right
    have hb' : b = 0 := by
      have : 0 ≤ b := by rw [← hyb]; positivity
      linarith
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, character_one, Set.mem_singleton_iff, hb']
    constructor
    · rintro ⟨-, hx⟩
      exact eq_zero_of_zero x (by
        rcases mul_eq_zero.mp hx with h | h
        · exact absurd h hu.ne'
        · exact h)
    · rintro rfl
      simp
  · left
    have hb' : b = 0 := by rw [← hyb, ← hu, zero_mul]
    ext x
    simp [character_one, ← hu, hb']

/-- The nonempty faces of the ray `x ≤ 0` are the ray and the vertex. -/
private theorem face_of_rayNeg {Q : Polyhedron 1} (h : IsFace rayNeg Q)
    (hQ : Q.carrier.Nonempty) : Q.carrier = rayNeg.carrier ∨ Q.carrier = vertex.carrier := by
  obtain ⟨u, b, hb, hQc⟩ := h
  rw [rayNeg_carrier] at hb hQc
  obtain ⟨y, hy⟩ := hQ
  rw [hQc] at hy
  obtain ⟨hy0, hyb⟩ := hy
  simp only [Set.mem_ofPred_eq, character_one] at hy0 hyb hb
  have hb0 : b ≤ 0 := by simpa using hb 0 (by simp)
  have hu : (u 0 : ℝ) ≤ 0 := by
    have h2 : b ≤ (u 0 : ℝ) * (y 0 - 1) := hb (fun _ ↦ y 0 - 1) (by
      show y 0 - 1 ≤ (0 : ℝ)
      linarith)
    nlinarith
  rw [rayNeg_carrier, vertex_carrier, hQc]
  rcases hu.lt_or_eq with hu | hu
  · right
    have hb' : b = 0 := by
      have : 0 ≤ b := by rw [← hyb]; nlinarith
      linarith
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, character_one, Set.mem_singleton_iff, hb']
    constructor
    · rintro ⟨-, hx⟩
      exact eq_zero_of_zero x (by
        rcases mul_eq_zero.mp hx with h | h
        · exact absurd h hu.ne
        · exact h)
    · rintro rfl
      simp
  · left
    have hb' : b = 0 := by rw [← hyb, hu, zero_mul]
    ext x
    simp [character_one, hu, hb']

/-- The only nonempty face of the vertex is the vertex. -/
private theorem face_of_vertex {Q : Polyhedron 1} (h : IsFace vertex Q)
    (hQ : Q.carrier.Nonempty) : Q.carrier = vertex.carrier := by
  obtain ⟨u, b, -, hQc⟩ := h
  rw [hQc] at hQ ⊢
  obtain ⟨y, hy, hyH⟩ := hQ
  rw [vertex_carrier] at hy ⊢
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hyH)

private theorem isFace_refl (P : Polyhedron 1) : IsFace P P :=
  ⟨0, 0, fun x _ ↦ by simp [character_one], by ext x; simp [character_one]⟩

private theorem isFace_rayPos_vertex : IsFace rayPos vertex :=
  ⟨fun _ ↦ 1, 0, fun x hx ↦ by
    rw [rayPos_carrier] at hx
    simpa [character_one] using hx, by
    rw [rayPos_carrier, vertex_carrier]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, character_one,
      Int.cast_one, one_mul]
    constructor
    · rintro rfl
      simp
    · rintro ⟨-, h⟩
      exact eq_zero_of_zero x h⟩

private theorem isFace_rayNeg_vertex : IsFace rayNeg vertex :=
  ⟨fun _ ↦ -1, 0, fun x hx ↦ by
    rw [rayNeg_carrier] at hx
    simp only [character_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    simp only [Set.mem_ofPred_eq] at hx
    linarith, by
    rw [rayNeg_carrier, vertex_carrier]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, character_one,
      Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_eq_zero]
    constructor
    · rintro rfl
      simp
    · rintro ⟨-, h⟩
      exact eq_zero_of_zero x h⟩

private theorem one_mem_rayPos : (fun _ ↦ (1 : ℝ)) ∈ rayPos.carrier := by
  simp [rayPos_carrier]

private theorem one_not_mem_rayNeg : (fun _ ↦ (1 : ℝ)) ∉ rayNeg.carrier := by
  simp [rayNeg_carrier]

private theorem one_not_mem_vertex : (fun _ ↦ (1 : ℝ)) ∉ vertex.carrier := by
  rw [vertex_carrier, Set.mem_singleton_iff]
  intro h
  simpa using congrFun h 0

private theorem neg_one_mem_rayNeg : (fun _ ↦ (-1 : ℝ)) ∈ rayNeg.carrier := by
  simp [rayNeg_carrier]

private theorem neg_one_not_mem_vertex : (fun _ ↦ (-1 : ℝ)) ∉ vertex.carrier := by
  rw [vertex_carrier, Set.mem_singleton_iff]
  intro h
  simpa using congrFun h 0

private theorem zero_mem_vertex : (0 : RealSpace 1) ∈ vertex.carrier := by
  simp [vertex_carrier]

/-- The two rays and their common vertex. -/
private def twoRays : Complex 1 where
  count := 3
  cell := ![rayPos, rayNeg, vertex]
  distinct := by
    intro i j h
    simp only at h
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.reduceFinMk] at h ⊢
    · exact (one_not_mem_rayNeg (h ▸ one_mem_rayPos)).elim
    · exact (one_not_mem_vertex (h ▸ one_mem_rayPos)).elim
    · exact (one_not_mem_rayNeg (h ▸ one_mem_rayPos)).elim
    · exact (neg_one_not_mem_vertex (h ▸ neg_one_mem_rayNeg)).elim
    · exact (one_not_mem_vertex (h.symm ▸ one_mem_rayPos)).elim
    · exact (neg_one_not_mem_vertex (h.symm ▸ neg_one_mem_rayNeg)).elim
  faces i Q h hQ := by
    fin_cases i
    · rcases face_of_rayPos h hQ with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases face_of_rayNeg h hQ with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · exact ⟨2, (face_of_vertex h hQ).symm⟩
  intersections i j := by
    have pn : rayPos.carrier ∩ rayNeg.carrier = vertex.carrier := by
      rw [rayPos_carrier, rayNeg_carrier, vertex_carrier]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact eq_zero_of_zero x (le_antisymm h2 h1)
      · rintro rfl
        simp
    have pv : rayPos.carrier ∩ vertex.carrier = vertex.carrier := by
      rw [Set.inter_eq_right, vertex_carrier, Set.singleton_subset_iff, rayPos_carrier]
      simp
    have nv : rayNeg.carrier ∩ vertex.carrier = vertex.carrier := by
      rw [Set.inter_eq_right, vertex_carrier, Set.singleton_subset_iff, rayNeg_carrier]
      simp
    fin_cases i <;> fin_cases j
    · exact ⟨0, by simp, isFace_refl _, isFace_refl _⟩
    · exact ⟨2, by simpa using pn.symm, isFace_rayPos_vertex, isFace_rayNeg_vertex⟩
    · exact ⟨2, by simpa using pv.symm, isFace_rayPos_vertex, isFace_refl _⟩
    · exact ⟨2, by simpa [Set.inter_comm] using pn.symm, isFace_rayNeg_vertex,
        isFace_rayPos_vertex⟩
    · exact ⟨1, by simp, isFace_refl _, isFace_refl _⟩
    · exact ⟨2, by simpa using nv.symm, isFace_rayNeg_vertex, isFace_refl _⟩
    · exact ⟨2, by simpa [Set.inter_comm] using pv.symm, isFace_refl _, isFace_rayPos_vertex⟩
    · exact ⟨2, by simpa [Set.inter_comm] using nv.symm, isFace_refl _, isFace_rayNeg_vertex⟩
    · exact ⟨2, by simp, isFace_refl _, isFace_refl _⟩

/-- The line, subdivided at the origin. -/
private def raySubdivision : Subdivision lineWeighted where
  complex := twoRays
  index _ := (0 : Fin 1)
  contained i := by
    change _ ⊆ line.carrier
    rw [line_carrier]
    exact Set.subset_univ _
  covers j := by
    fin_cases j
    change line.carrier = _
    rw [line_carrier]
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    rcases le_total 0 (x 0) with h | h
    · exact ⟨⟨(0 : Fin 3), rfl⟩, by simpa [twoRays, rayPos_carrier] using h⟩
    · exact ⟨⟨(1 : Fin 3), rfl⟩, by simpa [twoRays, rayNeg_carrier] using h⟩
  full_dimension _ _ := line_dimension' (0 : Fin 1)
  empty_weight i h _ := by
    exfalso
    fin_cases i
    · exact Set.nonempty_iff_ne_empty.mp ⟨_, one_mem_rayPos⟩ h
    · exact Set.nonempty_iff_ne_empty.mp ⟨_, neg_one_mem_rayNeg⟩ h
    · exact Set.nonempty_iff_ne_empty.mp ⟨_, zero_mem_vertex⟩ h

private theorem rayPos_starsMeet (w v : RealSpace 1) : starsMeet rayPos line w v :=
  ⟨0, fun i _ ↦ by simp, -v, by simp [starDirections, line], by simp⟩

private theorem rayNeg_starsMeet (w v : RealSpace 1) : starsMeet rayNeg line w v :=
  ⟨0, fun i _ ↦ by simp, -v, by simp [starDirections, line], by simp⟩

/-- At the new vertex, the raw sum against the whole line counts both rays: two. -/
example (v : RealSpace 1) :
    stableMultiplicity (subdivide raySubdivision) lineWeighted 0 v = 2 := by
  classical
  have h0 : (0 : RealSpace 1) ∈ line.carrier := by simp [line_carrier]
  have hidx : ∀ P : Polyhedron 1, P.lattice = ⊤ → latticeIndex P line = 1 := by
    intro P hP
    simp [latticeIndex, hP, line_lattice]
  unfold stableMultiplicity
  erw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_one]
  have hd : line.dimension = 1 := line_dimension' (0 : Fin 1)
  simp [subdivide, raySubdivision, twoRays, lineWeighted, lineComplex, h0, hd,
    rayPos_dimension, rayNeg_dimension, vertex_dimension, rayPos_starsMeet, rayNeg_starsMeet,
    hidx _ rayPos_lattice, hidx _ rayNeg_lattice, zero_mem_vertex, rayPos_carrier,
    rayNeg_carrier]
  rfl

/-- The vertex lies in the weighted support of the two rays. -/
private theorem vertex_subset_support :
    vertex.carrier ⊆ (subdivide raySubdivision).support := by
  intro x hx
  rw [vertex_carrier, Set.mem_singleton_iff] at hx
  subst hx
  refine Set.mem_iUnion.mpr ⟨(0 : Fin 3), ?_⟩
  have hw : (subdivide raySubdivision).weight (0 : Fin 3) = 1 := by
    simp [subdivide, raySubdivision, twoRays, lineWeighted, rayPos_dimension]
  simp only [hw, one_ne_zero, ↓reduceIte]
  change (0 : RealSpace 1) ∈ rayPos.carrier
  simp [rayPos_carrier]

/-- The line is its own weighted support. -/
private theorem line_subset_support : line.carrier ⊆ lineWeighted.support := by
  intro x hx
  refine Set.mem_iUnion.mpr ⟨(0 : Fin 1), ?_⟩
  change x ∈ (if (1 : ℤ) = 0 then ∅ else line.carrier)
  simpa using hx

/-- The vertex is not a regular point. -/
example : ¬ RegularPoint (subdivide raySubdivision) lineWeighted 0 := by
  intro h
  have := h (2 : Fin 3) (0 : Fin 1) vertex_subset_support line_subset_support zero_mem_vertex
    (by simp [lineWeighted, lineComplex, line_carrier])
  change 1 + 1 ≤ 1 + Module.finrank ℝ (affineSpan ℝ (vertex.carrier ∩ line.carrier)).direction
    at this
  rw [line_carrier, Set.inter_univ, vertex_direction, finrank_bot] at this
  omega

/-- The point `1` of the ray `x ≥ 0` is a regular point. -/
private theorem one_regular :
    RegularPoint (subdivide raySubdivision) lineWeighted (fun _ ↦ 1) := by
  intro i j _ _ hi _
  fin_cases i
  · change 1 + 1 ≤ 1 + Module.finrank ℝ (affineSpan ℝ (rayPos.carrier ∩ line.carrier)).direction
    rw [line_carrier, Set.inter_univ, rayPos_direction, finrank_top, Module.finrank_fin_fun]
  · exact (one_not_mem_rayNeg hi).elim
  · exact (one_not_mem_vertex hi).elim

/-- At that regular point the raw sum against the line is one, as for the line itself. -/
example (v : RealSpace 1) :
    stableMultiplicity (subdivide raySubdivision) lineWeighted (fun _ ↦ 1) v = 1 := by
  classical
  have h1 : (fun _ ↦ (1 : ℝ)) ∈ line.carrier := by simp [line_carrier]
  have hidx : latticeIndex rayPos line = 1 := by simp [latticeIndex, rayPos_lattice, line_lattice]
  have hd : line.dimension = 1 := line_dimension' (0 : Fin 1)
  unfold stableMultiplicity
  erw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_one]
  simp [subdivide, raySubdivision, twoRays, lineWeighted, lineComplex, h1, hd, rayPos_dimension,
    rayNeg_dimension, vertex_dimension, rayPos_starsMeet, hidx, one_mem_rayPos, one_not_mem_rayNeg,
    one_not_mem_vertex]

/-- The primitive normal `1` of the ray `x ≥ 0` at the vertex. -/
private def posNormal : FaceNormal twoRays (0 : Fin 3) (2 : Fin 3) where
  vector := fun _ ↦ 1
  in_direction := by
    change _ ∈ rayPos.lattice
    rw [rayPos_lattice]
    trivial
  nonzero := by
    change (QuotientAddGroup.mk' vertex.lattice) _ ≠ 0
    rw [QuotientAddGroup.mk'_apply, Ne, QuotientAddGroup.eq_zero_iff, vertex_lattice,
      AddSubgroup.mem_bot]
    intro h
    simpa using congrFun h 0
  primitive := by
    change rayPos.lattice.map (QuotientAddGroup.mk' vertex.lattice) =
      AddSubgroup.zmultiples (QuotientAddGroup.mk' vertex.lattice (fun _ ↦ 1))
    rw [rayPos_lattice]
    ext q
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v 0, ?_⟩
      rw [← map_zsmul]
      congr 1
      funext i
      fin_cases i
      simp
    · rintro ⟨k, rfl⟩
      exact ⟨k • (fun _ ↦ 1), by rw [map_zsmul]⟩
  positive := by
    intro w hw
    change w ∈ intrinsicInterior ℝ vertex.carrier at hw
    rw [vertex_carrier, intrinsicInterior_singleton, Set.mem_singleton_iff] at hw
    subst hw
    change latticeCast 1 (fun _ ↦ 1) ∈ starDirections rayPos 0
    intro i _
    simp [character_one, rayPos, latticeCast]

/-- The primitive normal `-1` of the ray `x ≤ 0` at the vertex. -/
private def negNormal : FaceNormal twoRays (1 : Fin 3) (2 : Fin 3) where
  vector := fun _ ↦ -1
  in_direction := by
    change _ ∈ rayNeg.lattice
    rw [rayNeg_lattice]
    trivial
  nonzero := by
    change (QuotientAddGroup.mk' vertex.lattice) _ ≠ 0
    rw [QuotientAddGroup.mk'_apply, Ne, QuotientAddGroup.eq_zero_iff, vertex_lattice,
      AddSubgroup.mem_bot]
    intro h
    simpa using congrFun h 0
  primitive := by
    change rayNeg.lattice.map (QuotientAddGroup.mk' vertex.lattice) =
      AddSubgroup.zmultiples (QuotientAddGroup.mk' vertex.lattice (fun _ ↦ -1))
    rw [rayNeg_lattice]
    ext q
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨-v 0, ?_⟩
      rw [← map_zsmul]
      congr 1
      funext i
      fin_cases i
      simp
    · rintro ⟨k, rfl⟩
      exact ⟨k • (fun _ ↦ -1), by rw [map_zsmul]⟩
  positive := by
    intro w hw
    change w ∈ intrinsicInterior ℝ vertex.carrier at hw
    rw [vertex_carrier, intrinsicInterior_singleton, Set.mem_singleton_iff] at hw
    subst hw
    change latticeCast 1 (fun _ ↦ -1) ∈ starDirections rayNeg 0
    intro i _
    simp [character_one, rayNeg, latticeCast]

/-- Normals of the two rays at their common vertex, the only codimension-one incidence. -/
private def rayNormals : NormalData twoRays where
  normal i j _ _ hd :=
    if h : i.val = 0 ∧ j.val = 2 then by
      obtain ⟨hi, hj⟩ := h
      obtain rfl : i = (0 : Fin 3) := Fin.ext hi
      obtain rfl : j = (2 : Fin 3) := Fin.ext hj
      exact posNormal
    else if h' : i.val = 1 ∧ j.val = 2 then by
      obtain ⟨hi, hj⟩ := h'
      obtain rfl : i = (1 : Fin 3) := Fin.ext hi
      obtain rfl : j = (2 : Fin 3) := Fin.ext hj
      exact negNormal
    else
      False.elim (by
        revert h h' hd
        fin_cases i <;> fin_cases j <;>
          simp [twoRays, rayPos_dimension, rayNeg_dimension, vertex_dimension])

/-- The weight-one rays are balanced at their vertex. -/
example : Balanced (subdivide raySubdivision) rayNormals := by
  refine ⟨(subdivide raySubdivision).support_dimension, (subdivide raySubdivision).empty_weight,
    fun j _ hd ↦ ?_⟩
  fin_cases j
  · exfalso
    change rayPos.dimension + 1 = 1 at hd
    rw [rayPos_dimension] at hd
    omega
  · exfalso
    change rayNeg.dimension + 1 = 1 at hd
    rw [rayNeg_dimension] at hd
    omega
  · classical
    unfold balanceAt
    erw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_one]
    have hv : (vertex.carrier).Nonempty := ⟨0, zero_mem_vertex⟩
    simp [subdivide, raySubdivision, twoRays, lineWeighted, rayNormals, posNormal, negNormal,
      rayPos_dimension, rayNeg_dimension, vertex_dimension, hv, isFace_rayPos_vertex,
      isFace_rayNeg_vertex]
    show (1 : ℤ) • QuotientAddGroup.mk' vertex.lattice (fun _ ↦ (1 : ℤ)) +
      ((1 : ℤ) • QuotientAddGroup.mk' vertex.lattice (fun _ ↦ (-1 : ℤ)) + 0) = 0
    rw [one_smul, one_smul, add_zero, ← map_add]
    convert map_zero (QuotientAddGroup.mk' vertex.lattice)
    funext i
    simp

/-! ### A non-unimodular transverse pair

In the plane, the horizontal axis and the line of slope two meet transversally at the origin, but
their lattices `ℤ (1, 0)` and `ℤ (1, 2)` span the index-two sublattice of vectors with even second
coordinate, so their lattice index is `2`. -/

/-- The line `{x | ⟪u, x⟫ = 0}`, cut out by `u ≥ 0` and `-u ≥ 0`. -/
private def kernelLine (u : Lattice 2) : Polyhedron 2 where
  count := 2
  normal i := if i = 0 then u else -u
  constant _ := 0

private theorem kernelLine_carrier (u : Lattice 2) :
    (kernelLine u).carrier = {x | character 2 u x = 0} := by
  ext x
  simp only [Polyhedron.carrier, kernelLine, Set.mem_ofPred_eq]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one] at h0 h1
    have : character 2 (-u) x = -character 2 u x := by
      simp [character, Finset.sum_neg_distrib]
    linarith
  · intro h i
    by_cases hi : i = 0
    · simp [hi, h]
    · have : character 2 (-u) x = -character 2 u x := by
        simp [character, Finset.sum_neg_distrib]
      simp [hi, this, h]

private theorem kernelLine_mem_lattice (u v : Lattice 2) :
    v ∈ (kernelLine u).lattice ↔ u 0 * v 0 + u 1 * v 1 = 0 := by
  change latticeCast 2 v ∈ (affineSpan ℝ (kernelLine u).carrier).direction ↔ _
  rw [kernelLine_carrier, direction_affineSpan]
  have key : latticeCast 2 v ∈ vectorSpan ℝ {x | character 2 u x = 0} ↔
      character 2 u (latticeCast 2 v) = 0 := by
    constructor
    · intro hz
      have hle : vectorSpan ℝ {x | character 2 u x = 0} ≤ LinearMap.ker (character 2 u) := by
        rw [vectorSpan_def, Submodule.span_le]
        rintro _ ⟨x, hx, y, hy, rfl⟩
        simp only [Set.mem_ofPred_eq] at hx hy
        simp [hx, hy]
      exact hle hz
    · intro hz
      simpa using vsub_mem_vectorSpan ℝ (show latticeCast 2 v ∈ {x | character 2 u x = 0} from hz)
        (show (0 : RealSpace 2) ∈ {x | character 2 u x = 0} by simp)
  rw [key]
  simp only [character, latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Fin.sum_univ_two]
  exact_mod_cast Iff.rfl

/-- The horizontal axis and the line of slope two have lattice index two. -/
example : latticeIndex (kernelLine ![0, 1]) (kernelLine ![2, -1]) = 2 := by
  let f : Lattice 2 →+ ZMod 2 :=
    { toFun := fun v ↦ (v 1 : ZMod 2)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  have hsup : (kernelLine ![0, 1]).lattice ⊔ (kernelLine ![2, -1]).lattice = f.ker := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · intro v hv
        rw [kernelLine_mem_lattice] at hv
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul,
          zero_add] at hv
        simp [f, hv]
      · intro v hv
        rw [kernelLine_mem_lattice] at hv
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, one_mul] at hv
        have hv1 : v 1 = 2 * v 0 := by linarith
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_mk, ZeroHom.coe_mk, f, hv1]
        push_cast
        rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    · intro v hv
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_mk, ZeroHom.coe_mk, f] at hv
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (v 1) 2).mp hv
      rw [AddSubgroup.mem_sup]
      refine ⟨![v 0 - k, 0], ?_, ![k, 2 * k], ?_, ?_⟩
      · rw [kernelLine_mem_lattice]
        simp
      · rw [kernelLine_mem_lattice]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      · funext i
        fin_cases i
        · simp
        · simp [hk]
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨![0, z.val], ?_⟩
    simp [f]
  rw [latticeIndex, hsup, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective f hsurj]
  simp

/-- A line meets itself non-transversally: the common lattice has infinite index, recorded as `0`,
so such a pair contributes nothing to a stable multiplicity. -/
example : latticeIndex (kernelLine ![0, 1]) (kernelLine ![0, 1]) = 0 := by
  let g : Lattice 2 →+ ℤ :=
    { toFun := fun v ↦ v 1
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hker : (kernelLine ![0, 1]).lattice = g.ker := by
    ext v
    rw [kernelLine_mem_lattice]
    simp [g]
  have hsurj : Function.Surjective g := fun z ↦ ⟨![0, z], by simp [g]⟩
  rw [latticeIndex, sup_idem, hker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top_of_surjective g hsurj]
  simp

end MathlibExtTest.BalancedTropicalCycles
