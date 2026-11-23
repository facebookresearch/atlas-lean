/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.BravaisLattice

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.BravaisLattice`

* Square: the rotation group `Multiplicative (ZMod 4)` of a square acts on its four vertices
  `ZMod 4`. All four vertices lie in one orbit, the stabiliser of a vertex is trivial, the orbit has
  four points, orbit–stabiliser reads `4 * 1 = 4`, and the orbit sizes add up to four.
* Simple cubic: with `B = 1` and one atom at the origin, the positions are exactly the integer
  points `ℤ³`, the nearest-neighbour distance is `1`, every unimodular relabeling of the cells
  preserves the positions, and the cell volume is `1` before and after a shear relabeling.
* Countermodel without `det B ≠ 0`: the singular matrix with columns `e₀, e₀, e₂` sends the
  nonzero integer vector `(1, -1, 0)` to `0`, so `n ↦ B *ᵥ n` is not injective.
* Countermodel without distinct offsets modulo `L`: two motif atoms whose offsets differ by the
  lattice vector `e₀` occupy one position with two different index pairs.
* Physlib sites: translating a site of the simple cubic crystal adds to its cell index and moves
  its position by the lattice vector, and distinct sites occupy distinct positions.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.BravaisLattice

open _root_.Crystallography MeasureTheory
open scoped Matrix

/-! ### Rotations of a square -/

/-- The rotations of a square: `Multiplicative.ofAdd r` turns it by `r` quarter turns. -/
abbrev Rotation := Multiplicative (ZMod 4)

-- Rotating by `r` quarter turns sends vertex `k` to vertex `k + r`.
example (r k : ZMod 4) : Multiplicative.ofAdd r • k = r + k := rfl

/-- The orbit of a vertex, listed by the four rotations. -/
instance (v : ZMod 4) : Fintype (MulAction.orbit Rotation v) := Set.fintypeRange _

/-- All four vertices lie in the orbit of vertex `0`. -/
lemma orbit_zero : MulAction.orbit Rotation (0 : ZMod 4) = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  exact ⟨Multiplicative.ofAdd v, add_zero v⟩

/-- Only the identity rotation fixes vertex `0`. -/
lemma stabilizer_zero : MulAction.stabilizer Rotation (0 : ZMod 4) = ⊥ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  change Multiplicative.toAdd g + 0 = 0 ↔ g = 1
  rw [add_zero]
  exact toAdd_eq_zero

-- The orbit of vertex `0` has four points.
example : Fintype.card (MulAction.orbit Rotation (0 : ZMod 4)) = 4 := by
  rw [card_orbit_eq_card_group_of_stabilizer_eq_bot Rotation 0 stabilizer_zero,
    Fintype.card_multiplicative, ZMod.card]

-- The stabiliser of vertex `0` has one element.
example : Fintype.card (MulAction.stabilizer Rotation (0 : ZMod 4)) = 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact (Subgroup.eq_bot_iff_card _).mp stabilizer_zero

-- Orbit–stabiliser for vertex `0`: the orbit has four points and the stabiliser one.
example : Fintype.card (MulAction.orbit Rotation (0 : ZMod 4)) *
    Fintype.card (MulAction.stabilizer Rotation (0 : ZMod 4)) = 4 := by
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Fintype.card_multiplicative,
    ZMod.card]

open scoped Classical in
-- The orbit sizes add up to the four vertices.
example : ∑ ω : MulAction.orbitRel.Quotient Rotation (ZMod 4),
    Fintype.card (MulAction.orbit Rotation (Quotient.out ω)) = 4 := by
  rw [sum_card_orbit_eq_card, ZMod.card]

/-! ### Simple cubic crystal -/

/-- The simple cubic lattice: the primitive vectors are the standard basis, `B = 1`. -/
noncomputable def simpleCubicLattice : BravaisLattice := ⟨1, by simp⟩

/-- The simple cubic crystal: one atom per cell, at the origin of the cell. -/
noncomputable def simpleCubic : BravaisCrystal Unit :=
  { simpleCubicLattice with offset := fun _ => 0 }

/-- The integer point `n` of Euclidean space. -/
noncomputable def intPoint (n : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => (n i : ℝ)

/-- The simple cubic atom in cell `n` sits at the integer point `n`. -/
lemma position_simpleCubic (n : Fin 3 → ℤ) (f : Unit) :
    simpleCubic.position n f = intPoint n := by
  simp [simpleCubic, simpleCubicLattice, intPoint, BravaisCrystal.position,
    BravaisLattice.latticeVector_apply]

/-- The simple cubic positions are exactly the integer points `ℤ³`. -/
lemma positions_simpleCubic : simpleCubic.positions = Set.range intPoint := by
  ext x
  constructor
  · rintro ⟨⟨n, f⟩, rfl⟩
    exact ⟨n, (position_simpleCubic n f).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(n, ()), position_simpleCubic n ()⟩

/-- Distinct integer points are at distance at least `1`. -/
lemma one_le_dist_intPoint {n m : Fin 3 → ℤ} (h : n ≠ m) : 1 ≤ dist (intPoint n) (intPoint m) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hi' : (1 : ℤ) ≤ |n i - m i| := Int.one_le_abs (sub_ne_zero.mpr hi)
  calc (1 : ℝ) ≤ ‖(intPoint n - intPoint m).ofLp i‖ := by
        simpa [intPoint, Real.norm_eq_abs] using (Int.cast_le (R := ℝ)).mpr hi'
    _ ≤ ‖intPoint n - intPoint m‖ := PiLp.norm_apply_le _ i
    _ = dist (intPoint n) (intPoint m) := (dist_eq_norm _ _).symm

/-- The integer points `0` and `e₀` are at distance `1`. -/
lemma dist_intPoint_zero_single : dist (intPoint 0) (intPoint (Pi.single 0 1)) = 1 := by
  simp [EuclideanSpace.dist_eq, intPoint, Fin.sum_univ_three]

-- The nearest-neighbour distance of the simple cubic crystal is `1`.
example : IsLeast {d | ∃ x ∈ simpleCubic.positions, ∃ y ∈ simpleCubic.positions,
    x ≠ y ∧ dist x y = d} 1 := by
  rw [positions_simpleCubic]
  constructor
  · refine ⟨intPoint 0, ⟨0, rfl⟩, intPoint (Pi.single 0 1), ⟨Pi.single 0 1, rfl⟩, ?_,
      dist_intPoint_zero_single⟩
    intro h
    have h1 := dist_intPoint_zero_single
    rw [h, dist_self] at h1
    exact zero_ne_one h1
  · rintro d ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, hnm, rfl⟩
    exact one_le_dist_intPoint fun h => hnm (congrArg intPoint h)

-- Every unimodular relabeling of the cells preserves the simple cubic positions.
example (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) :
    (simpleCubic.relabel P hP).positions = Set.range intPoint := by
  rw [BravaisCrystal.positions_relabel, positions_simpleCubic]

/-- A shear of the cells: the second primitive vector becomes `e₀ + e₁`. -/
def shear : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

/-- The shear is unimodular. -/
lemma isUnit_det_shear : IsUnit shear.det := by
  simp [shear, Matrix.det_fin_three]

-- The sheared cell gives the same positions.
example : (simpleCubic.relabel shear isUnit_det_shear).positions = Set.range intPoint := by
  rw [BravaisCrystal.positions_relabel, positions_simpleCubic]

-- The simple cubic cell has volume `1`, before and after the shear.
example : volume (parallelepiped simpleCubic.primitiveVector) = 1 := by
  rw [BravaisLattice.volume_parallelepiped_primitiveVector]
  simp [simpleCubic, simpleCubicLattice]

example : volume (parallelepiped (simpleCubic.relabel shear isUnit_det_shear).primitiveVector) =
    1 := by
  rw [BravaisCrystal.relabel_toBravaisLattice, BravaisLattice.volume_parallelepiped_relabel,
    BravaisLattice.volume_parallelepiped_primitiveVector]
  simp [simpleCubic, simpleCubicLattice]

/-! ### Countermodels -/

/-- A singular basis matrix, with columns `e₀, e₀, e₂`. -/
def singularMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 0, 0, 0; 0, 0, 1]

-- The matrix is singular.
example : singularMatrix.det = 0 := by
  simp [singularMatrix, Matrix.det_fin_three]

/-- The integer vector `(1, -1, 0)` lies in the kernel of the singular matrix. -/
lemma singularMatrix_mulVec_kernel :
    (singularMatrix *ᵥ fun i => ((![1, -1, 0] : Fin 3 → ℤ) i : ℝ)) = 0 := by
  ext i
  fin_cases i <;> simp [singularMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- Without `det B ≠ 0`, the map `n ↦ B *ᵥ n` is not injective on integer vectors.
example : ¬ Function.Injective fun n : Fin 3 → ℤ => singularMatrix *ᵥ fun i => (n i : ℝ) := by
  intro h
  have h0 : (![1, -1, 0] : Fin 3 → ℤ) = 0 := by
    apply h
    simp only [singularMatrix_mulVec_kernel, Pi.zero_apply, Int.cast_zero]
    exact (Matrix.mulVec_zero _).symm
  have h00 := congrFun h0 0
  simp at h00

/-- Two atoms per simple cubic cell, the second offset from the first by the lattice vector `e₀`. -/
noncomputable def doubledCubic : BravaisCrystal (Fin 2) :=
  { simpleCubicLattice with offset := ![0, simpleCubicLattice.latticeVector (Pi.single 0 1)] }

/-- Atom `0` of cell `e₀` and atom `1` of cell `0` occupy the same position. -/
lemma position_doubledCubic : doubledCubic.position (Pi.single 0 1) 0 =
    doubledCubic.position 0 1 := by
  simp [doubledCubic, BravaisCrystal.position]

-- Without distinct offsets modulo the lattice, a position does not determine its index pair.
example : ¬ Function.Injective fun p : (Fin 3 → ℤ) × Fin 2 => doubledCubic.position p.1 p.2 := by
  intro h
  have h' := @h (Pi.single 0 1, 0) (0, 1) position_doubledCubic
  simp at h'

-- The offsets of `doubledCubic` are not distinct modulo the lattice.
example : ¬ ∀ f g : Fin 2,
    doubledCubic.offset f - doubledCubic.offset g ∈ doubledCubic.lattice → f = g := by
  rw [← BravaisCrystal.position_injective_iff]
  intro h
  have h' := @h (Pi.single 0 1, 0) (0, 1) position_doubledCubic
  simp at h'

/-! ### Sites of the Physlib crystal -/

-- Translating the site in cell `n` by `m` gives the site in cell `n + m`.
example (m n : Fin 3 → ℤ) :
    m +ᵥ (⟨n, ()⟩ : (BravaisCrystal.physlibCrystal Unit).Site) = ⟨n + m, ()⟩ :=
  BravaisCrystal.vadd_mk m n ()

-- The translated site of the simple cubic crystal sits at the translated integer point.
example (m n : Fin 3 → ℤ) :
    simpleCubic.sitePosition (m +ᵥ ⟨n, ()⟩) = intPoint (n + m) := by
  rw [BravaisCrystal.sitePosition_vadd, BravaisCrystal.sitePosition_mk,
    BravaisCrystal.latticeVector_add_position, position_simpleCubic]

-- Distinct sites of the simple cubic crystal occupy distinct positions.
example : Function.Injective simpleCubic.sitePosition :=
  simpleCubic.sitePosition_injective fun f g _ => Subsingleton.elim f g

end PhyslibExtTest.CondensedMatter.Crystallography.BravaisLattice
