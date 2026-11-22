/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Physlib.CondensedMatter.Crystal.Basic

/-!
# Bravais lattices and crystals with a motif

A three-dimensional crystal is a Bravais lattice of translations with a finite motif of atoms
repeated in every cell.

## i. Overview

Three primitive vectors in `EuclideanSpace ℝ (Fin 3)` are recorded by their basis matrix `B`, whose
`j`-th column holds the Cartesian coordinates of the `j`-th vector. Determinant convention: `det B`
is the determinant of this column matrix. It is the oriented volume of the parallelepiped spanned by
the vectors. It is nonzero exactly when the vectors are linearly independent, and `|det B|` is the
Lebesgue volume of the parallelepiped. Coordinates in a basis exist and are unique. A change of
basis whose matrix `P` has as columns the old coordinates of the new basis vectors transforms
coordinates by `P⁻¹` and determinants by `det B' = det P * det B`.

A Bravais lattice is given by a matrix `B` with `det B ≠ 0`. Its lattice is
`L = {B *ᵥ n | n : Fin 3 → ℤ}`, the integer combinations of the primitive vectors. The map
`n ↦ B *ᵥ n` is injective because `det B ≠ 0`. A crystal adds a finite nonempty motif `F` with
offsets `u : F → EuclideanSpace ℝ (Fin 3)`, and its atoms sit at the positions `B *ᵥ n + u f`. A
position determines its cell index `n` and motif label `f` exactly when no two offsets differ by a
lattice vector, and this hypothesis is stated explicitly wherever it is used. Relabeling the cells
by an integer matrix `P` with `det P = ±1` preserves both the lattice and the cell volume `|det B|`.

Finite symmetry groups act on finite sets of sites, planes or directions. The orbits of such an
action partition the set, and orbit–stabiliser counts the points of each orbit.

Physlib's `Physlib.CondensedMatter.Crystal` records the cells and labels of a crystal but no
coordinates. The last section places the sites of `Crystal.ofUnitCell (Fin 3 → ℤ) F` at the atomic
positions, compatibly with translations.

Reciprocal lattices, classification of point and space groups, and the conversion between
conventional and primitive cells are not treated here.

## ii. Key results

- `Crystallography.eq_sum_smul_iff` : the basis coordinates of a vector exist and are unique.
- `Crystallography.repr_eq_inv_mulVec_repr` : a change of basis transforms coordinates by `P⁻¹`.
- `Crystallography.det_cartesianMatrix_eq_det_mul_det` : `det B' = det P * det B`.
- `Crystallography.det_cartesianMatrix_ne_zero_iff` : `det B ≠ 0` iff the vectors are linearly
  independent.
- `Crystallography.volume_parallelepiped` : a parallelepiped has volume `|det B|`.
- `Crystallography.sum_card_orbit_eq_card` : the orbits of a group action partition a finite set.
- `Crystallography.card_orbit_eq_card_group_of_stabilizer_eq_bot` : orbit–stabiliser for a point
  with trivial stabiliser.
- `Crystallography.BravaisLattice` : a lattice given by a basis matrix with `det B ≠ 0`.
- `Crystallography.BravaisLattice.mem_lattice_iff` : the lattice is `{B *ᵥ n | n : Fin 3 → ℤ}`.
- `Crystallography.BravaisLattice.latticeVector_injective` : `n ↦ B *ᵥ n` is injective.
- `Crystallography.BravaisCrystal` : a Bravais lattice with a finite motif.
- `Crystallography.BravaisCrystal.existsUnique_index` : each atomic position has a unique cell index
  and motif label when the offsets are distinct modulo the lattice.
- `Crystallography.BravaisLattice.volume_fundamentalDomain` : the fundamental cell has volume
  `|det B|`.
- `Crystallography.BravaisLattice.lattice_relabel`, `Crystallography.BravaisLattice.abs_det_relabel`
  : a unimodular relabeling preserves the lattice and `|det B|`.
- `Crystallography.BravaisCrystal.physlibCrystal` : the stable Physlib crystal with translation
  group `Fin 3 → ℤ` and unit cell `F`.
- `Crystallography.BravaisCrystal.vadd_mk` : translating a site by `m` sends `(n, f)` to
  `(n + m, f)`.
- `Crystallography.BravaisCrystal.sitePosition_vadd` : translating a Physlib site translates its
  position by the corresponding lattice vector.

## iii. Table of contents

- A. Basis coordinates and the basis matrix
- B. Orbits of finite group actions
- C. Bravais lattices
- D. Crystals with a motif
- E. Unimodular relabeling and cell volume
- F. Sites of the Physlib crystal

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapter 4, for Bravais lattices, primitive vectors and lattices with a basis.
* D. S. Dummit and R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley (2004), Section 4.1, for group
  actions, orbits and stabilisers.

-/

@[expose] public section

open Module MeasureTheory
open scoped Matrix

namespace Crystallography

/-! ## A. Basis coordinates and the basis matrix -/

/-- The basis matrix of three vectors: its `j`-th column holds the Cartesian coordinates of `v j`.
Its determinant is the oriented volume of the parallelepiped spanned by `v`. -/
noncomputable def cartesianMatrix (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix v

/-- The `(i, j)` entry of the basis matrix is the `i`-th Cartesian coordinate of `v j`. -/
@[simp] lemma cartesianMatrix_apply (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    cartesianMatrix v i j = (v j).ofLp i := by
  simp [cartesianMatrix, Basis.toMatrix_apply]

/-- Every vector is the combination of a basis with its coordinates. -/
lemma eq_sum_repr_smul (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    x = ∑ i, b.repr x i • b i :=
  (b.sum_repr x).symm

/-- The coefficients `c` give `x` in the basis `b` exactly when they are the coordinates of `x`:
the coordinate vector exists and is unique. -/
lemma eq_sum_smul_iff (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) (c : Fin 3 → ℝ) :
    x = ∑ i, c i • b i ↔ c = ⇑(b.repr x) := by
  constructor
  · rintro rfl
    exact (b.repr_sum_self c).symm
  · rintro rfl
    exact eq_sum_repr_smul b x

/-- Change of basis: the columns of `P = b.toMatrix b'` are the coordinates of the new basis vectors
`b' j` in the old basis `b`, and the new coordinates of `x` are `P⁻¹ *ᵥ` its old coordinates. -/
lemma repr_eq_inv_mulVec_repr (b b' : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    ⇑(b'.repr x) = (b.toMatrix b')⁻¹ *ᵥ ⇑(b.repr x) := by
  rw [Matrix.inv_eq_right_inv (b.toMatrix_mul_toMatrix_flip b'), b.toMatrix_mulVec_repr b' x]

/-- Under a change of basis the basis matrices satisfy `B' = B * P` with `P = b.toMatrix b'`. -/
lemma cartesianMatrix_eq_mul (b b' : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    cartesianMatrix b' = cartesianMatrix b * b.toMatrix b' :=
  ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix_mul_toMatrix b b').symm

/-- The oriented volume changes by `det P` under a change of basis: `det B' = det P * det B`. -/
lemma det_cartesianMatrix_eq_det_mul_det (b b' : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (cartesianMatrix b').det = (b.toMatrix b').det * (cartesianMatrix b).det := by
  rw [cartesianMatrix_eq_mul b b', Matrix.det_mul, mul_comm]

/-- Three vectors are linearly independent, and hence a basis, exactly when their basis matrix has
nonzero determinant. -/
lemma det_cartesianMatrix_ne_zero_iff (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    (cartesianMatrix v).det ≠ 0 ↔ LinearIndependent ℝ v := by
  rw [cartesianMatrix, ← Basis.det_apply, ← isUnit_iff_ne_zero, ← Basis.is_basis_iff_det]
  exact ⟨And.left, fun h => ⟨h, h.span_eq_top_of_card_eq_finrank' (by simp)⟩⟩

/-- The parallelepiped spanned by three vectors has volume `|det B|`. -/
lemma volume_parallelepiped (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    volume (parallelepiped v) = ENNReal.ofReal |(cartesianMatrix v).det| := by
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).addHaar_eq_volume, Measure.addHaar_parallelepiped,
    Basis.det_apply, cartesianMatrix]

/-! ## B. Orbits of finite group actions -/

/-- The orbits of a group action partition a finite set: the sizes of the orbits, one
representative per orbit, add up to the size of the set. -/
lemma sum_card_orbit_eq_card (G X : Type*) [Group G] [MulAction G X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)] [∀ x : X, Fintype (MulAction.orbit G x)] :
    ∑ ω : MulAction.orbitRel.Quotient G X, Fintype.card (MulAction.orbit G (Quotient.out ω)) =
      Fintype.card X := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (MulAction.selfEquivSigmaOrbits G X)).symm

/-- Orbit–stabiliser for a point with trivial stabiliser: its orbit has as many points as the group.
This instantiates Mathlib's `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. -/
lemma card_orbit_eq_card_group_of_stabilizer_eq_bot (G : Type*) {X : Type*} [Group G]
    [Fintype G] [MulAction G X] (x : X) [Fintype (MulAction.orbit G x)]
    (h : MulAction.stabilizer G x = ⊥) :
    Fintype.card (MulAction.orbit G x) = Fintype.card G := by
  classical
  have hstab : Fintype.card (MulAction.stabilizer G x) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Subgroup.eq_bot_iff_card _).mp h
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  rwa [hstab, mul_one] at key

/-! ## C. Bravais lattices -/

/-- If `det B ≠ 0`, then `n ↦ B *ᵥ n` is injective on integer vectors. -/
lemma mulVec_intCast_injective {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.det ≠ 0) :
    Function.Injective fun n : Fin 3 → ℤ => B *ᵥ fun i => (n i : ℝ) := by
  intro n m h
  have h' := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)) h
  funext i
  exact_mod_cast congrFun h' i

/-- A three-dimensional Bravais lattice, given by its basis matrix `B`, whose `j`-th column holds
the Cartesian coordinates of the `j`-th primitive vector. The primitive vectors must be linearly
independent, which is required in the form `det B ≠ 0`. -/
structure BravaisLattice where
  /-- The basis matrix `B`, whose columns are the primitive vectors. -/
  basisMatrix : Matrix (Fin 3) (Fin 3) ℝ
  /-- The basis matrix is nonsingular. -/
  det_ne_zero : basisMatrix.det ≠ 0

namespace BravaisLattice

/-- The `j`-th primitive vector, the `j`-th column of `B`. -/
def primitiveVector (Λ : BravaisLattice) (j : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (Λ.basisMatrix.col j)

/-- The basis matrix of the primitive vectors is `B`. -/
@[simp] lemma cartesianMatrix_primitiveVector (Λ : BravaisLattice) :
    cartesianMatrix Λ.primitiveVector = Λ.basisMatrix := by
  ext i j
  simp [primitiveVector]

/-- The primitive vectors are linearly independent because `det B ≠ 0`. -/
lemma linearIndependent_primitiveVector (Λ : BravaisLattice) :
    LinearIndependent ℝ Λ.primitiveVector :=
  (det_cartesianMatrix_ne_zero_iff _).mp (by simpa using Λ.det_ne_zero)

/-- The primitive vectors as a basis of Euclidean space. -/
noncomputable def basis (Λ : BravaisLattice) : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  basisOfLinearIndependentOfCardEqFinrank Λ.linearIndependent_primitiveVector (by simp)

/-- The vectors of the primitive basis are the primitive vectors. -/
@[simp] lemma coe_basis (Λ : BravaisLattice) : ⇑Λ.basis = Λ.primitiveVector :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The lattice vector `B *ᵥ n` of an integer cell index `n`. -/
noncomputable def latticeVector (Λ : BravaisLattice) :
    (Fin 3 → ℤ) →+ EuclideanSpace ℝ (Fin 3) where
  toFun n := WithLp.toLp 2 (Λ.basisMatrix *ᵥ fun i => (n i : ℝ))
  map_zero' := by
    ext i
    simp [Matrix.mulVec]
  map_add' n m := by
    rw [← WithLp.toLp_add, ← Matrix.mulVec_add]
    congr 2
    ext i
    simp

/-- The lattice vector of `n` is `B *ᵥ n`. -/
lemma latticeVector_apply (Λ : BravaisLattice) (n : Fin 3 → ℤ) :
    Λ.latticeVector n = WithLp.toLp 2 (Λ.basisMatrix *ᵥ fun i => (n i : ℝ)) := rfl

/-- The lattice vector of `n` is the integer combination `∑ j, n j • b j` of the primitive
vectors. -/
lemma latticeVector_eq_sum (Λ : BravaisLattice) (n : Fin 3 → ℤ) :
    Λ.latticeVector n = ∑ j, (n j : ℝ) • Λ.basis j := by
  ext i
  simp [latticeVector_apply, primitiveVector, Matrix.mulVec, dotProduct, mul_comm]

/-- The coordinates of the lattice vector `B *ᵥ n` in the primitive basis are the entries of
`n`. -/
@[simp] lemma repr_latticeVector (Λ : BravaisLattice) (n : Fin 3 → ℤ) :
    ⇑(Λ.basis.repr (Λ.latticeVector n)) = fun i => (n i : ℝ) := by
  rw [latticeVector_eq_sum, Basis.repr_sum_self]

/-- Distinct integer cell indices give distinct lattice vectors, because `det B ≠ 0`. -/
lemma latticeVector_injective (Λ : BravaisLattice) : Function.Injective Λ.latticeVector :=
  fun _ _ h => mulVec_intCast_injective Λ.det_ne_zero (WithLp.toLp_injective 2 h)

/-- The lattice `L`: the `ℤ`-span of the primitive vectors, an additive subgroup of Euclidean
space. -/
noncomputable def lattice (Λ : BravaisLattice) : Submodule ℤ (EuclideanSpace ℝ (Fin 3)) :=
  Submodule.span ℤ (Set.range Λ.basis)

/-- The lattice consists of the vectors `B *ᵥ n` with `n` an integer vector. -/
lemma mem_lattice_iff (Λ : BravaisLattice) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ Λ.lattice ↔ ∃ n : Fin 3 → ℤ, Λ.latticeVector n = x := by
  simp only [lattice, Submodule.mem_span_range_iff_exists_fun, latticeVector_eq_sum,
    Int.cast_smul_eq_zsmul]

/-- The set `{B *ᵥ n | n : Fin 3 → ℤ}` is the carrier of the submodule `L`. -/
lemma coe_lattice (Λ : BravaisLattice) :
    (Λ.lattice : Set (EuclideanSpace ℝ (Fin 3))) = Set.range Λ.latticeVector := by
  ext x
  exact Λ.mem_lattice_iff x

/-- The lattice is discrete. -/
instance instDiscreteTopologyLattice (Λ : BravaisLattice) : DiscreteTopology Λ.lattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range Λ.basis)))

/-- The lattice is a full-rank `ℤ`-lattice in Mathlib's sense. -/
instance instIsZLatticeLattice (Λ : BravaisLattice) : IsZLattice ℝ Λ.lattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range Λ.basis)))

end BravaisLattice

/-! ## D. Crystals with a motif -/

/-- A three-dimensional crystal: a Bravais lattice together with a finite nonempty motif `F`, whose
atom `f` sits at the offset `offset f` from the origin of its cell. -/
structure BravaisCrystal (F : Type*) [Finite F] [Nonempty F] extends BravaisLattice where
  /-- The offset `u f` of motif atom `f` in the reference cell. -/
  offset : F → EuclideanSpace ℝ (Fin 3)

namespace BravaisCrystal

/-- The position `B *ᵥ n + u f` of motif atom `f` in the cell with integer index `n`. -/
noncomputable def position {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (n : Fin 3 → ℤ) (f : F) : EuclideanSpace ℝ (Fin 3) :=
  X.latticeVector n + X.offset f

/-- The atomic positions `{B *ᵥ n + u f | n : Fin 3 → ℤ, f : F}`. -/
def positions {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range fun p : (Fin 3 → ℤ) × F => X.position p.1 p.2

/-- Translating the atom at `(n, f)` by the lattice vector `B *ᵥ m` gives the atom at
`(n + m, f)`. -/
lemma latticeVector_add_position {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (m n : Fin 3 → ℤ) (f : F) :
    X.latticeVector m + X.position n f = X.position (n + m) f := by
  simp only [position, map_add]
  abel

/-- The coordinates of the atom at `(n, f)` in the primitive basis are the cell index `n` plus the
coordinates of the offset `u f`. -/
lemma repr_position {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (n : Fin 3 → ℤ) (f : F) :
    ⇑(X.basis.repr (X.position n f)) = (fun i => (n i : ℝ)) + ⇑(X.basis.repr (X.offset f)) := by
  rw [position, map_add, Finsupp.coe_add, BravaisLattice.repr_latticeVector]

/-- The positions determine the index pairs `(n, f)` exactly when the motif offsets are pairwise
distinct modulo the lattice: no two different atoms have offsets differing by a lattice vector. -/
lemma position_injective_iff {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F) :
    Function.Injective (fun p : (Fin 3 → ℤ) × F => X.position p.1 p.2) ↔
      ∀ f g : F, X.offset f - X.offset g ∈ X.lattice → f = g := by
  constructor
  · intro h f g hfg
    obtain ⟨k, hk⟩ := (X.mem_lattice_iff _).mp hfg
    have hpos : X.position k g = X.position 0 f := by
      simp only [position, map_zero, zero_add, hk, sub_add_cancel]
    exact (congrArg Prod.snd (@h (k, g) (0, f) hpos)).symm
  · rintro h ⟨n, f⟩ ⟨m, g⟩ hp
    simp only [position] at hp
    obtain rfl : f = g := h f g ((X.mem_lattice_iff _).mpr ⟨m - n, by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (X.offset f)]
      exact hp.symm⟩)
    exact Prod.ext (X.latticeVector_injective (add_right_cancel hp)) rfl

/-- If the motif offsets are pairwise distinct modulo the lattice, each atomic position has a
unique cell index and motif label. -/
lemma existsUnique_index {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (hu : ∀ f g : F, X.offset f - X.offset g ∈ X.lattice → f = g)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ X.positions) :
    ∃! p : (Fin 3 → ℤ) × F, X.position p.1 p.2 = x := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p, rfl, fun q hq => X.position_injective_iff.mpr hu hq⟩

end BravaisCrystal

/-! ## E. Unimodular relabeling and cell volume -/

namespace BravaisLattice

/-- The cell spanned by the primitive vectors has volume `|det B|`. -/
lemma volume_parallelepiped_primitiveVector (Λ : BravaisLattice) :
    volume (parallelepiped Λ.primitiveVector) = ENNReal.ofReal |Λ.basisMatrix.det| := by
  rw [volume_parallelepiped, cartesianMatrix_primitiveVector]

/-- The half-open fundamental cell `ZSpan.fundamentalDomain`, the points whose primitive coordinates
lie in `[0, 1)`, also has volume `|det B|`. -/
lemma volume_fundamentalDomain (Λ : BravaisLattice) :
    volume (ZSpan.fundamentalDomain Λ.basis) = ENNReal.ofReal |Λ.basisMatrix.det| := by
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Λ.basis volume), coe_basis,
    volume_parallelepiped_primitiveVector]

/-- Relabel the cells by an integer matrix `P` with `IsUnit P.det`, that is `det P = ±1`, so that
`P` has an integer inverse. The new primitive vectors are the columns of `B * P`. -/
noncomputable def relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) : BravaisLattice where
  basisMatrix := Λ.basisMatrix * P.map (Int.cast : ℤ → ℝ)
  det_ne_zero := by
    rw [Matrix.det_mul, ← Int.cast_det]
    refine mul_ne_zero Λ.det_ne_zero ?_
    rcases Int.isUnit_iff.mp hP with h | h <;> simp [h]

/-- The basis matrix of the relabeled lattice is `B * P`. -/
lemma relabel_basisMatrix (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) :
    (Λ.relabel P hP).basisMatrix = Λ.basisMatrix * P.map (Int.cast : ℤ → ℝ) := rfl

/-- The change-of-basis matrix from the old primitive basis to the relabeled one is `P`. -/
lemma toMatrix_basis_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) :
    Λ.basis.toMatrix (Λ.relabel P hP).basis = P.map (Int.cast : ℤ → ℝ) := by
  have h := cartesianMatrix_eq_mul Λ.basis (Λ.relabel P hP).basis
  rw [coe_basis, coe_basis, cartesianMatrix_primitiveVector, cartesianMatrix_primitiveVector,
    relabel_basisMatrix] at h
  have hB : IsUnit Λ.basisMatrix.det := isUnit_iff_ne_zero.mpr Λ.det_ne_zero
  rw [coe_basis, ← Matrix.nonsing_inv_mul_cancel_left Λ.basisMatrix (Λ.basis.toMatrix _) hB, ← h,
    Matrix.nonsing_inv_mul_cancel_left Λ.basisMatrix _ hB]

/-- Relabeling transforms the basis coordinates as in a change of basis, by `P⁻¹`. -/
lemma repr_basis_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) (x : EuclideanSpace ℝ (Fin 3)) :
    ⇑((Λ.relabel P hP).basis.repr x) = (P.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ ⇑(Λ.basis.repr x) := by
  rw [repr_eq_inv_mulVec_repr Λ.basis, toMatrix_basis_relabel]

/-- A unimodular relabeling preserves `|det B|`. -/
lemma abs_det_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) :
    |(Λ.relabel P hP).basisMatrix.det| = |Λ.basisMatrix.det| := by
  rw [relabel_basisMatrix, Matrix.det_mul, ← Int.cast_det, abs_mul]
  rcases Int.isUnit_iff.mp hP with h | h <;> simp [h]

/-- A unimodular relabeling preserves the cell volume. -/
lemma volume_parallelepiped_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) :
    volume (parallelepiped (Λ.relabel P hP).primitiveVector) =
      volume (parallelepiped Λ.primitiveVector) := by
  rw [volume_parallelepiped_primitiveVector, volume_parallelepiped_primitiveVector,
    abs_det_relabel]

/-- The relabeled lattice vector of `n` is the old lattice vector of `P *ᵥ n`. -/
lemma latticeVector_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ)
    (hP : IsUnit P.det) (n : Fin 3 → ℤ) :
    (Λ.relabel P hP).latticeVector n = Λ.latticeVector (P *ᵥ n) := by
  rw [latticeVector_apply, latticeVector_apply, relabel_basisMatrix, ← Matrix.mulVec_mulVec]
  congr 2
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- A unimodular relabeling preserves the lattice. -/
lemma lattice_relabel (Λ : BravaisLattice) (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) :
    (Λ.relabel P hP).lattice = Λ.lattice := by
  ext x
  rw [mem_lattice_iff, mem_lattice_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨P *ᵥ n, (Λ.latticeVector_relabel P hP n).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨P⁻¹ *ᵥ m, ?_⟩
    rw [latticeVector_relabel, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP,
      Matrix.one_mulVec]

end BravaisLattice

namespace BravaisCrystal

/-- Relabel the cells of a crystal by a unimodular integer matrix, keeping the motif offsets. -/
noncomputable def relabel {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) : BravaisCrystal F where
  toBravaisLattice := X.toBravaisLattice.relabel P hP
  offset := X.offset

/-- The lattice of the relabeled crystal is the relabeled lattice. -/
@[simp] lemma relabel_toBravaisLattice {F : Type*} [Finite F] [Nonempty F]
    (X : BravaisCrystal F) (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) :
    (X.relabel P hP).toBravaisLattice = X.toBravaisLattice.relabel P hP := rfl

/-- A unimodular relabeling of the cells does not move any atom. -/
lemma positions_relabel {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (P : Matrix (Fin 3) (Fin 3) ℤ) (hP : IsUnit P.det) :
    (X.relabel P hP).positions = X.positions := by
  ext x
  constructor
  · rintro ⟨⟨n, f⟩, rfl⟩
    exact ⟨(P *ᵥ n, f), by simp [relabel, position, BravaisLattice.latticeVector_relabel]⟩
  · rintro ⟨⟨m, f⟩, rfl⟩
    refine ⟨(P⁻¹ *ᵥ m, f), ?_⟩
    simp [relabel, position, BravaisLattice.latticeVector_relabel, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv P hP]

/-! ## F. Sites of the Physlib crystal -/

/-- The stable Physlib crystal of a crystal with motif `F`: translation group `Fin 3 → ℤ` and unit
cell `F`, so that a site is a cell index together with a motif label. Physlib's crystals carry no
coordinates, so this crystal depends only on `F`. -/
abbrev physlibCrystal (F : Type*) [Finite F] [Nonempty F] :
    Physlib.CondensedMatter.Crystal (Fin 3 → ℤ) :=
  Physlib.CondensedMatter.Crystal.ofUnitCell (Fin 3 → ℤ) F

/-- The atomic position of a site: the site with cell `n` and label `f` sits at `B *ᵥ n + u f`. -/
noncomputable def sitePosition {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (s : (physlibCrystal F).Site) : EuclideanSpace ℝ (Fin 3) :=
  X.position s.cell s.label

/-- The site with cell `n` and label `f` sits at the position of the atom `(n, f)`. -/
@[simp] lemma sitePosition_mk {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (n : Fin 3 → ℤ) (f : F) : X.sitePosition ⟨n, f⟩ = X.position n f := rfl

/-- Translating a site by `m` sends the site for `(n, f)` to the site for `(n + m, f)`. -/
lemma vadd_mk {F : Type*} [Finite F] [Nonempty F] (m n : Fin 3 → ℤ) (f : F) :
    m +ᵥ (⟨n, f⟩ : (physlibCrystal F).Site) = ⟨n + m, f⟩ := by
  rw [Physlib.CondensedMatter.Crystal.Site.vadd_def, add_comm]

/-- Translating a site by `m` translates its position by the lattice vector `B *ᵥ m`. -/
lemma sitePosition_vadd {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (m : Fin 3 → ℤ) (s : (physlibCrystal F).Site) :
    X.sitePosition (m +ᵥ s) = X.latticeVector m + X.sitePosition s := by
  obtain ⟨n, f⟩ := s
  rw [vadd_mk, sitePosition_mk, sitePosition_mk, latticeVector_add_position]

/-- The sites occupy exactly the atomic positions. -/
lemma range_sitePosition {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F) :
    Set.range X.sitePosition = X.positions := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(s.cell, s.label), rfl⟩
  · rintro ⟨⟨n, f⟩, rfl⟩
    exact ⟨⟨n, f⟩, rfl⟩

/-- If the motif offsets are pairwise distinct modulo the lattice, distinct sites occupy distinct
positions. -/
lemma sitePosition_injective {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (hu : ∀ f g : F, X.offset f - X.offset g ∈ X.lattice → f = g) :
    Function.Injective X.sitePosition := by
  intro s t h
  have hinj := X.position_injective_iff.mpr hu
  have hst := @hinj (s.cell, s.label) (t.cell, t.label) h
  exact Physlib.CondensedMatter.Crystal.Site.ext (congrArg Prod.fst hst) (congrArg Prod.snd hst)

/-- If the motif offsets are pairwise distinct modulo the lattice, the sites of the Physlib crystal
correspond to the atomic positions. -/
noncomputable def siteEquivPositions {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (hu : ∀ f g : F, X.offset f - X.offset g ∈ X.lattice → f = g) :
    (physlibCrystal F).Site ≃ X.positions :=
  Equiv.ofBijective (fun s => ⟨X.sitePosition s, (s.cell, s.label), rfl⟩)
    ⟨fun _ _ h => X.sitePosition_injective hu (congrArg Subtype.val h), by
      rintro ⟨x, ⟨n, f⟩, rfl⟩
      exact ⟨⟨n, f⟩, rfl⟩⟩

/-- The site equivalence sends a site to its position. -/
@[simp] lemma coe_siteEquivPositions {F : Type*} [Finite F] [Nonempty F] (X : BravaisCrystal F)
    (hu : ∀ f g : F, X.offset f - X.offset g ∈ X.lattice → f = g) (s : (physlibCrystal F).Site) :
    (X.siteEquivPositions hu s : EuclideanSpace ℝ (Fin 3)) = X.sitePosition s := rfl

end BravaisCrystal

end Crystallography
