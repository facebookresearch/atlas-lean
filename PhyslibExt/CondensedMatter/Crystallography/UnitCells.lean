/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import PhyslibExt.CondensedMatter.Crystallography.BravaisLattice
public import PhyslibExt.CondensedMatter.Crystallography.ReciprocalLattice

/-!
# Unit cells: GL(3,Z) bases, conventional cells, Wigner-Seitz cells, 14 Bravais lattices

Conventional vs primitive cells, the GL(3,Z) change-of-basis theorem, Wigner-Seitz covering and
disjointness, and a reference table of the 14 Bravais lattices.

## i. Overview

A `BravaisLattice` (MF09) is the canonical embedded full-rank integer lattice: its basis matrix
`B` has the lattice basis vectors (the `primitiveVector`s) as columns, and its `lattice` is
their integer span. This must not be confused with the motif (the finite set of atomic offsets
traditionally called the crystallographic basis): the lattice basis vectors generate
translations, while the motif offsets in `BravaisCrystal` place atoms within each cell. This
module introduces no new lattice or motif type; everything is built on the MF09 API.

Two bases span the same lattice exactly when they differ by `GL(3, Z)`: `B' = B * P` for an
integer matrix `P` with `det P = ±1` (`lattice_eq_iff_gl`). The `<=` direction reuses
`BravaisLattice.lattice_relabel`; the `=>` direction extracts `P` from equal lattices and proves
`det P = ±1` from the determinant equation. The cell volume `|det B|` is then independent of the
choice of basis, with the sign of `det` (left- vs right-handed bases) absorbed by the absolute
value.

A conventional cell is the fundamental parallelepiped of a coarse superlattice: `Λc` is a
superlattice of `Λf` (`IsSuperlatticeOf`) when `Λc.lattice ≤ Λf.lattice`, e.g. the simple cubic
lattice of side `a` inside the face-centred cubic lattice. The number of lattice points per
conventional cell (`pointsPerCell`, the cardinality of the quotient) equals `V_conv / V_prim`,
proved to be a natural number (`pointsPerCell_eq_volume_ratio`): 4 for FCC, 2 for BCC.

The Wigner-Seitz cell is reused from `BravaisLattice.wignerSeitzCell` (closed convention: points
at least as close to the origin as to any lattice point, ties included) together with its
fundamental-domain theorem; this module proves the pointwise covering and disjoint-interiors
statements, shows overlaps of closed cells lie on the boundary, and exhibits overlapping
boundary points.

The 14 Bravais lattices and seven crystal systems are a reference-only data table
(`bravaisTable`): names, systems, centring types and explicit parametrised basis matrices, with
machine-checked nonzero determinants and pairwise-distinct entries. No completeness or
classification theorem is claimed.

## ii. Key results

- `Crystallography.BravaisLattice.exists_intMatrix_of_lattice_le` : a sublattice inclusion gives
  an integer change-of-basis matrix.
- `Crystallography.BravaisLattice.lattice_eq_iff_gl` : same lattice iff `GL(3, Z)`-related
  bases.
- `Crystallography.BravaisLattice.abs_det_eq_of_lattice_eq` : `|det B|` is basis-independent.
- `Crystallography.BravaisLattice.volume_parallelepiped_eq_of_lattice_eq` : cell volume is
  basis-independent.
- `Crystallography.BravaisLattice.IsSuperlatticeOf` : the conventional-cell (superlattice)
  relation.
- `Crystallography.BravaisLattice.pointsPerCell` : lattice points per conventional cell.
- `Crystallography.BravaisLattice.pointsPerCell_eq_volume_ratio` : the count equals
  `V_conv / V_prim` and the sublattice index.
- `Crystallography.BravaisLattice.pointsPerCell_faceCenteredCubic` : FCC has 4.
- `Crystallography.BravaisLattice.pointsPerCell_bodyCenteredCubic` : BCC has 2.
- `Crystallography.BravaisLattice.wignerSeitzCell_cover` : translates cover space.
- `Crystallography.BravaisLattice.wignerSeitzCell_disjoint_interior_translate` : distinct
  translates have disjoint interiors.
- `Crystallography.BravaisLattice.wignerSeitzCell_exists_overlap` : closed cells can overlap.
- `Crystallography.bravaisTable` : the 14 Bravais lattices (reference-only).
- `Crystallography.bravaisTable_injective` : the 14 entries are pairwise distinct.

## iii. Table of contents

- A. Integer change of basis and GL(3, Z)
- B. Cell volume invariance
- C. Superlattices and points per cell
- D. FCC and BCC
- E. Wigner-Seitz covering and disjoint interiors
- F. The 14 Bravais lattices (reference-only)

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapters 4 and 5, for Bravais lattices, Wigner-Seitz cells and reciprocal lattices.
* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005), Chapter 2.
* DoITPoMS (Cambridge) TLP Library: "Crystallography" and "Lattice Planes and Miller Indices".
* MITx 3.012S.3x Structure of Materials; Allen & Thomas, *The Structure of Materials*.

-/

@[expose] public section

open Module MeasureTheory
open scoped Matrix

namespace Crystallography

/-! ## A. Integer change of basis and GL(3, Z) -/

namespace BravaisLattice

/-- From a sublattice inclusion, extract the integer change-of-basis matrix: each coarse
primitive vector is a fine-lattice vector, hence an integer combination of the fine primitive
vectors, and these combinations are the columns of `M` with `B_c = B_f * M`. -/
lemma exists_intMatrix_of_lattice_le (Λc Λf : BravaisLattice) (h : Λc.lattice ≤ Λf.lattice) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ,
      Λc.basisMatrix = Λf.basisMatrix * M.map (Int.cast : ℤ → ℝ) := by
  choose c hc using fun j : Fin 3 =>
    (Λf.mem_lattice_iff (Λc.primitiveVector j)).mp (h (Λc.primitiveVector_mem_lattice j))
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  have key : ∀ j : Fin 3,
      Λf.basisMatrix *ᵥ (fun i => ((c j i : ℤ) : ℝ)) = Λc.basisMatrix.col j := by
    intro j
    have hcol := hc j
    simp only [latticeVector_apply, primitiveVector] at hcol
    exact WithLp.toLp_injective 2 hcol
  ext i j
  have h2 := congrFun (key j) i
  rw [Matrix.col_apply] at h2
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mulVec,
    dotProduct] at h2 ⊢
  exact h2.symm

/-- **GL(3, Z) change of basis**: two `BravaisLattice`s span the same lattice iff their basis
matrices satisfy `B' = B * P` for an integer matrix `P` with `det P = ±1` (as `IsUnit P.det`),
in the column convention of `BravaisLattice`. The reverse direction reuses `lattice_relabel`;
the forward direction extracts `P` and proves `det P = ±1` from the determinant equations. -/
theorem lattice_eq_iff_gl (Λ Λ' : BravaisLattice) :
    Λ.lattice = Λ'.lattice ↔
      ∃ P : Matrix (Fin 3) (Fin 3) ℤ,
        IsUnit P.det ∧ Λ'.basisMatrix = Λ.basisMatrix * P.map (Int.cast : ℤ → ℝ) := by
  constructor
  · intro heq
    obtain ⟨P, hP⟩ := exists_intMatrix_of_lattice_le Λ' Λ heq.symm.le
    obtain ⟨Q, hQ⟩ := exists_intMatrix_of_lattice_le Λ Λ' heq.le
    have dP : Λ'.basisMatrix.det = Λ.basisMatrix.det * (P.det : ℝ) := by
      rw [hP, Matrix.det_mul, ← Int.cast_det]
    have dQ : Λ.basisMatrix.det = Λ'.basisMatrix.det * (Q.det : ℝ) := by
      rw [hQ, Matrix.det_mul, ← Int.cast_det]
    have hPQ : Λ.basisMatrix.det * ((P.det : ℝ) * (Q.det : ℝ)) = Λ.basisMatrix.det := by
      have e : Λ.basisMatrix.det * ((P.det : ℝ) * (Q.det : ℝ))
          = (Λ.basisMatrix.det * (P.det : ℝ)) * (Q.det : ℝ) := by ring
      rw [e, ← dP]
      exact dQ.symm
    have h2 : Λ.basisMatrix.det * ((P.det : ℝ) * (Q.det : ℝ))
        = Λ.basisMatrix.det * 1 := by rw [hPQ, mul_one]
    have hX : (P.det : ℝ) * (Q.det : ℝ) = 1 := mul_left_cancel₀ Λ.det_ne_zero h2
    have hmul : P.det * Q.det = 1 := by
      have h3 : ((P.det * Q.det : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
        rw [Int.cast_mul, Int.cast_one]
        exact hX
      exact Int.cast_injective h3
    refine ⟨P, ?_, hP⟩
    exact ⟨⟨P.det, Q.det, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  · rintro ⟨P, hP, hB⟩
    have hEq : Λ' = Λ.relabel P hP := basisMatrix_injective (by rw [hB, relabel_basisMatrix])
    rw [hEq, lattice_relabel]

/-! ## B. Cell volume invariance -/

/-- The cell volume `|det B|` does not depend on the choice of basis: lattices with the same
lattice vectors have the same `|det|`. The absolute value absorbs the sign, so left-handed
(`det B < 0`) and right-handed bases give the same volume. -/
lemma abs_det_eq_of_lattice_eq (Λ Λ' : BravaisLattice) (h : Λ.lattice = Λ'.lattice) :
    |Λ.basisMatrix.det| = |Λ'.basisMatrix.det| := by
  obtain ⟨P, hP, hB⟩ := (lattice_eq_iff_gl Λ Λ').mp h
  have hEq : Λ' = Λ.relabel P hP := basisMatrix_injective (by rw [hB, relabel_basisMatrix])
  rw [hEq, abs_det_relabel]

/-- The volume of the fundamental parallelepiped depends only on the lattice, not on the
choice of primitive vectors. -/
lemma volume_parallelepiped_eq_of_lattice_eq (Λ Λ' : BravaisLattice)
    (h : Λ.lattice = Λ'.lattice) :
    volume (parallelepiped Λ.primitiveVector)
      = volume (parallelepiped Λ'.primitiveVector) := by
  rw [volume_parallelepiped_primitiveVector, volume_parallelepiped_primitiveVector,
    abs_det_eq_of_lattice_eq Λ Λ' h]

/-! ## C. Superlattices and points per cell -/

/-- `Λc` is a superlattice of `Λf` when its lattice is contained in that of `Λf`: the coarse
(conventional) cell is larger. Running example: the simple cubic lattice of side `a` is a
superlattice of the face-centred cubic lattice with the same conventional cell. -/
def IsSuperlatticeOf (Λc Λf : BravaisLattice) : Prop := Λc.lattice ≤ Λf.lattice

/-- The conventional cell of `Λc`: its fundamental parallelepiped. For a superlattice pair this
is the cell whose lattice points are counted by `pointsPerCell`. -/
def conventionalCell (Λc : BravaisLattice) : Set (EuclideanSpace ℝ (Fin 3)) :=
  parallelepiped Λc.primitiveVector

/-- The number of lattice points of `Λf` per conventional cell of `Λc`: the cardinality of the
quotient of the fine lattice by the coarse sublattice. Meaningful when
`IsSuperlatticeOf Λc Λf`, in which case `pointsPerCell_eq_volume_ratio` shows it equals
`V_conv / V_prim`. -/
noncomputable def pointsPerCell (Λc Λf : BravaisLattice) : ℕ :=
  Nat.card (↥Λf.lattice ⧸ (Λc.lattice.comap Λf.lattice.subtype))

/-- The lattice homomorphism to the subtype, for `latticeEquivInt`. -/
noncomputable def latticeHom (Λ : BravaisLattice) : (Fin 3 → ℤ) →+ Λ.lattice where
  toFun n := ⟨Λ.latticeVector n, (Λ.mem_lattice_iff _).mpr ⟨n, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero Λ.latticeVector)
  map_add' a b := Subtype.ext (map_add Λ.latticeVector a b)

/-- The lattice vectors are indexed by integer vectors: `n ↦ B *ᵥ n` is an additive equivalence
between `Fin 3 → ℤ` and the lattice. -/
noncomputable def latticeEquivInt (Λ : BravaisLattice) : (Fin 3 → ℤ) ≃+ Λ.lattice :=
  AddEquiv.ofBijective (latticeHom Λ)
    ⟨fun a b h => Λ.latticeVector_injective (Subtype.ext_iff.mp h), fun x => by
      obtain ⟨n, hn⟩ := (Λ.mem_lattice_iff x.1).mp x.2
      exact ⟨n, Subtype.ext hn⟩⟩

/-- The equivalence sends `n` to the lattice vector `B *ᵥ n`. -/
@[simp] lemma coe_latticeEquivInt (Λ : BravaisLattice) (n : Fin 3 → ℤ) :
    ((latticeEquivInt Λ n : Λ.lattice) : EuclideanSpace ℝ (Fin 3))
      = Λ.latticeVector n :=
  rfl

/-- Casting an integer matrix-vector product to the reals factors through the cast matrix. -/
private lemma map_intCast_mulVec (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => ((v i : ℤ) : ℝ))
      = (fun i => (((M *ᵥ v) i : ℤ) : ℝ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

/-- **Points per conventional cell**: for a superlattice pair, the number of fine-lattice points
per coarse cell equals `V_conv / V_prim`, a natural number, and equals the sublattice index
(the cardinality of the quotient). -/
theorem pointsPerCell_eq_volume_ratio (Λc Λf : BravaisLattice)
    (h : Λc.lattice ≤ Λf.lattice) :
    ∃ k : ℕ, pointsPerCell Λc Λf = k ∧
      |Λc.basisMatrix.det| = (k : ℝ) * |Λf.basisMatrix.det| ∧
      |Λc.basisMatrix.det| / |Λf.basisMatrix.det| = (k : ℝ) := by
  obtain ⟨M, hM⟩ := exists_intMatrix_of_lattice_le Λc Λf h
  have hdetM : M.det ≠ 0 := by
    have d : Λc.basisMatrix.det = Λf.basisMatrix.det * (M.det : ℝ) := by
      rw [hM, Matrix.det_mul, ← Int.cast_det]
    intro hz
    rw [hz] at d
    simp only [Int.cast_zero, mul_zero] at d
    exact Λc.det_ne_zero d
  set N : Submodule ℤ (Fin 3 → ℤ) := Submodule.span ℤ (Set.range M.col) with hNdef
  have hφ : Function.Injective M.mulVecLin := by
    intro a b hab
    have hab' : M *ᵥ a = M *ᵥ b := by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hab
      exact hab
    have hcast : (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => ((a i : ℤ) : ℝ))
        = (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => ((b i : ℤ) : ℝ)) := by
      rw [map_intCast_mulVec, map_intCast_mulVec, hab']
    have hUnit : IsUnit (M.map (Int.cast : ℤ → ℝ)).det := by
      rw [← Int.cast_det]
      exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdetM)
    have hUnitMat : IsUnit (M.map (Int.cast : ℤ → ℝ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hUnit
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hUnitMat hcast
    funext i
    exact Int.cast_injective (congrFun hinj i)
  have hcols : LinearIndependent ℤ M.col :=
    Matrix.mulVec_injective_iff.mp fun a b h => hφ (by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      exact h)
  have hli : LinearIndependent ℤ
      (fun i => (⟨M.col i, Submodule.subset_span (Set.mem_range_self i)⟩ : ↥N)) := by
    have hcols' : LinearIndependent ℤ
        (N.subtype ∘ fun i => (⟨M.col i,
          Submodule.subset_span (Set.mem_range_self i)⟩ : ↥N)) := hcols
    exact LinearIndependent.of_comp N.subtype hcols'
  have hsp : ⊤ ≤ Submodule.span ℤ
      (Set.range fun i => (⟨M.col i, Submodule.subset_span (Set.mem_range_self i)⟩ :
        ↥N)) := by
    intro x _
    have hx2 : (x : Fin 3 → ℤ) ∈ N := x.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx2
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hc
  set bN : Basis (Fin 3) ℤ ↥N := Basis.mk hli hsp with hbNdef
  have hbN : ∀ i : Fin 3, ((bN i : ↥N) : Fin 3 → ℤ) = M.col i := by
    intro i
    rw [hbNdef]
    exact congrArg Subtype.val (Basis.mk_apply hli hsp i)
  have hFree : Module.Free ℤ (Fin 3 → ℤ) := Module.Free.of_basis (Pi.basisFun ℤ (Fin 3))
  have hFin : Module.Finite ℤ (Fin 3 → ℤ) :=
    Module.Finite.of_basis (Pi.basisFun ℤ (Fin 3))
  have hcard := @Submodule.natAbs_det_basis_change (Fin 3 → ℤ) inferInstance hFree hFin
    (Fin 3) inferInstance inferInstance (Pi.basisFun ℤ (Fin 3)) N bN
  have hdet : (Pi.basisFun ℤ (Fin 3)).det ((↑) ∘ ⇑bN) = M.det := by
    rw [Pi.basisFun_det_apply]
    have hof : Matrix.of ((↑) ∘ ⇑bN) = Mᵀ := by
      ext i j
      simp only [Matrix.of_apply, Function.comp_apply, hbN, Matrix.col_apply,
        Matrix.transpose_apply]
    rw [hof, Matrix.det_transpose]
  rw [hdet] at hcard
  set E : (Fin 3 → ℤ) ≃+ ↥Λf.lattice := latticeEquivInt Λf with hEdef
  set N' : Submodule ℤ ↥Λf.lattice := Λc.lattice.comap Λf.lattice.subtype with hN'def
  have hcol : ∀ j : Fin 3, Λf.latticeVector (M.col j) = Λc.primitiveVector j := by
    intro j
    rw [latticeVector_apply, primitiveVector]
    congr 1
    have hcolM : Λc.basisMatrix.col j
        = (Λf.basisMatrix * M.map (Int.cast : ℤ → ℝ)).col j := by rw [hM]
    rw [hcolM]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
      Matrix.col_apply]
  have hmem : ∀ z : Fin 3 → ℤ, z ∈ N ↔ Λf.latticeVector z ∈ Λc.lattice := by
    intro z
    constructor
    · intro hz
      refine Submodule.span_induction
        (p := fun x _ => Λf.latticeVector x ∈ Λc.lattice) ?_ ?_ ?_ ?_ hz
      · intro x hx
        obtain ⟨j, rfl⟩ := hx
        rw [hcol j]
        exact Λc.primitiveVector_mem_lattice j
      · rw [map_zero]
        exact Λc.lattice.zero_mem
      · intro x y _ _ ihx ihy
        rw [map_add]
        exact add_mem ihx ihy
      · intro a x _ ih
        rw [map_zsmul]
        exact Submodule.smul_mem _ _ ih
    · intro hfz
      obtain ⟨w, hw⟩ := (Λc.mem_lattice_iff _).mp hfz
      have hw' : Λc.basisMatrix *ᵥ (fun i => ((w i : ℤ) : ℝ))
          = Λf.basisMatrix *ᵥ (fun i => ((z i : ℤ) : ℝ)) := by
        rw [latticeVector_apply, latticeVector_apply] at hw
        exact WithLp.toLp_injective 2 hw
      have hBw : Λc.basisMatrix *ᵥ (fun i => ((w i : ℤ) : ℝ))
          = Λf.basisMatrix *ᵥ (fun i => (((M *ᵥ w) i : ℤ) : ℝ)) := by
        rw [hM, ← Matrix.mulVec_mulVec]
        congr 1
        exact map_intCast_mulVec M w
      have hzw : Λf.latticeVector z = Λf.latticeVector (M *ᵥ w) := by
        rw [latticeVector_apply, latticeVector_apply]
        congr 1
        rw [← hw', hBw]
      have hMw : z = M *ᵥ w := Λf.latticeVector_injective hzw
      rw [hMw, hNdef, ← Matrix.range_mulVecLin]
      exact ⟨w, Matrix.mulVecLin_apply M w⟩
  have hbridge : ∀ z : Fin 3 → ℤ,
      Λf.lattice.subtype (E z) = Λf.latticeVector z := by
    intro z
    simp only [hEdef, Submodule.coe_subtype, coe_latticeEquivInt]
  have hrel : ∀ x y : Fin 3 → ℤ,
      N.quotientRel x y ↔ N'.quotientRel (E x) (E y) := by
    intro x y
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    have hsub : E x - E y = E (x - y) := by simp
    rw [hsub, hN'def, Submodule.mem_comap, hbridge]
    exact hmem (x - y)
  have hequiv : ((Fin 3 → ℤ) ⧸ N) ≃ (↥Λf.lattice ⧸ N') :=
    Quotient.congr (ra := N.quotientRel) (rb := N'.quotientRel) E.toEquiv hrel
  have hcard2 : Nat.card (↥Λf.lattice ⧸ N') = M.det.natAbs := by
    rw [← Nat.card_congr hequiv]
    exact hcard.symm
  have hvol : |Λc.basisMatrix.det| = (M.det.natAbs : ℝ) * |Λf.basisMatrix.det| := by
    have d : Λc.basisMatrix.det = Λf.basisMatrix.det * (M.det : ℝ) := by
      rw [hM, Matrix.det_mul, ← Int.cast_det]
    have habs : |(M.det : ℝ)| = (M.det.natAbs : ℝ) := by
      rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]
    rw [d, abs_mul, habs]
    exact mul_comm _ _
  have hBf : |Λf.basisMatrix.det| ≠ 0 := abs_ne_zero.mpr Λf.det_ne_zero
  refine ⟨M.det.natAbs, ?_, hvol, ?_⟩
  · exact hcard2
  · rw [hvol]
    field_simp

/-! ## D. FCC and BCC -/

/-- The simple cubic lattice of side `a` is a superlattice of the face-centred cubic lattice:
each cubic edge is an integer combination of FCC primitive vectors. -/
lemma fcc_superlattice (a : ℝ) (ha : 0 < a) :
    (simpleCubic a ha).lattice ≤ (faceCenteredCubic a ha).lattice := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  obtain ⟨j, rfl⟩ := hx
  rw [coe_basis]
  fin_cases j
  · refine ((faceCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![-1, 1, 1], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [faceCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring
  · refine ((faceCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![1, -1, 1], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [faceCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring
  · refine ((faceCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![1, 1, -1], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [faceCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring

/-- The simple cubic lattice of side `a` is a superlattice of the body-centred cubic lattice:
each cubic edge is an integer combination of BCC primitive vectors. -/
lemma bcc_superlattice (a : ℝ) (ha : 0 < a) :
    (simpleCubic a ha).lattice ≤ (bodyCenteredCubic a ha).lattice := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  obtain ⟨j, rfl⟩ := hx
  rw [coe_basis]
  fin_cases j
  · refine ((bodyCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![0, 1, 1], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [bodyCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring
  · refine ((bodyCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![1, 0, 1], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [bodyCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring
  · refine ((bodyCenteredCubic a ha).mem_lattice_iff _).mpr ⟨![1, 1, 0], ?_⟩
    rw [latticeVector_apply, primitiveVector]
    congr 1
    ext i
    fin_cases i <;> simp [bodyCenteredCubic, simpleCubic, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.col_apply, Matrix.one_apply] <;> ring

/-- **FCC has 4 lattice points per conventional cubic cell**, by the general theorem. The
conventional cell is the cube (basis matrix `a • 1`); the FCC primitive vectors are
`(a/2) (0,1,1)`, `(a/2) (1,0,1)` and `(a/2) (1,1,0)`. -/
theorem pointsPerCell_faceCenteredCubic (a : ℝ) (ha : 0 < a) :
    pointsPerCell (simpleCubic a ha) (faceCenteredCubic a ha) = 4 ∧
      |(simpleCubic a ha).basisMatrix.det|
        = 4 * |(faceCenteredCubic a ha).basisMatrix.det| ∧
      |(simpleCubic a ha).basisMatrix.det| / |(faceCenteredCubic a ha).basisMatrix.det| = 4 := by
  obtain ⟨k, hcard, hvol, hratio⟩ :=
    pointsPerCell_eq_volume_ratio (simpleCubic a ha) (faceCenteredCubic a ha)
      (fcc_superlattice a ha)
  have vSC : |(simpleCubic a ha).basisMatrix.det| = a ^ 3 := by
    change |((a • 1 : Matrix (Fin 3) (Fin 3) ℝ)).det| = a ^ 3
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      abs_of_pos (pow_pos ha 3)]
  have vFCC : |(faceCenteredCubic a ha).basisMatrix.det| = a ^ 3 / 4 := by
    change |((a / 2) • !![0, 1, 1; 1, 0, 1; 1, 1, 0]).det| = a ^ 3 / 4
    have dM : (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ).det = 2 := by
      simp [Matrix.det_fin_three]
      norm_num
    rw [Matrix.det_smul, Fintype.card_fin, dM,
      abs_of_pos (by positivity : (0 : ℝ) < (a / 2) ^ 3 * 2)]
    ring
  have hk : k = 4 := by
    have hvol' := hvol
    rw [vSC, vFCC] at hvol'
    have ha3 : (0 : ℝ) < a ^ 3 / 4 := by positivity
    have h4 : (k : ℝ) * (a ^ 3 / 4) = 4 * (a ^ 3 / 4) := by
      rw [← hvol']
      ring
    have hk4 : (k : ℝ) = 4 := mul_right_cancel₀ (ne_of_gt ha3) h4
    exact Nat.cast_injective hk4
  subst hk
  simp only [Nat.cast_ofNat] at hvol hratio
  exact ⟨hcard, hvol, hratio⟩

/-- **BCC has 2 lattice points per conventional cubic cell**, by the general theorem. The
conventional cell is the cube (basis matrix `a • 1`); the BCC primitive vectors are
`(a/2) (-1,1,1)`, `(a/2) (1,-1,1)` and `(a/2) (1,1,-1)`. -/
theorem pointsPerCell_bodyCenteredCubic (a : ℝ) (ha : 0 < a) :
    pointsPerCell (simpleCubic a ha) (bodyCenteredCubic a ha) = 2 ∧
      |(simpleCubic a ha).basisMatrix.det|
        = 2 * |(bodyCenteredCubic a ha).basisMatrix.det| ∧
      |(simpleCubic a ha).basisMatrix.det| / |(bodyCenteredCubic a ha).basisMatrix.det| = 2 := by
  obtain ⟨k, hcard, hvol, hratio⟩ :=
    pointsPerCell_eq_volume_ratio (simpleCubic a ha) (bodyCenteredCubic a ha)
      (bcc_superlattice a ha)
  have vSC : |(simpleCubic a ha).basisMatrix.det| = a ^ 3 := by
    change |((a • 1 : Matrix (Fin 3) (Fin 3) ℝ)).det| = a ^ 3
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      abs_of_pos (pow_pos ha 3)]
  have vBCC : |(bodyCenteredCubic a ha).basisMatrix.det| = a ^ 3 / 2 := by
    change |((a / 2) • !![-1, 1, 1; 1, -1, 1; 1, 1, -1]).det| = a ^ 3 / 2
    have dM : (!![-1, 1, 1; 1, -1, 1; 1, 1, -1] : Matrix (Fin 3) (Fin 3) ℝ).det = 4 := by
      simp [Matrix.det_fin_three]
      norm_num
    rw [Matrix.det_smul, Fintype.card_fin, dM,
      abs_of_pos (by positivity : (0 : ℝ) < (a / 2) ^ 3 * 4)]
    ring
  have hk : k = 2 := by
    have hvol' := hvol
    rw [vSC, vBCC] at hvol'
    have ha3 : (0 : ℝ) < a ^ 3 / 2 := by positivity
    have h2 : (k : ℝ) * (a ^ 3 / 2) = 2 * (a ^ 3 / 2) := by
      rw [← hvol']
      ring
    have hk2 : (k : ℝ) = 2 := mul_right_cancel₀ (ne_of_gt ha3) h2
    exact Nat.cast_injective hk2
  subst hk
  simp only [Nat.cast_ofNat] at hvol hratio
  exact ⟨hcard, hvol, hratio⟩

/-! ## E. Wigner-Seitz covering and disjoint interiors -/

/-- **Wigner-Seitz covering**: the lattice translates of the (closed) Wigner-Seitz cell cover
the whole space. Boundary convention (from `wignerSeitzCell`): the closed cell of points at
least as close to the origin as to any lattice point, ties included. -/
theorem wignerSeitzCell_cover (Λ : BravaisLattice) (x : EuclideanSpace ℝ (Fin 3)) :
    ∃ R ∈ Λ.lattice, x - R ∈ Λ.wignerSeitzCell := by
  obtain ⟨R₀, hR₀, hmin⟩ := Λ.exists_forall_norm_sub_le x
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR
  have hle := hmin _ (Λ.lattice.add_mem hR₀ hR)
  have e : x - R₀ - R = x - (R₀ + R) := by abel
  rw [e]
  exact hle

/-- The Wigner-Seitz cell is centrally symmetric. -/
lemma wignerSeitzCell_neg_mem (Λ : BravaisLattice) (x : EuclideanSpace ℝ (Fin 3)) :
    -x ∈ Λ.wignerSeitzCell ↔ x ∈ Λ.wignerSeitzCell := by
  constructor <;> intro h R hR
  · have h1 := h (-R) (neg_mem hR)
    have e : x - R = -(-x - -R) := by abel
    rw [e, norm_neg, (norm_neg x).symm]
    exact h1
  · have h1 := h (-R) (neg_mem hR)
    have e' : -x - R = -(x - -R) := by abel
    simp only [e', norm_neg]
    exact h1

/-- Points in the interior of the Wigner-Seitz cell are strictly closer to the origin than to
any other lattice point. -/
lemma wignerSeitzCell_interior_strict (Λ : BravaisLattice) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ interior Λ.wignerSeitzCell) (R : EuclideanSpace ℝ (Fin 3))
    (hR : R ∈ Λ.lattice) (hRne : R ≠ 0) : ‖x‖ < ‖x - R‖ := by
  by_contra hle
  rw [not_lt] at hle
  have hxmem : x ∈ Λ.wignerSeitzCell := interior_subset hx
  have heq : ‖x‖ = ‖x - R‖ := le_antisymm (hxmem R hR) hle
  obtain ⟨δ, hδ, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) x hx
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hRne
  have hRne' : ‖R‖ ≠ 0 := ne_of_gt hRpos
  set t : ℝ := δ / (2 * ‖R‖) with htdef
  have ht : 0 < t := by
    rw [htdef]
    positivity
  set y : EuclideanSpace ℝ (Fin 3) := x + t • R with hydef
  have htyR : t * ‖R‖ = δ / 2 := by
    rw [htdef]
    field_simp
  have hyball : dist y x < δ := by
    rw [dist_eq_norm]
    have hyx : y - x = t • R := by
      rw [hydef]
      abel
    rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htyR]
    linarith
  have hyWS : y ∈ Λ.wignerSeitzCell :=
    interior_subset (hball (Metric.mem_ball.mpr hyball))
  have hle2 := hyWS R hR
  have hdiff : ‖y‖ ^ 2 - ‖y - R‖ ^ 2 = 2 * t * ‖R‖ ^ 2 := by
    have hyR : y - R = (x - R) + t • R := by
      rw [hydef]
      abel
    rw [hyR, hydef, norm_add_sq_real, norm_add_sq_real]
    simp only [real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    rw [heq]
    ring
  have hN : (0 : ℝ) < ‖R‖ ^ 2 := pow_pos hRpos 2
  have hpos : (0 : ℝ) < 2 * t * ‖R‖ ^ 2 := by positivity
  have hsq : ‖y - R‖ ^ 2 < ‖y‖ ^ 2 := by linarith
  have hfactor : (‖y‖ - ‖y - R‖) * (‖y‖ + ‖y - R‖) = ‖y‖ ^ 2 - ‖y - R‖ ^ 2 := by ring
  have hprod : (0 : ℝ) < (‖y‖ - ‖y - R‖) * (‖y‖ + ‖y - R‖) := by
    rw [hfactor]
    linarith
  have hsum : (0 : ℝ) ≤ ‖y‖ + ‖y - R‖ := by positivity
  have hlt : ‖y - R‖ < ‖y‖ := by
    have hpos2 := pos_of_mul_pos_left hprod hsum
    linarith
  linarith

/-- **Wigner-Seitz disjoint interiors**: the interiors of distinct lattice translates of the
(closed) Wigner-Seitz cell are pairwise disjoint. Closed cells themselves may overlap on the
boundary (see `wignerSeitzCell_exists_overlap`); only interiors are disjoint. -/
theorem wignerSeitzCell_disjoint_interior_translate (Λ : BravaisLattice)
    (R₁ R₂ : EuclideanSpace ℝ (Fin 3)) (h1 : R₁ ∈ Λ.lattice) (h2 : R₂ ∈ Λ.lattice)
    (hne : R₁ ≠ R₂) :
    Disjoint (interior ((fun x => R₁ + x) '' Λ.wignerSeitzCell))
      (interior ((fun x => R₂ + x) '' Λ.wignerSeitzCell)) := by
  rw [Set.disjoint_left]
  rintro x hx1 hx2
  have g1 : x - R₁ ∈ interior Λ.wignerSeitzCell := by
    have h1' : (fun x => R₁ + x) = ⇑(Homeomorph.addLeft R₁) := rfl
    rw [h1', ← Homeomorph.image_interior] at hx1
    obtain ⟨w, hw, hwx⟩ := hx1
    have hwx' : R₁ + w = x := hwx
    have e : x - R₁ = w := by
      rw [← hwx']
      abel
    rwa [e]
  have g2 : x - R₂ ∈ interior Λ.wignerSeitzCell := by
    have h2' : (fun x => R₂ + x) = ⇑(Homeomorph.addLeft R₂) := rfl
    rw [h2', ← Homeomorph.image_interior] at hx2
    obtain ⟨w, hw, hwx⟩ := hx2
    have hwx' : R₂ + w = x := hwx
    have e : x - R₂ = w := by
      rw [← hwx']
      abel
    rwa [e]
  have s1 := wignerSeitzCell_interior_strict Λ _ g1 (R₂ - R₁) (sub_mem h2 h1)
    (sub_ne_zero.mpr (Ne.symm hne))
  have s2 := wignerSeitzCell_interior_strict Λ _ g2 (R₁ - R₂) (sub_mem h1 h2)
    (sub_ne_zero.mpr hne)
  rw [show (x - R₁) - (R₂ - R₁) = x - R₂ by abel] at s1
  rw [show (x - R₂) - (R₁ - R₂) = x - R₁ by abel] at s2
  linarith

/-- Overlaps of closed Wigner-Seitz cells lie on the boundary: no interior point of the cell
at the origin lies in another closed cell. This is consistent with disjoint interiors. -/
lemma wignerSeitzCell_overlap_mem_boundary (Λ : BravaisLattice)
    (x R : EuclideanSpace ℝ (Fin 3)) (hR : R ∈ Λ.lattice) (hRne : R ≠ 0)
    (hmem : x ∈ (fun y => R + y) '' Λ.wignerSeitzCell) :
    x ∉ interior Λ.wignerSeitzCell := by
  intro hxint
  obtain ⟨w, hw, hwx⟩ := hmem
  have hwx' : w + R = x := by
    rw [← hwx]
    abel
  have hle : ‖w‖ ≤ ‖x‖ := by
    have h1 := hw (-R) (neg_mem hR)
    rw [sub_neg_eq_add, hwx'] at h1
    exact h1
  have hstrict := wignerSeitzCell_interior_strict Λ x hxint R hR hRne
  have hw' : w = x - R := by
    rw [← hwx']
    abel
  rw [hw'] at hle
  linarith

/-- **Closed Wigner-Seitz cells can overlap**: some point lies in two distinct closed cells.
The midpoint of a shortest nonzero lattice vector lies in both the central cell and the cell
centred there. -/
theorem wignerSeitzCell_exists_overlap (Λ : BravaisLattice) :
    ∃ x R₁ R₂ : EuclideanSpace ℝ (Fin 3), R₁ ∈ Λ.lattice ∧ R₂ ∈ Λ.lattice ∧ R₁ ≠ R₂ ∧
      x ∈ (fun y => R₁ + y) '' Λ.wignerSeitzCell ∧
      x ∈ (fun y => R₂ + y) '' Λ.wignerSeitzCell := by
  set R₁ : EuclideanSpace ℝ (Fin 3) := Λ.primitiveVector 0 with hR₁def
  have hR₁mem : R₁ ∈ Λ.lattice := Λ.primitiveVector_mem_lattice 0
  have hR₁ne : R₁ ≠ 0 := LinearIndependent.ne_zero 0 Λ.linearIndependent_primitiveVector
  have hfinS : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ‖R₁‖ ∩
      (Λ.lattice : Set (EuclideanSpace ℝ (Fin 3)))).Finite :=
    ZSpan.setFinite_inter Λ.basis Metric.isBounded_closedBall
  have hR₁ball : R₁ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ‖R₁‖ := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hne : ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ‖R₁‖ ∩
      (Λ.lattice : Set (EuclideanSpace ℝ (Fin 3)))) \ {0}).Nonempty :=
    ⟨R₁, (Set.mem_sdiff _).mpr ⟨⟨hR₁ball, hR₁mem⟩,
      fun h => hR₁ne (Set.mem_singleton_iff.mp h)⟩⟩
  obtain ⟨R₀, hR₀mem, hR₀min⟩ := Set.exists_min_image _
    (fun R => ‖R‖ ^ 2) (hfinS.subset Set.sdiff_subset) hne
  rw [Set.mem_sdiff] at hR₀mem
  obtain ⟨⟨hR₀ball, hR₀L⟩, hR₀ne'⟩ := hR₀mem
  have hR₀ne : R₀ ≠ 0 := by simpa using hR₀ne'
  have hshort : ∀ S : EuclideanSpace ℝ (Fin 3),
      S ∈ Λ.lattice → S ≠ 0 → ‖R₀‖ ^ 2 ≤ ‖S‖ ^ 2 := by
    intro S hSL hSne
    by_cases hSb : S ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ‖R₁‖
    · exact hR₀min S
        ((Set.mem_sdiff _).mpr ⟨⟨hSb, hSL⟩, fun h => hSne (Set.mem_singleton_iff.mp h)⟩)
    · have hR₁le : ‖R₀‖ ^ 2 ≤ ‖R₁‖ ^ 2 := hR₀min R₁
        ((Set.mem_sdiff _).mpr ⟨⟨hR₁ball, hR₁mem⟩,
          fun h => hR₁ne (Set.mem_singleton_iff.mp h)⟩)
      have hballlt : ‖R₁‖ < ‖S‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hSb
        simpa using hSb
      have hfactor : (‖S‖ - ‖R₁‖) * (‖S‖ + ‖R₁‖) = ‖S‖ ^ 2 - ‖R₁‖ ^ 2 := by ring
      have hpos1 : (0 : ℝ) < ‖S‖ - ‖R₁‖ := by linarith
      have hpos2 : (0 : ℝ) < ‖S‖ + ‖R₁‖ := by
        have h1 := norm_nonneg S
        have h2 := norm_nonneg R₁
        linarith
      have hprod := mul_pos hpos1 hpos2
      rw [hfactor] at hprod
      have hsq : ‖R₁‖ ^ 2 < ‖S‖ ^ 2 := by linarith
      linarith
  set m : EuclideanSpace ℝ (Fin 3) := (2⁻¹ : ℝ) • R₀ with hmdef
  have hamm : m + m = R₀ := by
    rw [hmdef, ← add_smul, show (2⁻¹ + 2⁻¹ : ℝ) = 1 by norm_num, one_smul]
  have hmWS : m ∈ Λ.wignerSeitzCell := by
    intro S hSL
    by_contra hlt
    rw [not_le] at hlt
    have hpara := parallelogram_law_with_norm ℝ m (S - m)
    have e1 : m + (S - m) = S := by abel
    have e2 : m - (S - m) = R₀ - S := by
      rw [← hamm]
      abel
    rw [e1, e2] at hpara
    have hmn : ‖m‖ = 2⁻¹ * ‖R₀‖ := by
      rw [hmdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    have hlt' : ‖S - m‖ < ‖m‖ := by
      rw [norm_sub_rev]
      exact hlt
    have hsq2 : ‖S - m‖ ^ 2 < ‖m‖ ^ 2 := by
      have hfactor : (‖m‖ - ‖S - m‖) * (‖m‖ + ‖S - m‖)
          = ‖m‖ ^ 2 - ‖S - m‖ ^ 2 := by ring
      have hpos1 : (0 : ℝ) < ‖m‖ - ‖S - m‖ := by linarith
      have hpos2 : (0 : ℝ) < ‖m‖ + ‖S - m‖ := by
        have h1 := norm_nonneg m
        have h2 := norm_nonneg (S - m)
        linarith
      have hprod := mul_pos hpos1 hpos2
      rw [hfactor] at hprod
      linarith
    have h4C : 4 * ‖m‖ ^ 2 = ‖R₀‖ ^ 2 := by
      rw [hmn]
      ring
    have hsum : ‖S‖ ^ 2 + ‖R₀ - S‖ ^ 2 < ‖R₀‖ ^ 2 := by linarith
    by_cases hS0 : S = 0
    · subst hS0
      simp at hlt
    · by_cases hRS0 : R₀ - S = 0
      · have hSeq : S = R₀ := (sub_eq_zero.mp hRS0).symm
        rw [hSeq] at hlt
        have hme : m - R₀ = -m := by
          rw [← hamm]
          abel
        rw [hme, norm_neg] at hlt
        exact lt_irrefl _ hlt
      · have m1 := hshort S hSL hS0
        have m2 := hshort (R₀ - S) (sub_mem hR₀L hSL) hRS0
        have hnn := sq_nonneg ‖R₀‖
        linarith
  have hmneg : -m ∈ Λ.wignerSeitzCell := (wignerSeitzCell_neg_mem Λ m).mpr hmWS
  have hmR : R₀ + -m = m := by
    rw [← hamm]
    abel
  refine ⟨m, 0, R₀, Λ.lattice.zero_mem, hR₀L, ?_, ?_, ?_⟩
  · exact Ne.symm hR₀ne
  · exact ⟨m, hmWS, zero_add m⟩
  · exact ⟨-m, hmneg, hmR⟩

end BravaisLattice

/-! ## F. The 14 Bravais lattices (reference-only) -/

/-- The seven crystal systems. Reference-only: part of the 14-Bravais-lattice data table, not a
classification theorem. -/
inductive CrystalSystem
  | triclinic | monoclinic | orthorhombic | tetragonal | trigonal | hexagonal | cubic
  deriving DecidableEq, Repr

/-- Centring types. Reference-only: part of the 14-Bravais-lattice data table. `baseCentred`
is the C setting (A and B are equivalent alternate settings); `rhombohedral` is the R
centring of the trigonal system. -/
inductive CentringType
  | primitive | baseCentred | bodyCentred | faceCentred | rhombohedral
  deriving DecidableEq, Repr

/-- A Bravais-lattice table entry: name, crystal system and centring type. Reference-only: the
corresponding parametrised basis matrices are the `BravaisLattice` definitions in this section
(`simpleCubic`, `faceCenteredCubic`, `bodyCenteredCubic` and the eleven below); no completeness
or classification theorem is claimed. -/
structure BravaisEntry where
  name : String
  system : CrystalSystem
  centring : CentringType
  deriving DecidableEq, Repr

/-- The 14 Bravais lattices. Reference-only data table: names, crystal systems and centring
types, indexed by `Fin 14`. Each entry has nonzero determinant (proved in its `BravaisLattice`
definition) and the entries are pairwise distinct (`bravaisTable_injective`). -/
def bravaisTable : Fin 14 → BravaisEntry :=
  ![⟨"cP", .cubic, .primitive⟩, ⟨"cI", .cubic, .bodyCentred⟩,
    ⟨"cF", .cubic, .faceCentred⟩, ⟨"tP", .tetragonal, .primitive⟩,
    ⟨"tI", .tetragonal, .bodyCentred⟩, ⟨"oP", .orthorhombic, .primitive⟩,
    ⟨"oC", .orthorhombic, .baseCentred⟩, ⟨"oI", .orthorhombic, .bodyCentred⟩,
    ⟨"oF", .orthorhombic, .faceCentred⟩, ⟨"hP", .hexagonal, .primitive⟩,
    ⟨"hR", .trigonal, .rhombohedral⟩, ⟨"mP", .monoclinic, .primitive⟩,
    ⟨"mC", .monoclinic, .baseCentred⟩, ⟨"aP", .triclinic, .primitive⟩]

/-- The 14 table entries are pairwise distinct. -/
lemma bravaisTable_injective : Function.Injective bravaisTable := by decide

namespace BravaisLattice

/-- The primitive tetragonal lattice with parameters `a, c > 0`: diagonal basis matrix
`diag(a, a, c)`. Reference-only table entry `tP`. -/
noncomputable def tetragonalP (a c : ℝ) (ha : 0 < a) (hc : 0 < c) : BravaisLattice where
  basisMatrix := !![a, 0, 0; 0, a, 0; 0, 0, c]
  det_ne_zero := by
    have hdet : (!![a, 0, 0; 0, a, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) ℝ).det
        = a * a * c := by
      simp [Matrix.det_fin_three]
    rw [hdet]
    positivity

/-- The body-centred tetragonal lattice with parameters `a, c > 0` and primitive vectors
`(-a/2, a/2, c/2)`, `(a/2, -a/2, c/2)`, `(a/2, a/2, -c/2)`. Reference-only table entry `tI`. -/
noncomputable def tetragonalI (a c : ℝ) (ha : 0 < a) (hc : 0 < c) : BravaisLattice where
  basisMatrix := !![-a / 2, a / 2, a / 2; a / 2, -a / 2, a / 2; c / 2, c / 2, -c / 2]
  det_ne_zero := by
    have hdet : (!![-a / 2, a / 2, a / 2; a / 2, -a / 2, a / 2; c / 2, c / 2, -c / 2] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a ^ 2 * c / 2 := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The primitive orthorhombic lattice with parameters `a, b, c > 0`: diagonal basis matrix
`diag(a, b, c)`. Reference-only table entry `oP`. -/
noncomputable def orthorhombicP (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    BravaisLattice where
  basisMatrix := !![a, 0, 0; 0, b, 0; 0, 0, c]
  det_ne_zero := by
    have hdet : (!![a, 0, 0; 0, b, 0; 0, 0, c] : Matrix (Fin 3) (Fin 3) ℝ).det
        = a * b * c := by
      simp [Matrix.det_fin_three]
    rw [hdet]
    positivity

/-- The base-centred orthorhombic lattice with parameters `a, b, c > 0` and primitive vectors
`(a/2, -b/2, 0)`, `(a/2, b/2, 0)`, `(0, 0, c)`. Reference-only table entry `oC`. -/
noncomputable def orthorhombicC (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    BravaisLattice where
  basisMatrix := !![a / 2, a / 2, 0; -b / 2, b / 2, 0; 0, 0, c]
  det_ne_zero := by
    have hdet : (!![a / 2, a / 2, 0; -b / 2, b / 2, 0; 0, 0, c] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c / 2 := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The body-centred orthorhombic lattice with parameters `a, b, c > 0` and primitive vectors
`(-a/2, b/2, c/2)`, `(a/2, -b/2, c/2)`, `(a/2, b/2, -c/2)`. Reference-only table entry `oI`. -/
noncomputable def orthorhombicI (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    BravaisLattice where
  basisMatrix := !![-a / 2, a / 2, a / 2; b / 2, -b / 2, b / 2; c / 2, c / 2, -c / 2]
  det_ne_zero := by
    have hdet : (!![-a / 2, a / 2, a / 2; b / 2, -b / 2, b / 2; c / 2, c / 2, -c / 2] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c / 2 := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The face-centred orthorhombic lattice with parameters `a, b, c > 0` and primitive vectors
`(0, b/2, c/2)`, `(a/2, 0, c/2)`, `(a/2, b/2, 0)`. Reference-only table entry `oF`. -/
noncomputable def orthorhombicF (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    BravaisLattice where
  basisMatrix := !![0, a / 2, a / 2; b / 2, 0, b / 2; c / 2, c / 2, 0]
  det_ne_zero := by
    have hdet : (!![0, a / 2, a / 2; b / 2, 0, b / 2; c / 2, c / 2, 0] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c / 4 := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The primitive hexagonal lattice with parameters `a, c > 0` and primitive vectors
`(a, 0, 0)`, `(-a/2, a√3/2, 0)`, `(0, 0, c)`. Reference-only table entry `hP`. -/
noncomputable def hexagonalP (a c : ℝ) (ha : 0 < a) (hc : 0 < c) : BravaisLattice where
  basisMatrix := !![a, -a / 2, 0; 0, a * Real.sqrt 3 / 2, 0; 0, 0, c]
  det_ne_zero := by
    have hdet : (!![a, -a / 2, 0; 0, a * Real.sqrt 3 / 2, 0; 0, 0, c] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * (a * Real.sqrt 3 / 2) * c := by
      simp [Matrix.det_fin_three]
    rw [hdet]
    positivity

/-- The rhombohedral lattice with parameters `a > 0` and rhombohedral angle `α`, with
`sin α ≠ 0` and positive volume factor `1 - 3cos²α + 2cos³α > 0`. Reference-only table
entry `hR` (trigonal system, rhombohedral centring). -/
noncomputable def rhombohedralR (a α : ℝ) (ha : 0 < a) (hsin : Real.sin α ≠ 0)
    (hΩ : 0 < 1 - 3 * Real.cos α ^ 2 + 2 * Real.cos α ^ 3) : BravaisLattice where
  basisMatrix := !![a, a * Real.cos α, a * Real.cos α;
    0, a * Real.sin α, a * (Real.cos α - Real.cos α ^ 2) / Real.sin α;
    0, 0, a * Real.sqrt (1 - 3 * Real.cos α ^ 2 + 2 * Real.cos α ^ 3) / Real.sin α]
  det_ne_zero := by
    have hdet : (!![a, a * Real.cos α, a * Real.cos α;
        0, a * Real.sin α, a * (Real.cos α - Real.cos α ^ 2) / Real.sin α;
        0, 0, a * Real.sqrt (1 - 3 * Real.cos α ^ 2 + 2 * Real.cos α ^ 3) / Real.sin α] :
        Matrix (Fin 3) (Fin 3) ℝ).det
        = a ^ 3 * Real.sqrt (1 - 3 * Real.cos α ^ 2 + 2 * Real.cos α ^ 3) := by
      simp [Matrix.det_fin_three]
      field_simp
    rw [hdet]
    positivity

/-- The primitive monoclinic lattice with parameters `a, b, c > 0` and angle `β` with
`sin β ≠ 0`: basis vectors `(a, 0, 0)`, `(0, b, 0)`, `(c cosβ, 0, c sinβ)`. Reference-only
table entry `mP`. -/
noncomputable def monoclinicP (a b c β : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsin : Real.sin β ≠ 0) : BravaisLattice where
  basisMatrix := !![a, 0, c * Real.cos β; 0, b, 0; 0, 0, c * Real.sin β]
  det_ne_zero := by
    have hdet : (!![a, 0, c * Real.cos β; 0, b, 0; 0, 0, c * Real.sin β] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c * Real.sin β := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The base-centred monoclinic lattice with parameters `a, b, c > 0` and angle `β` with
`sin β ≠ 0`, with primitive vectors `(a/2, -b/2, 0)`, `(a/2, b/2, 0)`,
`(c cosβ, 0, c sinβ)`. Reference-only table entry `mC`. -/
noncomputable def monoclinicC (a b c β : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsin : Real.sin β ≠ 0) : BravaisLattice where
  basisMatrix := !![a / 2, a / 2, c * Real.cos β; -b / 2, b / 2, 0; 0, 0, c * Real.sin β]
  det_ne_zero := by
    have hdet : (!![a / 2, a / 2, c * Real.cos β; -b / 2, b / 2, 0; 0, 0, c * Real.sin β] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c * Real.sin β / 2 := by
      simp [Matrix.det_fin_three]
      ring
    rw [hdet]
    positivity

/-- The triclinic lattice with parameters `a, b, c > 0` and angles `α, β, γ`, with
`sin γ ≠ 0` and positive volume factor `1 - cos²α - cos²β - cos²γ + 2cosα cosβ cosγ > 0`.
Reference-only table entry `aP`. -/
noncomputable def triclinicP (a b c α β γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsin : Real.sin γ ≠ 0)
    (hΩ : 0 < 1 - Real.cos α ^ 2 - Real.cos β ^ 2 - Real.cos γ ^ 2
      + 2 * Real.cos α * Real.cos β * Real.cos γ) : BravaisLattice where
  basisMatrix := !![a, b * Real.cos γ, c * Real.cos β;
    0, b * Real.sin γ, c * (Real.cos α - Real.cos β * Real.cos γ) / Real.sin γ;
    0, 0, c * Real.sqrt (1 - Real.cos α ^ 2 - Real.cos β ^ 2 - Real.cos γ ^ 2
      + 2 * Real.cos α * Real.cos β * Real.cos γ) / Real.sin γ]
  det_ne_zero := by
    have hdet : (!![a, b * Real.cos γ, c * Real.cos β;
        0, b * Real.sin γ, c * (Real.cos α - Real.cos β * Real.cos γ) / Real.sin γ;
        0, 0, c * Real.sqrt (1 - Real.cos α ^ 2 - Real.cos β ^ 2 - Real.cos γ ^ 2
          + 2 * Real.cos α * Real.cos β * Real.cos γ) / Real.sin γ] :
        Matrix (Fin 3) (Fin 3) ℝ).det = a * b * c * Real.sqrt
          (1 - Real.cos α ^ 2 - Real.cos β ^ 2 - Real.cos γ ^ 2
            + 2 * Real.cos α * Real.cos β * Real.cos γ) := by
      simp [Matrix.det_fin_three]
      field_simp
    rw [hdet]
    positivity

/-- An integer multiple of `a ≠ 0` cannot be `a / 2`. Helper for same-system lattice
inequalities. -/
private lemma int_mul_ne_div_two (a : ℝ) (ha : a ≠ 0) (n : ℤ)
    (h : a * (n : ℝ) = a / 2) : False := by
  have hm : ((n : ℤ) : ℝ) = 1 / 2 := by
    have h2 : a * (n : ℝ) = a * (1 / 2) := by
      rw [h]
      ring
    exact mul_left_cancel₀ ha h2
  have hc : ((2 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    rw [Int.cast_mul, hm]
    norm_num
  have h3 : 2 * n = 1 := Int.cast_injective hc
  omega

/-- Cubic P and F with the same parameter are different lattices (reference-only). -/
lemma lattice_ne_cP_cF (a : ℝ) (ha : 0 < a) :
    (simpleCubic a ha).lattice ≠ (faceCenteredCubic a ha).lattice := by
  intro heq
  have hmem : (faceCenteredCubic a ha).primitiveVector 2
      ∈ (simpleCubic a ha).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((simpleCubic a ha).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, simpleCubic,
    faceCenteredCubic, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.col_apply, Matrix.one_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Cubic P and I with the same parameter are different lattices (reference-only). -/
lemma lattice_ne_cP_cI (a : ℝ) (ha : 0 < a) :
    (simpleCubic a ha).lattice ≠ (bodyCenteredCubic a ha).lattice := by
  intro heq
  have hmem : (bodyCenteredCubic a ha).primitiveVector 2
      ∈ (simpleCubic a ha).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((simpleCubic a ha).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, simpleCubic,
    bodyCenteredCubic, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.col_apply, Matrix.one_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Tetragonal P and I with the same parameters are different lattices (reference-only). -/
lemma lattice_ne_tP_tI (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (tetragonalP a c ha hc).lattice ≠ (tetragonalI a c ha hc).lattice := by
  intro heq
  have hmem : (tetragonalI a c ha hc).primitiveVector 2
      ∈ (tetragonalP a c ha hc).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((tetragonalP a c ha hc).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, tetragonalP, tetragonalI,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Orthorhombic P and C with the same parameters are different lattices (reference-only). -/
lemma lattice_ne_oP_oC (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (orthorhombicP a b c ha hb hc).lattice ≠ (orthorhombicC a b c ha hb hc).lattice := by
  intro heq
  have hmem : (orthorhombicC a b c ha hb hc).primitiveVector 1
      ∈ (orthorhombicP a b c ha hb hc).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((orthorhombicP a b c ha hb hc).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, orthorhombicP, orthorhombicC,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Orthorhombic P and I with the same parameters are different lattices (reference-only). -/
lemma lattice_ne_oP_oI (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (orthorhombicP a b c ha hb hc).lattice ≠ (orthorhombicI a b c ha hb hc).lattice := by
  intro heq
  have hmem : (orthorhombicI a b c ha hb hc).primitiveVector 2
      ∈ (orthorhombicP a b c ha hb hc).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((orthorhombicP a b c ha hb hc).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, orthorhombicP, orthorhombicI,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Orthorhombic P and F with the same parameters are different lattices (reference-only). -/
lemma lattice_ne_oP_oF (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (orthorhombicP a b c ha hb hc).lattice ≠ (orthorhombicF a b c ha hb hc).lattice := by
  intro heq
  have hmem : (orthorhombicF a b c ha hb hc).primitiveVector 2
      ∈ (orthorhombicP a b c ha hb hc).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((orthorhombicP a b c ha hb hc).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, orthorhombicP, orthorhombicF,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col_apply] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

/-- Cubic I and F with the same parameter are different lattices (reference-only). -/
lemma lattice_ne_cI_cF (a : ℝ) (ha : 0 < a) :
    (bodyCenteredCubic a ha).lattice ≠ (faceCenteredCubic a ha).lattice := by
  intro heq
  have hmem : (faceCenteredCubic a ha).primitiveVector 2
      ∈ (bodyCenteredCubic a ha).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((bodyCenteredCubic a ha).mem_lattice_iff _).mp hmem
  have h0 := congrArg (fun x => x.ofLp 0) hm
  have h1 := congrArg (fun x => x.ofLp 1) hm
  have h2 := congrArg (fun x => x.ofLp 2) hm
  simp only [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp] at h0 h1 h2
  simp [bodyCenteredCubic, faceCenteredCubic, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.col_apply] at h0 h1 h2
  have ha2 : (a : ℝ) / 2 ≠ 0 := div_ne_zero ha.ne' (by norm_num)
  have e0 : -((m 0 : ℤ) : ℝ) + m 1 + m 2 = 1 := by
    have hS : (a / 2) * (-((m 0 : ℤ) : ℝ) + m 1 + m 2) = a / 2 := by
      linear_combination h0
    have h2' : (a / 2) * (-((m 0 : ℤ) : ℝ) + m 1 + m 2) = (a / 2) * 1 := by
      rw [hS]
      ring
    exact mul_left_cancel₀ ha2 h2'
  have e1 : ((m 0 : ℤ) : ℝ) - m 1 + m 2 = 1 := by
    have hS : (a / 2) * (((m 0 : ℤ) : ℝ) - m 1 + m 2) = a / 2 := by
      linear_combination h1
    have h2' : (a / 2) * (((m 0 : ℤ) : ℝ) - m 1 + m 2) = (a / 2) * 1 := by
      rw [hS]
      ring
    exact mul_left_cancel₀ ha2 h2'
  have e2 : ((m 0 : ℤ) : ℝ) + m 1 - m 2 = 0 := by
    have hS : (a / 2) * (((m 0 : ℤ) : ℝ) + m 1 - m 2) = 0 := by
      linear_combination h2
    have h2' : (a / 2) * (((m 0 : ℤ) : ℝ) + m 1 - m 2) = (a / 2) * 0 := by
      rw [hS, mul_zero]
    exact mul_left_cancel₀ ha2 h2'
  have z0 : -m 0 + m 1 + m 2 = 1 := by
    have hc : (((-m 0 + m 1 + m 2 : ℤ)) : ℝ) = ((1 : ℤ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_neg, Int.cast_one]
      linarith [e0]
    exact Int.cast_injective hc
  have z1 : m 0 - m 1 + m 2 = 1 := by
    have hc : (((m 0 - m 1 + m 2 : ℤ)) : ℝ) = ((1 : ℤ) : ℝ) := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_one]
      linarith [e1]
    exact Int.cast_injective hc
  have z2 : m 0 + m 1 - m 2 = 0 := by
    have hc : (((m 0 + m 1 - m 2 : ℤ)) : ℝ) = ((0 : ℤ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_sub, Int.cast_zero]
      linarith [e2]
    exact Int.cast_injective hc
  omega

/-- Monoclinic P and C with the same parameters are different lattices (reference-only). -/
lemma lattice_ne_mP_mC (a b c β : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsin : Real.sin β ≠ 0) :
    (monoclinicP a b c β ha hb hc hsin).lattice
      ≠ (monoclinicC a b c β ha hb hc hsin).lattice := by
  intro heq
  have hmem : (monoclinicC a b c β ha hb hc hsin).primitiveVector 1
      ∈ (monoclinicP a b c β ha hb hc hsin).lattice := by
    rw [heq]
    exact primitiveVector_mem_lattice _ _
  obtain ⟨m, hm⟩ := ((monoclinicP a b c β ha hb hc hsin).mem_lattice_iff _).mp hmem
  have h2 := congrArg (fun x => x.ofLp 2) hm
  have h0 := congrArg (fun x => x.ofLp 0) hm
  simp [latticeVector_apply, primitiveVector, WithLp.ofLp_toLp, monoclinicP, monoclinicC,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col_apply] at h2 h0
  have hm2 : m 2 = 0 := by
    rcases h2 with (h | h)
    · rcases h with hc0 | hsin0
      · exact (hc.ne' hc0).elim
      · exact (hsin hsin0).elim
    · exact h
  rw [hm2] at h0
  simp only [Int.cast_zero, mul_zero, add_zero] at h0
  have h0' : a * ((m 0 : ℤ) : ℝ) = a / 2 := by linear_combination h0
  exact int_mul_ne_div_two a ha.ne' (m 0) h0'

end BravaisLattice

end Crystallography
