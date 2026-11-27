/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_LatticeTreeOrbital.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeOrbital
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Basic.Complex.Basic

@[expose] public section

open scoped Matrix
open LT.LatticeTree

universe u

/-- `i ≠ -i` in `ℂ`. -/
private theorem complex_I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have h2 : Complex.I.im = (-Complex.I).im := congrArg Complex.im h
  rw [Complex.neg_im, Complex.I_im] at h2
  norm_num at h2

/-- Complex conjugation, as an integral automorphism of `ℂ` over itself. -/
private noncomputable def conjAut : IntegralAut ℂ ℂ where
  toField := starRingAut
  toBase := starRingAut
  commutes r := by
    simp [Algebra.algebraMap_self]

/-- Complex conjugation has order two. -/
private theorem conjAut_comp_conjAut : conjAut.comp conjAut = IntegralAut.refl ℂ ℂ := by
  unfold conjAut IntegralAut.comp IntegralAut.refl
  congr 1 <;>
  · ext x
    exact star_star x

/-- Consumer with the original binders: the fixed-vertex count is a conjugacy invariant. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (h * g * h⁻¹) = unitOrbitalCount R g :=
  unitOrbitalCount_conj g h

/-- Higher-universe consumer: if `σ³ = id`, twisted fixed vertices are fixed by `normThree δ σ`.
-/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K) :
    twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) (normThree δ σ) :=
  twistedFixedVertexSet_subset_fixedVertexSet_normThree δ hσ

private noncomputable def gammaZero : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

@[simp] private theorem gammaZero_coe :
    (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![0, -1; 1, -1] :=
  IsUnit.unit_spec _

private noncomputable def transvectionGate : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

@[simp] private theorem transvectionGate_coe :
    (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![1, 1; 0, 1] :=
  IsUnit.unit_spec _

private theorem not_two_dvd_one_padic : ¬ ((2 : ℤ_[2]) ∣ 1) := fun h =>
  (PadicInt.irreducible_p (p := 2)).not_isUnit (isUnit_of_dvd_one h)

example : IsFixedVertex
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
    (stdVertex ℤ_[2] ℚ_[2]) :=
  isFixedVertex_stdVertex_of_mem_range ⟨gammaZero, rfl⟩

example : ¬ IsFixedVertex
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
    (Vertex.mk ℤ_[2] ℚ_[2] (interLattice ℤ_[2] ℚ_[2] 2 1 0)
      (isFullLattice_interLattice PadicInt.irreducible_p 1 0)) := by
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 0 = 0 := by
    simp
  have hv1 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 1 = 1 := by
    simp
  refine not_isFixedVertex_interLattice_of_not_dvd gammaZero PadicInt.prime_p
    (fun h => not_two_dvd_one_padic h.1) ?_
  rw [hv0, hv1]
  intro hcon
  apply not_two_dvd_one_padic
  apply dvd_neg.mp
  have hval : (0 : ℤ_[2]) * 0 - 1 * 1 = -1 := by ring
  rwa [hval] at hcon

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (interLattice ℤ_[2] ℚ_[2] 2 0 1) ≠ interLattice ℤ_[2] ℚ_[2] 2 0 1 := by
  intro h
  have hd := dvd_of_latticeMap_map_interLattice_eq_self gammaZero h
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 0 = -1 := by
    simp
  have hval : (1 : ℤ_[2]) * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 0 -
      0 * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 1 = -1 := by
    rw [hv0]; ring
  rw [hval] at hd
  exact not_two_dvd_one_padic (dvd_neg.mp hd)

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (interLattice ℤ_[2] ℚ_[2] 2 1 1) ≠ interLattice ℤ_[2] ℚ_[2] 2 1 1 := by
  intro h
  have hd := dvd_of_latticeMap_map_interLattice_eq_self gammaZero h
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 0 = -1 := by
    simp
  have hv1 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 1 = 0 := by
    simp
  have hval : (1 : ℤ_[2]) * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 0 -
      1 * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 1 = -1 := by
    rw [hv0, hv1]; ring
  rw [hval] at hd
  exact not_two_dvd_one_padic (dvd_neg.mp hd)

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) transvectionGate)
        (interLattice ℤ_[2] ℚ_[2] 2 1 0) = interLattice ℤ_[2] ℚ_[2] 2 1 0 := by
  refine latticeMap_map_interLattice_eq_self transvectionGate 1 ?_ ?_
  · have hv : mulVecPair (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 0 = 1 := by
      simp
    rw [hv]
    simp
  · have hv : mulVecPair (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 1 = 0 := by
      simp
    rw [hv]
    simp

example : ¬ (fixedVertexSet (R := ℤ_[2])
    (scalarGL (Units.mk0 (2 : ℚ_[2]) (by norm_num)))).Subsingleton :=
  not_subsingleton_fixedVertexSet_scalarGL PadicInt.irreducible_p _

example :
    twistedUnitOrbitalCount
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (IntegralAut.refl ℤ_[2] ℚ_[2]) =
      unitOrbitalCount ℤ_[2]
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero) :=
  twistedUnitOrbitalCount_refl _

example :
    IsTwistedFixedVertex
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
      (IntegralAut.refl ℤ_[2] ℚ_[2]) (stdVertex ℤ_[2] ℚ_[2]) :=
  isTwistedFixedVertex_stdVertex_of_mem_range ⟨gammaZero, rfl⟩ _

example : ¬ (twistedFixedVertexSet (R := ℤ_[2])
    (scalarGL (Units.mk0 (2 : ℚ_[2]) (by norm_num)))
    (IntegralAut.refl ℤ_[2] ℚ_[2])).Subsingleton := by
  rw [twistedFixedVertexSet_refl]
  exact not_subsingleton_fixedVertexSet_scalarGL PadicInt.irreducible_p _

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2]) (c d : ℤ_[2]) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) δ)
        (IntegralAut.refl ℤ_[2] ℚ_[2]) (interLattice ℤ_[2] ℚ_[2] 2 c d) =
      interLattice ℤ_[2] ℚ_[2] 2
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) ℤ_[2]) c d 0)
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) ℤ_[2]) c d 1) :=
  twistedLatticeMap_map_interLattice δ (IntegralAut.refl ℤ_[2] ℚ_[2]) rfl c d

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℂ) (v : Vertex ℂ ℂ)
    (hv : IsTwistedFixedVertex δ conjAut v) : IsFixedVertex (normTwo δ conjAut) v :=
  isFixedVertex_normTwo_of_isTwistedFixedVertex δ conjAut_comp_conjAut hv

example :
    latticeGal conjAut (interLattice ℂ ℂ 0 1 Complex.I) =
      interLattice ℂ ℂ (conjAut.toBase 0) (conjAut.toBase 1)
        (conjAut.toBase Complex.I) :=
  latticeGal_interLattice conjAut 0 1 Complex.I

example :
    latticeGal conjAut (interLattice ℂ ℂ 0 1 Complex.I) ≠
      interLattice ℂ ℂ 0 1 Complex.I := by
  rw [latticeGal_interLattice,
    show conjAut.toBase (0 : ℂ) = 0 from map_zero _,
    show conjAut.toBase (1 : ℂ) = 1 from map_one _,
    show conjAut.toBase Complex.I = -Complex.I from Complex.conj_I]
  intro h
  have hd := dvd_of_interLattice_eq h
  rw [zero_dvd_iff] at hd
  apply complex_I_ne_neg_I
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination hd
  have hI : Complex.I = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  rw [hI, neg_zero]
