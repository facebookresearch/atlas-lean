/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LatticeTreeOrbital.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.Lattice

/-!
# Stabilizer of the standard lattice

`latticeMap_stdLattice_eq_iff_mem_range` identifies the matrices in `GL₂(K)` fixing the standard
lattice `R²` with the image of `GL₂(R)`, and `unitOfNeZero` is the unit of `K` given by a nonzero
element of `R`.
-/

@[expose] public section

noncomputable section

open Matrix

namespace LT.LatticeTree

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element `g ∈ GL₂(K)` fixes the standard lattice iff it comes from `GL₂(R)`. -/
theorem latticeMap_stdLattice_eq_iff_mem_range (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeMap g (stdLattice R K) = stdLattice R K ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinjM : Function.Injective
      ((algebraMap R K).mapMatrix : Matrix (Fin 2) (Fin 2) R →+* Matrix (Fin 2) (Fin 2) K) :=
    fun M N h => by
      ext i j
      apply hinj
      have := congrArg (fun X => X i j) h
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
  constructor
  · intro hfix
    have hcol : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single j 1) ∈ stdLattice R K :=
        hfix ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this
    have hfix' : latticeMap g⁻¹ (stdLattice R K) = stdLattice R K := by
      conv_lhs => rw [← hfix, latticeMap_inv_latticeMap]
    have hcol' : ∀ i j,
        IsLocalization.IsInteger R (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (Pi.single j 1) ∈ stdLattice R K :=
        hfix' ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this
    choose a ha using fun p : Fin 2 × Fin 2 => hcol p.1 p.2
    choose b hb using fun p : Fin 2 × Fin 2 => hcol' p.1 p.2
    set A : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => a (i, j) with hA
    set B : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => b (i, j) with hB
    have hmapA : (algebraMap R K).mapMatrix A = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact ha (i, j)
    have hmapB : (algebraMap R K).mapMatrix B =
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hb (i, j)
    have hAB : A * B = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBA : B * A = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    exact ha (i, j)
  · intro hg
    apply le_antisymm (latticeMap_le_stdLattice_of_isInteger
      (isInteger_apply_of_mem_range hg))
    have hg' : g⁻¹ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :=
      Subgroup.inv_mem _ hg
    have h1 : latticeMap g⁻¹ (stdLattice R K) ≤ stdLattice R K :=
      latticeMap_le_stdLattice_of_isInteger (isInteger_apply_of_mem_range hg')
    intro v hv
    have hv' : v ∈ latticeMap g (latticeMap g⁻¹ (stdLattice R K)) := by
      rw [latticeMap_latticeMap_inv]
      exact hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv'
    exact mulVec_mem_latticeMap (h1 hw)

/-- The unit of `K` given by a nonzero element of `R`. -/
def unitOfNeZero {ϖ : R} (hϖ : ϖ ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K ϖ)
    (fun h => hϖ (IsFractionRing.injective R K (by rw [h, map_zero])))

@[simp] theorem unitOfNeZero_coe {ϖ : R} (hϖ : ϖ ≠ 0) :
    ((unitOfNeZero (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

theorem isUnit_of_algebraMap_mul_eq_one {ϖ : R} {w : K}
    (hw : IsLocalization.IsInteger R w) (h : algebraMap R K ϖ * w = 1) : IsUnit ϖ := by
  obtain ⟨r, rfl⟩ := hw
  rw [← map_mul] at h
  have h1 : ϖ * r = 1 := IsFractionRing.injective R K (by rw [h, map_one])
  exact ⟨⟨ϖ, r, h1, (mul_comm r ϖ).trans h1⟩, rfl⟩

end LT.LatticeTree

end
