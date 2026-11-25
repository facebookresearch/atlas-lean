/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ProjSpace.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The structure morphism of projective space over a ring

For a commutative ring `R`, projective `n`-space over `R` is `Proj` of the polynomial ring
`R[X₀, …, Xₙ]` graded by total degree. This file defines its structure morphism
`ProjSpace.π R n` to `Spec R` and proves that it is proper.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The degree-zero part of `R[X₀, …, Xₙ]` is `R`, via constant polynomials. -/
def grad0Equiv : R ≃+* (𝒜 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [MvPolynomial.constantCoeff]
    · rw [MvPolynomial.coeff_C, ite_eq_right_iff.mpr (fun h => absurd h (Ne.symm hd))]
      by_contra h
      refine hd (Finsupp.ext fun i => ?_)
      have hdeg : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] at hdeg
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg i hi
      · exact Finsupp.notMem_support_iff.mp hi
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

@[simp] theorem grad0Equiv_apply_coe (r : R) : ((grad0Equiv R n r : 𝒜 0) :
    MvPolynomial (Fin (n + 1)) R) = C r := rfl

@[simp] theorem grad0Equiv_symm_apply (p : 𝒜 0) :
    (grad0Equiv R n).symm p = MvPolynomial.constantCoeff p.1 := rfl

/-- The structure morphism from projective `n`-space over `R` to `Spec R`. -/
def π : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)

theorem π_def : π R n =
    Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom) := rfl

instance finiteType_mvPolynomial :
    Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨C r, (mem_homogeneousSubmodule 0 _).mpr
      (isHomogeneous_C _ r)⟩ : 𝒜 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

instance isProper_π : IsProper (π R n) := by
  unfold π
  have : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have : IsIso (CommRingCat.ofHom (grad0Equiv R n).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (grad0Equiv R n).bijective
  have : IsIso (Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)) :=
    inferInstance
  infer_instance

end ProjSpace

end AlgebraicGeometry

end
