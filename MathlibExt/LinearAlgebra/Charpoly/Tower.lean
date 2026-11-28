/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Charpoly.DependentPi

/-!
# Left-multiplication characteristic polynomial in a finite tower

Let k,F be fields with a finite extension k→F and E a ring with compatible k- and F-algebra
structures, finite-dimensional over both. For θ∈F, χ_k(L_(image θ) on E)=χ_k(L_θ on F)^[dim_F
E]. E may be noncommutative and need not be a field.
-/

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Algebra

section Tower

variable {k F E : Type*} [Field k] [Field F] [Ring E]
  [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional k F] [FiniteDimensional F E] [FiniteDimensional k E]

/-- **Characteristic polynomial of an intermediate-field scalar.**

Let k,F be fields, E a ring with compatible algebra tower k→F→E, and all k/F, F/E and k/E
module dimensions finite. For θ∈F, (Algebra.lmul k E (algebraMap F E
θ)).charpoly=(Algebra.lmul k F θ).charpoly^(finrank_F E).
-/
theorem lmul_charpoly_algebraMap_tower (θ₀ : F) :
    (Algebra.lmul k E (algebraMap F E θ₀)).charpoly =
      (Algebra.lmul k F θ₀).charpoly ^ Module.finrank F E := by
  classical
  let n := Module.finrank F E
  let b : Module.Basis (Fin n) F E := Module.finBasis F E
  let e : E ≃ₗ[k] (Fin n → F) := b.equivFun.restrictScalars k
  have he : ∀ x i, e x i = b.repr x i := fun x i =>
    congrFun (Module.Basis.equivFun_apply b x) i
  have hconj : e.conj (Algebra.lmul k E (algebraMap F E θ₀)) =
      LinearMap.pi
        (fun i => (Algebra.lmul k F θ₀).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    funext i
    simp only [LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply, LinearMap.pi_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, he]
    have hmul : (Algebra.lmul k E (algebraMap F E θ₀)) x = θ₀ • x := by
      simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
        Algebra.smul_def]
    rw [hmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  calc
    (Algebra.lmul k E (algebraMap F E θ₀)).charpoly =
        (e.conj (Algebra.lmul k E (algebraMap F E θ₀))).charpoly :=
      (LinearEquiv.charpoly_conj e _).symm
    _ = ∏ _i : Fin n, (Algebra.lmul k F θ₀).charpoly := by
      rw [hconj, LinearMap.charpoly_pi_dependent]
    _ = (Algebra.lmul k F θ₀).charpoly ^ n := by simp
    _ = (Algebra.lmul k F θ₀).charpoly ^ Module.finrank F E := rfl

end Tower

end Algebra
