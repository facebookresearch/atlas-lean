/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Restriction of a linear endomorphism action

An algebra homomorphism into linear endomorphisms induces an action
whose scalar restriction is the original module action. These proofs
apply to the actual character-Chern polynomial action as well as any
other algebra of linear operators.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.EndScalarRestriction

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (ρ : A →ₐ[R] Module.End R M)

/-- The action is the native restriction of the tautological endomorphism action. -/
@[instance_reducible] def module : Module A M := Module.compHom M ρ.toRingHom

/-- Its scalar restriction is exactly the original module action. -/
theorem scalarTower : letI := module ρ; IsScalarTower R A M := by
  let _ := module ρ
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change ρ (algebraMap R A r) m = r • m
  rw [ρ.commutes]
  rfl

/-- The induced operators commute with the original scalar multiplication. -/
theorem scalarComm : letI := module ρ; SMulCommClass R A M := by
  let _ := module ρ
  exact ⟨fun r a m => (ρ a).map_smul r m |>.symm⟩

open scoped TensorProduct

variable {B N : Type*} [CommSemiring B] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B] [SMulCommClass A R B]
  [AddCommMonoid N] [Module R N]

/-- An intertwiner is linear for the two actual restricted endomorphism actions. -/
def intertwiningMap (σ : A →ₐ[R] Module.End R N) (f : M →ₗ[R] N)
    (h : ∀ (a : A) (m : M), f (ρ a m) = σ a (f m)) :
    letI := module ρ
    letI := module σ
    M →ₗ[A] N := by
  let _ := module ρ
  let _ := module σ
  exact { toFun := f, map_add' := f.map_add, map_smul' := h }

/-- Extend a scalar-linear map along the prescribed algebra of endomorphisms. -/
def tensorExtension (ρ : A →ₐ[R] Module.End R N) (f : M →ₗ[R] N) :
    B ⊗[R] M →ₗ[R] (letI := module ρ; B ⊗[A] N) := by
  let _ := module ρ
  let _ := scalarTower ρ
  let _ := scalarComm ρ
  exact TensorProduct.lift {
    toFun := fun b => {
      toFun := fun m => b ⊗ₜ[A] f m
      map_add' := by intro m m'; rw [f.map_add, TensorProduct.tmul_add]
      map_smul' := by intro r m; rw [f.map_smul, TensorProduct.tmul_smul]; rfl }
    map_add' := by intro b b'; ext m; exact TensorProduct.add_tmul b b' (f m)
    map_smul' := by intro r b; ext m; exact (TensorProduct.smul_tmul' r b (f m)).symm }

end MathlibExt.EndScalarRestriction
