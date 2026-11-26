/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Projective
public import MathlibExt.LinearAlgebra.LinearMap.RetractComparison

/-!
# Tensoring arbitrary products with a finite-projective factor

Let R be a commutative ring, I an arbitrary index type and (N_i) an I-indexed family of
R-modules. For an R-module U, let Π_U:U⊗_R(∏i N_i)→∏i(U⊗_R N_i) send u⊗x to (i↦u⊗x_i). If U is
finitely generated projective over R, Π_U is an R-linear isomorphism. The index I and the
product factors N_i are unrestricted.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uI uN uU uV

variable (R : Type uR) [CommRing R] {ι : Type uI}
  (N : ι → Type uN) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

attribute [local ext high] TensorProduct.ext

/-- **Finite coordinate and arbitrary product interchange.**

Let R be a commutative ring, I any index type and N_i R-modules. For n∈ℕ, finitePiFlip n:(Fin
n→∏i N_i)≃ₗ[R]∏i(Fin n→N_i) sends x to i↦(j↦x(j)(i)).
-/
def finitePiFlip (n : ℕ) : (Fin n → ∀ i, N i) ≃ₗ[R] ∀ i, Fin n → N i where
  toFun x i j := x j i
  invFun x j i := x i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Naturality of the product comparison in the tensor factor.**

Let R be a commutative ring, I an arbitrary index type and (N_i) an I-indexed family of
R-modules. For an R-module U, let Π_U:U⊗_R(∏i N_i)→∏i(U⊗_R N_i) send u⊗x to (i↦u⊗x_i). For
R-modules U,V and an R-linear f:U→V, Π_V∘(f⊗id)=(∏i(f⊗id_(N_i)))∘Π_U.
-/
theorem piRightHom_factor_naturality
    {U : Type uU} {V : Type uV}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (f : U →ₗ[R] V) :
    (piRightHom R R V N).comp (f.rTensor (∀ i, N i)) =
      (LinearMap.piMap (fun i => f.rTensor (N i))).comp (piRightHom R R U N) := by
  apply TensorProduct.ext'
  intro u x
  funext i
  rfl

/-- **Product tensor comparison for a finite-free factor.**

Let R be a commutative ring, I an arbitrary index type and (N_i) an I-indexed family of
R-modules. For an R-module U, let Π_U:U⊗_R(∏i N_i)→∏i(U⊗_R N_i) send u⊗x to (i↦u⊗x_i). For n∈ℕ
and U=R^(Fin n), the map Π_U is bijective.
-/
theorem piRightHom_finiteFree_bijective (n : ℕ) :
    Function.Bijective (piRightHom R R (Fin n → R) N) := by
  let eD : (Fin n → R) ⊗[R] (∀ i, N i) ≃ₗ[R] (∀ i, Fin n → N i) :=
    TensorProduct.comm R _ _ ≪≫ₗ TensorProduct.piScalarRight R R (∀ i, N i) (Fin n) ≪≫ₗ
      finitePiFlip R N n
  let eC : (∀ i, (Fin n → R) ⊗[R] N i) ≃ₗ[R] (∀ i, Fin n → N i) :=
    LinearEquiv.piCongrRight (fun i => TensorProduct.comm R _ _ ≪≫ₗ
      TensorProduct.piScalarRight R R (N i) (Fin n))
  have he : eC.toLinearMap.comp (piRightHom R R (Fin n → R) N) = eD.toLinearMap := by
    apply TensorProduct.ext'
    intro u x
    funext i j
    change (TensorProduct.piScalarRight R R (N i) (Fin n) (x i ⊗ₜ[R] u)) j =
      (TensorProduct.piScalarRight R R (∀ i, N i) (Fin n) (x ⊗ₜ[R] u)) j i
    simp only [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, Pi.smul_apply]
  have hb : Function.Bijective (fun x => eC (piRightHom R R (Fin n → R) N x)) := by
    change Function.Bijective (eC.toLinearMap.comp (piRightHom R R (Fin n → R) N))
    rw [he]
    exact eD.bijective
  constructor
  · intro x y h
    exact hb.injective (congrArg eC h)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (eC y)
    exact ⟨x, eC.injective hx⟩

/-- **Product tensor comparison for a finite-projective factor.**

Let R be a commutative ring, I an arbitrary index type and (N_i) an I-indexed family of
R-modules. For an R-module U, let Π_U:U⊗_R(∏i N_i)→∏i(U⊗_R N_i) send u⊗x to (i↦u⊗x_i). If U is
finitely generated projective over R, Π_U is bijective.
-/
theorem piRightHom_finiteFactor_bijective
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    Function.Bijective (piRightHom R R U N) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R U
  let dF := f.rTensor (∀ i, N i)
  let dG := g.rTensor (∀ i, N i)
  let cF := LinearMap.piMap (fun i => f.rTensor (N i))
  let cG := LinearMap.piMap (fun i => g.rTensor (N i))
  have hd : dF.comp dG = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hfg, LinearMap.rTensor_id]
  have hc : cF.comp cG = LinearMap.id := by
    ext x i
    have h : (f.rTensor (N i)).comp (g.rTensor (N i)) = LinearMap.id := by
      rw [← LinearMap.rTensor_comp, hfg, LinearMap.rTensor_id]
    exact LinearMap.congr_fun h (x i)
  exact LinearMap.comparison_bijective_of_retract
    (piRightHom R R U N) (piRightHom R R (Fin n → R) N)
    dG dF cG cF hd hc (piRightHom_factor_naturality R N g)
      (piRightHom_factor_naturality R N f) (piRightHom_finiteFree_bijective R N n)

/-- **Finite-projective factor product tensor equivalence.**

Let R be a commutative ring, I an arbitrary index type and (N_i) an I-indexed family of
R-modules. For an R-module U, let Π_U:U⊗_R(∏i N_i)→∏i(U⊗_R N_i) send u⊗x to (i↦u⊗x_i). For U
finitely generated projective over R, piRightFiniteFactor R N U:U⊗_R(∏iN_i)≃ₗ[R]∏i(U⊗_RN_i)
has forward map Π_U.
-/
def piRightFiniteFactor
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    U ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, U ⊗[R] N i :=
  LinearEquiv.ofBijective (piRightHom R R U N) (piRightHom_finiteFactor_bijective R N U)

theorem piRightFiniteFactor_toLinearMap
    (U : Type uU) [AddCommGroup U] [Module R U]
    [Module.Finite R U] [Module.Projective R U] :
    (piRightFiniteFactor R N U).toLinearMap = piRightHom R R U N := rfl

end TensorProduct
