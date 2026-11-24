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

The product index is arbitrary. Native finite-free tensor coordinates and the
actual finite-free retraction of the tensor factor earn bijectivity of the
original product comparison. No finite product-index hypothesis is used.
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

/-- Interchange of the actual finite-free coordinate and original product index. -/
def finitePiFlip (n : ℕ) : (Fin n → ∀ i, N i) ≃ₗ[R] ∀ i, Fin n → N i where
  toFun x i j := x j i
  invFun x j i := x i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original arbitrary-product tensor comparison respects every actual
linear map in the tensor factor. -/
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

/-- Native finite-free coordinates compute the original product comparison;
the family and product index remain arbitrary. -/
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

/-- The actual finite-free projection/inclusion and original comparison squares
earn the finite-projective case through the shared elementary retract provider. -/
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

/-- The actual product Iso has the native original product comparison as its
forward map, even for infinite products. -/
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
