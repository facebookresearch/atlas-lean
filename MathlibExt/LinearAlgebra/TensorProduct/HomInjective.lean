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

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Faithfulness of the algebraic tensor action on linear maps

The canonical tensor evaluation maps are injective over a field. Coordinates
in a basis of the vector factor detect every coefficient linear map. Applying
this twice proves faithfulness of the tensor action on two spaces, without
finite-dimension assumptions.

This injectivity supplies the algebraic faithfulness needed by tensor
representations and completion maps.
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uM uN uP uM₂ uN₂

variable {R : Type uR} [Field R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {P : Type uP} [AddCommGroup P] [Module R P]

/-- Tensoring vectors with linear maps gives a faithful pointwise tensor action. -/
theorem lTensorHomToHomLTensor_injective :
    Function.Injective (lTensorHomToHomLTensor (RingHom.id R) P M N) := by
  classical
  let b := Module.Basis.ofVectorSpace R M
  have hcoord (z : M ⊗[R] (P →ₗ[R] N)) (i : Module.Basis.ofVectorSpaceIndex R M) (p : P) :
      (equivFinsuppOfBasisLeft (N := P →ₗ[R] N) b z i) p =
        equivFinsuppOfBasisLeft (N := N) b
          (lTensorHomToHomLTensor (RingHom.id R) P M N z p) i := by
    induction z using TensorProduct.inductionOn with
    | tmul m f =>
      simp only [equivFinsuppOfBasisLeft_apply_tmul_apply,
        lTensorHomToHomLTensor_apply, LinearMap.smul_apply]
    | add z w hz hw =>
      simp only [map_add, Finsupp.add_apply, LinearMap.add_apply, hz, hw]
  intro z w h
  apply (equivFinsuppOfBasisLeft (N := P →ₗ[R] N) b).injective
  apply Finsupp.ext
  intro i
  apply LinearMap.ext
  intro p
  have hc := congrArg
    (fun f : P →ₗ[R] M ⊗[R] N => equivFinsuppOfBasisLeft (N := N) b (f p) i) h
  rw [← hcoord z i p, ← hcoord w i p] at hc
  exact hc

/-- Tensoring linear maps with vectors also gives a faithful tensor action. -/
theorem rTensorHomToHomRTensor_injective :
    Function.Injective (rTensorHomToHomRTensor (RingHom.id R) P M N) := by
  have hflip (z : (P →ₗ[R] M) ⊗[R] N) (p : P) :
      TensorProduct.comm R N M
        (lTensorHomToHomLTensor (RingHom.id R) P N M
          (TensorProduct.comm R (P →ₗ[R] M) N z) p) =
        rTensorHomToHomRTensor (RingHom.id R) P M N z p := by
    induction z using TensorProduct.inductionOn with
    | tmul f n =>
      simp only [comm_tmul, lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply]
    | add z w hz hw =>
      simp only [map_add, LinearMap.add_apply, hz, hw]
  intro z w h
  apply (TensorProduct.comm R (P →ₗ[R] M) N).injective
  apply lTensorHomToHomLTensor_injective
  apply LinearMap.ext
  intro p
  apply (TensorProduct.comm R N M).injective
  rw [hflip, hflip]
  exact DFunLike.congr_fun h p

variable {M₂ : Type uM₂} [AddCommGroup M₂] [Module R M₂]
variable {N₂ : Type uN₂} [AddCommGroup N₂] [Module R N₂]

/-- The tensor product of two linear maps acts faithfully on the algebraic tensor of their inputs. -/
theorem homTensorHomMap_injective :
    Function.Injective (homTensorHomMap (RingHom.id R) M N M₂ N₂) := by
  have heval (z : (M →ₗ[R] M₂) ⊗[R] (N →ₗ[R] N₂)) (m : M) (n : N) :
      homTensorHomMap (RingHom.id R) M N M₂ N₂ z (m ⊗ₜ[R] n) =
        lTensorHomToHomLTensor (RingHom.id R) N M₂ N₂
          (rTensorHomToHomRTensor (RingHom.id R) M M₂ (N →ₗ[R] N₂) z m) n := by
    induction z using TensorProduct.inductionOn with
    | tmul f g =>
      simp only [homTensorHomMap_apply, map_tmul,
        rTensorHomToHomRTensor_apply, lTensorHomToHomLTensor_apply]
    | add z w hz hw =>
      simp only [map_add, LinearMap.add_apply, hz, hw]
  intro z w h
  apply rTensorHomToHomRTensor_injective
  apply LinearMap.ext
  intro m
  apply lTensorHomToHomLTensor_injective
  apply LinearMap.ext
  intro n
  have he := DFunLike.congr_fun h (m ⊗ₜ[R] n)
  rw [heval, heval] at he
  exact he

end TensorProduct
