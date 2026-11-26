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
# Injectivity of algebraic tensor evaluation on linear maps

Let K be a field and all modules vector spaces in independent universes. The maps
P⊗Hom(M,N)→Hom(M,P⊗N), Hom(P,M)⊗N→Hom(P,M⊗N), and Hom(M,M₂)⊗Hom(N,N₂)→Hom(M⊗N,M₂⊗N₂) are
injective, with the usual pure-tensor evaluations.
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

/-- **Faithfulness of vector-first tensor evaluation.**

Let K be a field and P,M,N K-vector spaces. The linear map P⊗_KHom_K(M,N)→Hom_K(M,P⊗_KN),
sending p⊗f to x↦p⊗f(x), is injective, even without finite-dimensionality.
-/
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

/-- **Faithfulness of map-first tensor evaluation.**

Let K be a field and P,M,N K-vector spaces. The linear map Hom_K(P,M)⊗_KN→Hom_K(P,M⊗_KN),
f⊗n↦(p↦f(p)⊗n), is injective.
-/
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

/-- **Faithfulness of the tensor product action of two linear-map spaces.**

Let K be a field and M,N,M₂,N₂ K-vector spaces. The map
Hom(M,M₂)⊗_KHom(N,N₂)→Hom(M⊗_KN,M₂⊗_KN₂), f⊗g↦(x⊗y↦f(x)⊗g(y)), is injective.
-/
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
