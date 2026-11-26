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
# Injectivity of tensor evaluation maps over a field

Let R be a field and M,N,P arbitrary R-vector spaces, with independent scalar and carrier
universes. The tensor evaluation maps M⊗Hom_R(P,N)→Hom_R(P,M⊗N) and Hom_R(P,M)⊗N→Hom_R(P,M⊗N)
are injective. Their pure tensors act by p↦m⊗f(p) and p↦f(p)⊗n, respectively.

For vector spaces M,N,M₂,N₂, the canonical action Hom_R(M,M₂)⊗Hom_R(N,N₂)→Hom_R(M⊗N,M₂⊗N₂) is
also injective, sending f⊗g to m⊗n↦f(m)⊗g(n). Basis coordinates in the vector factors detect the
coefficient maps; no finite-dimensionality assumption is needed.
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

/-- Let R be a field and M,N,P R-vector spaces in independent universes. The canonical map
M⊗_RHom_R(P,N)→Hom_R(P,M⊗_R N), taking m⊗f to p↦m⊗f(p), is injective. The dimensions of all
three vector spaces may be arbitrary. -/
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

/-- Let R be a field and P,M,N R-vector spaces in independent universes. The canonical map
Hom_R(P,M)⊗_R N→Hom_R(P,M⊗_R N), taking f⊗n to p↦f(p)⊗n, is injective. The result uses tensor
interchange and vector-first evaluation injectivity. -/
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

/-- Let R be a field and M,N,M₂,N₂ R-vector spaces with independent carrier universes. The canonical
map Hom_R(M,M₂)⊗_RHom_R(N,N₂)→Hom_R(M⊗_R N,M₂⊗_R N₂) is injective. Its pure-tensor action is
(f⊗g)(m⊗n)=f(m)⊗g(n), with no finite-dimensionality assumption. -/
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
