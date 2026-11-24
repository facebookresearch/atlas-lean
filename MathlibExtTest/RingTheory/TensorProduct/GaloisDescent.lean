/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.TensorProduct.GaloisDescent

@[expose] public section

open scoped TensorProduct

universe u v

-- Consumer with the original binders.
example
    (𝒪 : Type u) [CommRing 𝒪] (𝒪' : Type u) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    [Module.Flat 𝒪 𝒪']
    (G : Type v) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪')
          ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (A : Type u) [CommRing A] [Algebra 𝒪' A] [Algebra 𝒪 A] [IsScalarTower 𝒪 𝒪' A]
    (θ : G → (A ≃+* A)) (hθ1 : θ 1 = RingEquiv.refl A)
    (hθmul : ∀ σ σ' : G, θ (σ * σ') = (θ σ').trans (θ σ))
    (hθτ : ∀ (σ : G) (l : 𝒪') (a : A),
      θ σ (algebraMap 𝒪' A l * a) = algebraMap 𝒪' A (τ σ l) * θ σ a)
    (C : Type u) [CommRing C] [Algebra 𝒪 C] (ι : C →ₐ[𝒪] A)
    (hι : Function.Injective ι)
    (hιG : ∀ a : A, (∀ σ : G, θ σ a = a) ↔ a ∈ Set.range ι) :
    Function.Bijective (Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A)
      (IsScalarTower.toAlgHom 𝒪 𝒪' A)
      (fun c l => Commute.all _ _) : C ⊗[𝒪] 𝒪' →ₐ[𝒪] A) :=
  Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois
    𝒪 𝒪' G τ hgal A θ hθ1 hθmul hθτ C ι hι hιG

-- Higher-universe consumer: all rings in `Type 1`, the group in `Type 1`.
example
    (𝒪 : Type 1) [CommRing 𝒪] (𝒪' : Type 1) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    [Module.Flat 𝒪 𝒪']
    (G : Type 1) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪')
          ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (A : Type 1) [CommRing A] [Algebra 𝒪' A] [Algebra 𝒪 A] [IsScalarTower 𝒪 𝒪' A]
    (θ : G → (A ≃+* A)) (hθ1 : θ 1 = RingEquiv.refl A)
    (hθmul : ∀ σ σ' : G, θ (σ * σ') = (θ σ').trans (θ σ))
    (hθτ : ∀ (σ : G) (l : 𝒪') (a : A),
      θ σ (algebraMap 𝒪' A l * a) = algebraMap 𝒪' A (τ σ l) * θ σ a)
    (C : Type 1) [CommRing C] [Algebra 𝒪 C] (ι : C →ₐ[𝒪] A)
    (hι : Function.Injective ι)
    (hιG : ∀ a : A, (∀ σ : G, θ σ a = a) ↔ a ∈ Set.range ι) :
    Function.Bijective (Algebra.TensorProduct.lift (ι : C →ₐ[𝒪] A)
      (IsScalarTower.toAlgHom 𝒪 𝒪' A)
      (fun c l => Commute.all _ _) : C ⊗[𝒪] 𝒪' →ₐ[𝒪] A) :=
  Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois
    𝒪 𝒪' G τ hgal A θ hθ1 hθmul hθτ C ι hι hιG
