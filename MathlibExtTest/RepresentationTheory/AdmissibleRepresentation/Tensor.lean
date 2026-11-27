/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Tensor

/-! Tests for tensor products of admissible representations: the product
`(S ⊗_F V) × (S ⊗_F W) → S ⊗_F (V ⊗_F W)` on pure tensors, its bilinearity and its equivariance,
products of fixed vectors, Fontaine's natural map `D_S(V) ⊗_{S^H} D_S(W) → D_S(V ⊗_F W)` on pure
tensors, and, for the trivial representations with the fixed bases `1 ⊗ vᵢ` and `1 ⊗ wⱼ`, the basis
form of admissibility of the tensor product, its consequences, and the bijectivity of the natural
map; and, for a regular ring, the tensor product of admissible representations. -/

open scoped TensorProduct

open Representation

variable {F G S V W : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V] [AddCommGroup W] [Module F W]

-- The product on pure tensors, and as the curried inverse of `distribBaseChange`.
example (a b : S) (v : V) (w : W) :
    tensorMul F S V W (a ⊗ₜ v) (b ⊗ₜ w) = (a * b) ⊗ₜ (v ⊗ₜ w) := by
  simp

example (v : V) (w : W) : tensorMul F S V W (1 ⊗ₜ v) (1 ⊗ₜ w) = (1 : S) ⊗ₜ[F] (v ⊗ₜ[F] w) := by
  simp

example (x : S ⊗[F] V) (y : S ⊗[F] W) :
    tensorMul F S V W x y =
      (TensorProduct.AlgebraTensorModule.distribBaseChange F S V W).symm (x ⊗ₜ y) :=
  tensorMul_apply x y

-- The product is `S`-bilinear.
example (s : S) (x : S ⊗[F] V) (y : S ⊗[F] W) :
    tensorMul F S V W (s • x) y = s • tensorMul F S V W x y ∧
      tensorMul F S V W x (s • y) = s • tensorMul F S V W x y := by
  simp

example (s a b : S) (v : V) (w : W) :
    tensorMul F S V W (a ⊗ₜ v) (s • b ⊗ₜ w) = (s * a * b) ⊗ₜ (v ⊗ₜ w) := by
  rw [map_smul, tensorMul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]

-- The product is equivariant for the diagonal actions.
example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S) (g : G)
    (x : S ⊗[F] V) (y : S ⊗[F] W) :
    TensorProduct.map (act g).toLinearMap (ρ.tprod σ g) (tensorMul F S V W x y) =
      tensorMul F S V W (TensorProduct.map (act g).toLinearMap (ρ g) x)
        (TensorProduct.map (act g).toLinearMap (σ g) y) :=
  map_tensorMul ρ σ act g x y

example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S) (g : G)
    (a b : S) (v : V) (w : W) :
    TensorProduct.map (act g).toLinearMap (ρ.tprod σ g) (tensorMul F S V W (a ⊗ₜ v) (b ⊗ₜ w)) =
      (act g a * act g b) ⊗ₜ (ρ g v ⊗ₜ σ g w) := by
  rw [map_tensorMul, TensorProduct.map_tmul, TensorProduct.map_tmul, tensorMul_tmul,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]

-- The product of fixed vectors is fixed: `1 ⊗ (v ⊗ w)` for vectors `v`, `w` fixed by `H`.
example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S)
    (H : Subgroup G) {v : V} (hv : ∀ g ∈ H, ρ g v = v) {w : W} (hw : ∀ g ∈ H, σ g w = w) :
    (1 : S) ⊗ₜ[F] (v ⊗ₜ[F] w) ∈ (ρ.tprod σ).periods act H := by
  have h := tensorMul_mem_periods (ρ := ρ) (σ := σ) (act := act) (H := H) (x := 1 ⊗ₜ v)
    (mem_periods.2 fun g hg => by
      rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, hv g hg])
    (y := 1 ⊗ₜ w)
    (mem_periods.2 fun g hg => by
      rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, hw g hg])
  rwa [tensorMul_tmul, mul_one] at h

-- Fontaine's natural map sends `x ⊗ y` to the product of `x` and `y`.
example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S)
    (H : Subgroup G) (x : ρ.periods act H) (y : σ.periods act H) :
    (periodsTensor ρ σ act H (x ⊗ₜ y) : S ⊗[F] (V ⊗[F] W)) = tensorMul F S V W x y := by
  simp

example (ρ : Representation F G V) (σ : Representation F G W) (act : G → S →ₐ[F] S)
    (H : Subgroup G) {v : V} (hv : (1 : S) ⊗ₜ[F] v ∈ ρ.periods act H) {w : W}
    (hw : (1 : S) ⊗ₜ[F] w ∈ σ.periods act H) :
    (periodsTensor ρ σ act H (⟨_, hv⟩ ⊗ₜ ⟨_, hw⟩) : S ⊗[F] (V ⊗[F] W)) = 1 ⊗ₜ (v ⊗ₜ w) := by
  simp

-- The tensor product of two trivial representations is admissible in the basis form, for every
-- action on `S`, with the fixed bases `1 ⊗ vᵢ` and `1 ⊗ wⱼ`.
example [FiniteDimensional F V] [FiniteDimensional F W] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    ((trivial F G V).tprod (trivial F G W)).HasFixedBasis act H :=
  HasFixedBasis.tprod
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F W), fun j g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

-- Hence it is admissible in the dimension form when `S` is nontrivial, and its comparison map is
-- an isomorphism.
example [Nontrivial S] [FiniteDimensional F V] [FiniteDimensional F W] (act : G → S →ₐ[F] S)
    (H : Subgroup G) : ((trivial F G V).tprod (trivial F G W)).IsAdmissible act H :=
  (HasFixedBasis.tprod
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F W), fun j g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩).isAdmissible

example {ρ : Representation F G V} {σ : Representation F G W} {act : G → S →ₐ[F] S}
    {H : Subgroup G} (hρ : ρ.HasFixedBasis act H) (hσ : σ.HasFixedBasis act H) :
    Function.Bijective ((ρ.tprod σ).comparison act H) :=
  (hρ.tprod hσ).comparison_bijective

-- For the trivial representations, Fontaine's natural map is bijective.
example [FiniteDimensional F V] [FiniteDimensional F W] (act : G → S →ₐ[F] S) (H : Subgroup G) :
    Function.Bijective (periodsTensor (trivial F G V) (trivial F G W) act H) :=
  HasFixedBasis.periodsTensor_bijective
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F V), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩
    ⟨_, Algebra.TensorProduct.basis S (Module.finBasis F W), fun j g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        map_one, trivial_apply]⟩

-- The isomorphism `periodsTensorEquiv` is the natural map, and sends `x ⊗ y` to `x · y`.
example {ρ : Representation F G V} {σ : Representation F G W} {act : G → S →ₐ[F] S}
    {H : Subgroup G} (hρ : ρ.HasFixedBasis act H) (hσ : σ.HasFixedBasis act H)
    (x : ρ.periods act H) (y : σ.periods act H) :
    (hρ.periodsTensorEquiv hσ (x ⊗ₜ y) : S ⊗[F] (V ⊗[F] W)) = tensorMul F S V W x y := by
  simp

example {ρ : Representation F G V} {σ : Representation F G W} {act : G → S →ₐ[F] S}
    {H : Subgroup G} (hρ : ρ.HasFixedBasis act H) (hσ : σ.HasFixedBasis act H)
    (z : (ρ.tprod σ).periods act H) :
    periodsTensor ρ σ act H ((hρ.periodsTensorEquiv hσ).symm z) = z := by
  rw [← HasFixedBasis.periodsTensorEquiv_apply hρ hσ, LinearEquiv.apply_symm_apply]

-- The trivial representation of `G` on `F`, for the trivial family `act g = id` on `S = F`: the
-- natural map `D_F(F) ⊗_F D_F(F) → D_F(F ⊗_F F)` is an isomorphism.
example (H : Subgroup G) :
    Function.Bijective
      (periodsTensor (trivial F G F) (trivial F G F) (fun _ => AlgHom.id F F) H) :=
  HasFixedBasis.periodsTensor_bijective
    ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, trivial_apply]⟩
    ⟨1, Algebra.TensorProduct.basis F (Module.Basis.singleton (Fin 1) F), fun i g _ => by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.id_apply, trivial_apply]⟩

-- For a regular ring, tensor products of admissible representations are admissible, and
-- Fontaine's natural map is an isomorphism; for instance for a field with any action.
example [IsDomain S] {act : G →* (S →ₐ[F] S)} {H : Subgroup G}
    (hS : IsRegularPeriodRing act H) {ρ : Representation F G V} {σ : Representation F G W}
    (hρ : ρ.IsAdmissible act H) (hσ : σ.IsAdmissible act H) :
    (ρ.tprod σ).IsAdmissible act H ∧ Function.Bijective (periodsTensor ρ σ act H) :=
  ⟨hS.isAdmissible_tprod hρ hσ, hS.periodsTensor_bijective hρ hσ⟩

example {L : Type*} [Field L] [Algebra F L] (act : G →* (L →ₐ[F] L)) (H : Subgroup G)
    {ρ : Representation F G V} (hρ : ρ.IsAdmissible act H) :
    (ρ.tprod ρ).IsAdmissible act H :=
  (isRegularPeriodRing_of_isField (Field.toIsField L) act H).isAdmissible_tprod hρ hρ
