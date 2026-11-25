/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.TensorProduct.ZModRestrict
public import MathlibExt.RepresentationTheory.Rep.ZModRestrict

/-!
# Tensor compatibility for restriction from `ZMod n` to `ℤ`

For representations whose carriers lie in the scalar universe, the canonical
comparison `M ⊗[ℤ] N ≃ M ⊗[ZMod n] N` is equivariant.  It therefore
identifies the tensor product of the scalar-restricted representations with
the scalar restriction of their tensor product.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace Rep

variable {G : Type u} [Group G]

/-- Equivariant tensor comparison for scalar restriction from `ZMod n` to
`ℤ`. -/
noncomputable def zmodRestrictIntTensorRepresentationEquiv
    (n : ℕ) (A B : Rep.{0} (ZMod n) G) :
    (zmodRestrictInt n A ⊗ zmodRestrictInt n B).ρ.Equiv
      (zmodRestrictInt n (A ⊗ B)).ρ :=
  Representation.Equiv.mk
    (TensorProduct.zmodRestrictIntEquiv n A B) (fun g => by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          let xA : A := x
          let yB : B := y
          change TensorProduct.zmodRestrictIntEquiv n A B
              (A.ρ g xA ⊗ₜ[ℤ] B.ρ g yB) =
            (A ⊗ B).ρ g
              (TensorProduct.zmodRestrictIntEquiv n A B
                (xA ⊗ₜ[ℤ] yB))
          rw [TensorProduct.zmodRestrictIntEquiv_apply_tmul,
            TensorProduct.zmodRestrictIntEquiv_apply_tmul]
          change A.ρ g x ⊗ₜ[ZMod n] B.ρ g y =
            TensorProduct.map (A.ρ g) (B.ρ g)
              (x ⊗ₜ[ZMod n] y)
          exact (TensorProduct.map_tmul (A.ρ g) (B.ρ g) xA yB).symm
      | add x y hx hy =>
          simp only [map_add]
          rw [hx, hy])

/-- Tensor product of restricted representations is canonically isomorphic
to the restriction of the tensor product. -/
noncomputable def zmodRestrictIntTensorIso
    (n : ℕ) (A B : Rep.{0} (ZMod n) G) :
    zmodRestrictInt n A ⊗ zmodRestrictInt n B ≅
      zmodRestrictInt n (A ⊗ B) :=
  Rep.mkIso (zmodRestrictIntTensorRepresentationEquiv n A B)

@[simp]
theorem zmodRestrictIntTensorIso_hom_tmul
    (n : ℕ) (A B : Rep.{0} (ZMod n) G) (x : A) (y : B) :
    @DFunLike.coe
      (((zmodRestrictInt n A).ρ.tprod (zmodRestrictInt n B).ρ).IntertwiningMap
        (zmodRestrictInt n (A ⊗ B)).ρ)
      (TensorProduct ℤ (zmodRestrictInt n A) (zmodRestrictInt n B))
      (fun _ => (zmodRestrictInt n (A ⊗ B) : Type))
      (Representation.IntertwiningMap.instFunLike
        ((zmodRestrictInt n A).ρ.tprod (zmodRestrictInt n B).ρ)
        (zmodRestrictInt n (A ⊗ B)).ρ)
      (ConcreteCategory.hom (zmodRestrictIntTensorIso n A B).hom) (x ⊗ₜ[ℤ] y) =
      x ⊗ₜ[ZMod n] y :=
  rfl

@[simp]
theorem zmodRestrictIntTensorIso_inv_tmul
    (n : ℕ) (A B : Rep.{0} (ZMod n) G) (x : A) (y : B) :
    @DFunLike.coe
      ((zmodRestrictInt n (A ⊗ B)).ρ.IntertwiningMap
        ((zmodRestrictInt n A).ρ.tprod (zmodRestrictInt n B).ρ))
      (zmodRestrictInt n (A ⊗ B))
      (fun _ => TensorProduct ℤ (zmodRestrictInt n A) (zmodRestrictInt n B))
      (Representation.IntertwiningMap.instFunLike
        (zmodRestrictInt n (A ⊗ B)).ρ
        ((zmodRestrictInt n A).ρ.tprod (zmodRestrictInt n B).ρ))
      (ConcreteCategory.hom (zmodRestrictIntTensorIso n A B).inv) (x ⊗ₜ[ZMod n] y) =
      x ⊗ₜ[ℤ] y :=
  rfl

end Rep
