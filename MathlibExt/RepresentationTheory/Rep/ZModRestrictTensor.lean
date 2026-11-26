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

Let `G` be a group in universe `u`, `n` a natural number, and `A`, `B`
representations of `G` over `ZMod n` whose coefficient carriers lie in universe zero.
The canonical comparison between their tensor products over `ℤ` and over `ZMod n`
is equivariant for the diagonal `G`-actions. It is therefore an isomorphism between
the tensor product of the scalar-restricted representations and the scalar
restriction of their tensor product. Both directions preserve the corresponding
pure tensor `x ⊗ y`, and the modulus `n = 0` is included.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace Rep

variable {G : Type u} [Group G]

/-- For any group `G`, natural number `n`, and representations `A`, `B` over
`ZMod n` with coefficient carriers in universe zero, the canonical linear equivalence
from `A ⊗[ℤ] B` to `A ⊗[ZMod n] B` intertwines the diagonal `G`-actions.
It sends the integral pure tensor `x ⊗ y` to the residue-ring pure tensor of the same
coefficients. The group universe is independent, and `n = 0` is allowed. -/
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

/-- Let `G` be a group, `n : ℕ`, and `A`, `B` representations over `ZMod n`
with coefficient carriers in universe zero. Their scalar-restricted tensor product
over `ℤ` is canonically isomorphic, as a `G`-representation, to the scalar restriction
of `A ⊗[ZMod n] B`. The underlying comparison preserves pure tensors in both
directions, including for `n = 0`. -/
noncomputable def zmodRestrictIntTensorIso
    (n : ℕ) (A B : Rep.{0} (ZMod n) G) :
    zmodRestrictInt n A ⊗ zmodRestrictInt n B ≅
      zmodRestrictInt n (A ⊗ B) :=
  Rep.mkIso (zmodRestrictIntTensorRepresentationEquiv n A B)

/-- For representations `A`, `B` of a group `G` over `ZMod n` with coefficient
carriers in universe zero, the forward tensor comparison sends `x ⊗ₜ[ℤ] y` to
`x ⊗ₜ[ZMod n] y` for every `x ∈ A`, `y ∈ B`. This holds for every `n : ℕ`. -/
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

/-- For representations `A`, `B` of a group `G` over `ZMod n` with coefficient
carriers in universe zero, the inverse tensor comparison sends `x ⊗ₜ[ZMod n] y` to
`x ⊗ₜ[ℤ] y` for every `x ∈ A`, `y ∈ B`. This holds for every `n : ℕ`. -/
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
