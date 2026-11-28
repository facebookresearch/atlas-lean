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

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Presheaf tensor comparison under precomposition and scalar restriction

Let F : C → D, let S and R be commutative ring presheaves on C and D, and let φ : S → F*R. A
module presheaf M over R is sent to the presheaf U ↦ M(F(U)), with its S(U)-action restricted
along φ_U.

The canonical comparison from P(M) ⊗_S P(N) to P(M ⊗_R N) sends m ⊗_{S(U)} n to m ⊗_{R(F(U))}
n. It is natural in both module-presheaf factors. The object and morphism universe levels of C
and D are separate.
-/

@[expose] public section
noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u u₁ u₂ v₁ v₂

namespace PresheafOfModulesOfCommRing

/-- Precomposition of module presheaves with scalar restriction.

For F : C → D and φ : S → F*R, send an R-module presheaf M to the S-module presheaf U ↦
M(F(U)), with action through φ_U. -/
abbrev scalarPresheafPushforward
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (φ : S ⟶ F.op ⋙ R) :
    PresheafOfModulesOfCommRing R ⥤ PresheafOfModulesOfCommRing S :=
  PresheafOfModules.pushforward (F := F)
    (S := S ⋙ forget₂ CommRingCat RingCat) (R := R ⋙ forget₂ CommRingCat RingCat)
    (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
      (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)

/-- The tensor comparison for scalar-restricted presheaf precomposition.

For R-module presheaves M,N, the map P(M) ⊗_S P(N) → P(M ⊗_R N) sends pure tensors at U from
the S(U)-tensor product to the same tensors over R(F(U)). -/
def presheafPushforwardTensorHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (φ : S ⟶ F.op ⋙ R) (M N : PresheafOfModulesOfCommRing R) :
    ((show PresheafOfModulesOfCommRing S from
        (PresheafOfModules.pushforward (F := F)
          (S := S ⋙ forget₂ CommRingCat RingCat)
          (R := R ⋙ forget₂ CommRingCat RingCat)
          (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
            (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)).obj M) ⊗
      (show PresheafOfModulesOfCommRing S from
        (PresheafOfModules.pushforward (F := F)
          (S := S ⋙ forget₂ CommRingCat RingCat)
          (R := R ⋙ forget₂ CommRingCat RingCat)
          (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
            (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)).obj N)) ⟶
    (show PresheafOfModulesOfCommRing S from
      (PresheafOfModules.pushforward (F := F)
        (S := S ⋙ forget₂ CommRingCat RingCat)
        (R := R ⋙ forget₂ CommRingCat RingCat)
        (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
          (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)).obj
        (M ⊗ N : PresheafOfModulesOfCommRing R)) where
  app U := by
    letI : Module (R.obj (F.op.obj U))
        (((PresheafOfModules.pushforward (F := F)
          (S := S ⋙ forget₂ CommRingCat RingCat) (R := R ⋙ forget₂ CommRingCat RingCat)
          (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
            (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)).obj M).obj U) :=
      inferInstanceAs (Module (R.obj (F.op.obj U)) (M.obj (F.op.obj U)))
    letI : Module (R.obj (F.op.obj U))
        (((PresheafOfModules.pushforward (F := F)
          (S := S ⋙ forget₂ CommRingCat RingCat) (R := R ⋙ forget₂ CommRingCat RingCat)
          (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
            (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)).obj N).obj U) :=
      inferInstanceAs (Module (R.obj (F.op.obj U)) (N.obj (F.op.obj U)))
    exact ModuleCat.MonoidalCategory.tensorLift
      (fun m n => m ⊗ₜ[R.obj (F.op.obj U)] n)
      (by intro m m' n; exact TensorProduct.add_tmul m m' n)
      (by
        intro a m n
        change ((show R.obj (F.op.obj U) from (φ.app U) a) • m) ⊗ₜ[R.obj (F.op.obj U)] n =
          (show R.obj (F.op.obj U) from (φ.app U) a) • (m ⊗ₜ[R.obj (F.op.obj U)] n)
        exact TensorProduct.smul_tmul' _ _ _)
      (by intro m n n'; exact TensorProduct.tmul_add m n n')
      (by
        intro a m n
        change m ⊗ₜ[R.obj (F.op.obj U)] ((show R.obj (F.op.obj U) from (φ.app U) a) • n) =
          (show R.obj (F.op.obj U) from (φ.app U) a) • (m ⊗ₜ[R.obj (F.op.obj U)] n)
        exact TensorProduct.tmul_smul _ _ _)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

/-- Naturality of the presheaf tensor comparison in both factors.

For maps a : M → M′ and b : N → N′, applying P(a) ⊗ P(b) before the comparison equals applying
the comparison first and then P(a ⊗ b). -/
theorem presheafPushforwardTensorHom_naturality
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (φ : S ⟶ F.op ⋙ R)
    {M M' N N' : PresheafOfModulesOfCommRing R} (a : M ⟶ M') (b : N ⟶ N') :
    ((scalarPresheafPushforward F S R φ).map a ⊗ₘ
        (scalarPresheafPushforward F S R φ).map b) ≫
      presheafPushforwardTensorHom F S R φ M' N' =
    presheafPushforwardTensorHom F S R φ M N ≫
      (scalarPresheafPushforward F S R φ).map (a ⊗ₘ b) := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

end PresheafOfModulesOfCommRing
