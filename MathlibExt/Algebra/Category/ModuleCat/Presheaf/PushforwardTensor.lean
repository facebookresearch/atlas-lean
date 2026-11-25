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
# Tensor comparison for scalar-restricted presheaf pushforward

For arbitrary functors between sites and maps of commutative ring presheaves,
the comparison sends a tensor over the source scalars to the same pure tensor
over the target scalars. It is natural in both module-presheaf factors.
-/

@[expose] public section
noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u u₁ u₂ v₁ v₂

namespace PresheafOfModulesOfCommRing

/-- The existing scalar-restricted pushforward with its commutative
presheaf source and target stated explicitly. -/
abbrev scalarPresheafPushforward
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (φ : S ⟶ F.op ⋙ R) :
    PresheafOfModulesOfCommRing R ⥤ PresheafOfModulesOfCommRing S :=
  PresheafOfModules.pushforward (F := F)
    (S := S ⋙ forget₂ CommRingCat RingCat) (R := R ⋙ forget₂ CommRingCat RingCat)
    (Functor.whiskerRight φ (forget₂ CommRingCat RingCat) ≫
      (Functor.associator F.op R (forget₂ CommRingCat RingCat)).hom)

/-- The actual tensor comparison on scalar-restricted pushforward
presheaves. Its local value is the canonical change of scalar tensor map. -/
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

/-- The genuine scalar tensor morphism is natural in both presheaf factors. -/
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
