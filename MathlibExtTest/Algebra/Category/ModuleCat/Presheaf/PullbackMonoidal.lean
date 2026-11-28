/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.PullbackMonoidal

/-!
# Tests for the monoidal structures on functors of presheaves of modules

The instances of `MathlibExt.Algebra.Category.ModuleCat.Presheaf.PullbackMonoidal` are found by
instance search, and their structure maps are the expected ones: the tensorator of restriction of
scalars sends `m ⊗ₜ n` to `m ⊗ₜ n`, and that of the free presheaf of modules sends
`freeMk x ⊗ₜ freeMk y` to `freeMk (x, y)`.
-/

@[expose] public section

noncomputable section

universe u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace MathlibExtTest.PresheafOfModulesPullbackMonoidal

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

example : (PresheafOfModules.restrictScalars (PresheafOfModules.ringCatHom φ)).LaxMonoidal :=
  inferInstance

/-- The unit of restriction of scalars is, objectwise, that of `ModuleCat.restrictScalars`. -/
example (U : Cᵒᵖ) :
    (ε (PresheafOfModules.restrictScalars (PresheafOfModules.ringCatHom φ))).app U =
      ε (ModuleCat.restrictScalars (φ.app U).hom) :=
  rfl

/-- The tensorator of restriction of scalars sends `m ⊗ₜ n` to `m ⊗ₜ n`. -/
example (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U) :
    (μ (PresheafOfModules.restrictScalars (PresheafOfModules.ringCatHom φ)) M N).app U
        ((m : ((PresheafOfModules.restrictScalars (PresheafOfModules.ringCatHom φ)).obj M).obj U)
          ⊗ₜ[S.obj U]
          (n : ((PresheafOfModules.restrictScalars (PresheafOfModules.ringCatHom φ)).obj N).obj U)) =
      (m ⊗ₜ[R.obj U] n : TensorProduct (R.obj U) (M.obj U) (N.obj U)) :=
  ModuleCat.restrictScalars_μ_tmul (φ.app U).hom (M.obj U) (N.obj U) m n

end restrictScalars

section pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

example :
    (PresheafOfModules.pushforward (R := R ⋙ forget₂ _ _)
      (PresheafOfModules.ringCatHom φ)).LaxMonoidal :=
  inferInstance

example [(PresheafOfModules.pushforward (R := R ⋙ forget₂ _ _)
      (PresheafOfModules.ringCatHom φ)).IsRightAdjoint] :
    (PresheafOfModules.pullback (R := R ⋙ forget₂ _ _)
      (PresheafOfModules.ringCatHom φ)).OplaxMonoidal :=
  inferInstance

end pushforward

section free

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

example : (PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).Monoidal :=
  inferInstance

/-- The tensorator of the free presheaf of modules is `freeμIso`. -/
example (F G : Cᵒᵖ ⥤ Type u) :
    Functor.Monoidal.μIso (PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)) F G =
      PresheafOfModules.freeμIso (R := R) F G :=
  rfl

/-- `freeμIso` sends `freeMk x ⊗ₜ freeMk y` to `freeMk (x, y)`. -/
example (F G : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    (PresheafOfModules.freeμIso (R := R) F G).hom.app X
        (ModuleCat.freeMk x ⊗ₜ[R.obj X] ModuleCat.freeMk y) =
      ModuleCat.freeMk (x, y) := by
  rw [PresheafOfModules.freeμIso_hom_app]
  exact ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk (R.obj X) x y

end free

section pullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D] (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

example : (PresheafOfModules.PullbackMonoidal.pb F φ).Monoidal :=
  inferInstance

example :
    (PresheafOfModules.pullback (R := R ⋙ forget₂ _ _)
      (PresheafOfModules.ringCatHom φ)).Monoidal :=
  inferInstance

example (A B : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    IsIso (δ (PresheafOfModules.PullbackMonoidal.pb F φ) A B) :=
  inferInstance

example : IsIso (η (PresheafOfModules.PullbackMonoidal.pb F φ)) :=
  inferInstance

end pullback

end MathlibExtTest.PresheafOfModulesPullbackMonoidal

end
