/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorFormulae
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed

universe u

noncomputable section

section Closed

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F G N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Instance synthesis: presheaves of modules over a presheaf of commutative rings are monoidal
closed. -/
example : MonoidalClosed (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :=
  inferInstance

/-- The internal hom of the closed structure is `ihomObj`. -/
example : (ihom F).obj N = PresheafOfModules.ihomObj F N := rfl

/-- The bijection of the tensor-hom adjunction is currying. -/
example (θ : F ⊗ G ⟶ N) :
    (PresheafOfModules.tensorIhomAdj F).homEquiv G N θ = PresheafOfModules.curry' F θ := rfl

/-- Currying the identity of `F ⊗ G` gives the coevaluation `y ↦ (x ↦ x ⊗ y)`. -/
example {X Y : Cᵒᵖ} (f : X ⟶ Y) (y : G.obj X) (x : F.obj Y) :
    ((PresheafOfModules.curry' F (𝟙 (F ⊗ G))).app X y).1 f x = x ⊗ₜ[R.obj Y] G.map f y :=
  rfl

/-- Round trip of currying on the identity of `F ⊗ G`, computed on a pure tensor. -/
example (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => (F ⊗ G).obj X)
      ((PresheafOfModules.uncurry' F (PresheafOfModules.curry' F (𝟙 (F ⊗ G)))).app X).hom
      (x ⊗ₜ[R.obj X] y) = x ⊗ₜ[R.obj X] y := by
  rw [PresheafOfModules.uncurry'_app_tmul, PresheafOfModules.curry'_app_val]
  erw [PresheafOfModules.map_id_apply]
  rfl

/-- Evaluation `F ⊗ ihom F N ⟶ N` evaluates a natural family at the identity arrow. -/
example (X : Cᵒᵖ) (x : F.obj X) (φ : (PresheafOfModules.ihomObj F N).obj X) :
    DFunLike.coe (α := (F.obj X ⊗ (PresheafOfModules.ihomObj F N).obj X :))
      (β := fun _ => N.obj X) (((ihom.ev F).app N).app X).hom (x ⊗ₜ[R.obj X] φ) =
      φ.1 (𝟙 X) x :=
  PresheafOfModules.uncurry'_app_tmul F (𝟙 _) x φ

/-- Restriction in the internal hom precomposes the indexing arrows. -/
example {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : (PresheafOfModules.ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) :
    ((PresheafOfModules.ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

end Closed

section Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat))

/-- The internal hom of two sheaves of modules is a sheaf of modules. -/
example (M N : SheafOfModules.{u} (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat)) :
    SheafOfModules.{u} (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat) :=
  ⟨PresheafOfModules.ihomObj M.val N.val, PresheafOfModules.isSheaf_ihomObj M.val N.val N.isSheaf⟩

/-- The internal hom of the closed structure into a sheaf is a sheaf. -/
example (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (hN : Presheaf.IsSheaf J N.presheaf) : Presheaf.IsSheaf J ((ihom F).obj N).presheaf :=
  PresheafOfModules.isSheaf_ihomObj F N hN

end Sheaf

end
