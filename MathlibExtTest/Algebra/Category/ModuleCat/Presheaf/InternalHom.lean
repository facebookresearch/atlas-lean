/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.InternalHom
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

/-- The internal hom of the closed structure is `PresheafOfModules.ihom`. -/
example : (ihom F).obj N = PresheafOfModules.ihom F N := rfl

/-- The counit of the tensor-hom adjunction, evaluation `F ⊗ ihom F N ⟶ N`, evaluates a section
of the internal hom (`PresheafOfModules.uncurry` of the identity). -/
example (X : Cᵒᵖ) (x : F.obj X) (φ : ((ihom F).obj N).obj X) :
    ((ihom.ev F).app N).app X (x ⊗ₜ φ) = PresheafOfModules.ihomEval φ x :=
  rfl

/-- The unit of the tensor-hom adjunction, coevaluation `G ⟶ ihom F (F ⊗ G)`, is
`PresheafOfModules.curry` of the identity: it sends `y` to `x ↦ x ⊗ y`, with `y` restricted. -/
example (X : Cᵒᵖ) (y : G.obj X) :
    ((ihom.coev F).app G).app X y = (PresheafOfModules.curry (𝟙 (F ⊗ G))).app X y :=
  rfl

end Closed

section Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat))

/-- The internal hom of the closed structure into a sheaf is a sheaf. -/
example (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (hN : Presheaf.IsSheaf J N.presheaf) : Presheaf.IsSheaf J ((ihom F).obj N).presheaf :=
  PresheafOfModules.isSheaf_ihom F N hN

/-- The internal hom of two sheaves of modules is a sheaf of modules. -/
example (M N : SheafOfModules.{u} (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat)) :
    SheafOfModules.{u} (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat) :=
  ⟨(ihom M.val).obj N.val, PresheafOfModules.isSheaf_ihom M.val N.val N.isSheaf⟩

end Sheaf

end
