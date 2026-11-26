/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RightExtraDegeneracyHomotopy

/-!
# Simplicial augmentations with right extra degeneracies

For an object `P` of any category, the constant augmented simplicial object has identity right
extra-degeneracy maps. Every augmented simplicial object has its augmentation morphism to the
constant object on its target.

In an abelian category, a right extra degeneracy contracts the augmented alternating-face
complex. Naturality with the constant augmentation then makes the alternating-face map to the
entire constant simplicial object a quasi-isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The right extra degeneracy of a constant augmented simplicial object.

For any category object `P`, use identity maps for the augmentation section and each extra
degeneracy of its constant augmented simplicial object. -/
def constantRightExtraDegeneracy (P : C) :
    RightExtraDegeneracy ((SimplicialObject.Augmented.const (C := C)).obj P) where
  s' := 𝟙 P
  s _ := 𝟙 P
  s'_comp_ε := by change (𝟙 P) ≫ (𝟙 P) = 𝟙 P; exact Category.id_comp _
  s₀_comp_δ₀ := by change (𝟙 P) ≫ (𝟙 P) = (𝟙 P) ≫ (𝟙 P); rfl
  s_comp_δ_last n := by change (𝟙 P) ≫ (𝟙 P) = 𝟙 P; exact Category.id_comp _
  s_comp_δ n i := by change (𝟙 P) ≫ (𝟙 P) = (𝟙 P) ≫ (𝟙 P); rfl
  s_comp_σ n i := by change (𝟙 P) ≫ (𝟙 P) = (𝟙 P) ≫ (𝟙 P); rfl

/-- The augmentation morphism to a constant simplicial target.

An augmented simplicial object maps to the constant augmented object on its augmentation
point, using its augmentation as the simplicial map and the identity at the point. -/
def augmentationToConstant (X : SimplicialObject.Augmented C) :
    X ⟶ (SimplicialObject.Augmented.const (C := C)).obj X.right where
  left := X.hom
  right := 𝟙 X.right
  w := by
    dsimp only [SimplicialObject.Augmented.const]
    change X.hom ≫ 𝟙 ((SimplicialObject.const C).obj X.right) =
      X.hom ≫ (SimplicialObject.const C).map (𝟙 X.right)
    exact congrArg (fun f => X.hom ≫ f) ((SimplicialObject.const C).map_id X.right).symm

variable [Abelian C]

/-- The alternating augmentation quasi-isomorphism from a right extra degeneracy.

In an abelian category, a right extra degeneracy makes the alternating-face complex map of the
augmentation to the constant simplicial target a quasi-isomorphism. -/
theorem quasiIso_alternating_augmentation {X : SimplicialObject.Augmented C}
    (ed : RightExtraDegeneracy X) :
    QuasiIso ((alternatingFaceMapComplex C).map X.hom) := by
  let Y := (SimplicialObject.Augmented.const (C := C)).obj X.right
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app X) := ed.quasiIso_augmentation
  letI : QuasiIso (AlternatingFaceMapComplex.ε.app Y) :=
    (constantRightExtraDegeneracy X.right).quasiIso_augmentation
  have h := AlternatingFaceMapComplex.ε.naturality (augmentationToConstant X)
  change (alternatingFaceMapComplex C).map X.hom ≫
      AlternatingFaceMapComplex.ε.app Y =
    AlternatingFaceMapComplex.ε.app X ≫
      (ChainComplex.single₀ C).map (𝟙 X.right) at h
  have hid := (ChainComplex.single₀ C).map_id X.right
  have h' := h.trans ((congrArg (fun f => AlternatingFaceMapComplex.ε.app X ≫ f) hid).trans
    (Category.comp_id _))
  letI hComp : QuasiIso ((alternatingFaceMapComplex C).map X.hom ≫
      AlternatingFaceMapComplex.ε.app Y) :=
    h'.symm ▸ (inferInstance : QuasiIso (AlternatingFaceMapComplex.ε.app X))
  exact quasiIso_of_comp_right ((alternatingFaceMapComplex C).map X.hom)
    (AlternatingFaceMapComplex.ε.app Y)
    (hφ := (constantRightExtraDegeneracy X.right).quasiIso_augmentation)
    (hφφ' := hComp)

end CategoryTheory.SimplicialObject.Augmented

end
