/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Basic

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Topology

open scoped Simplicial

namespace TopCat.SimplicialRealization

noncomputable section

variable {X Y : SimplicialObject TopCat.{u}}

example : SimplicialObject TopCat.{u} ⥤ TopCat.{u} := TopCat.simplicialRealization

example (n : SimplexCategory) :
    X.obj (op n) ⊗ SimplexCategory.toTop.obj n ⟶
      TopCat.simplicialRealization.obj X :=
  ι X n

example (f : X ⟶ Y) :
    TopCat.simplicialRealization.map (𝟙 X) = 𝟙 _ ∧
      TopCat.simplicialRealization.map (𝟙 X ≫ f) =
        TopCat.simplicialRealization.map (𝟙 X) ≫
          TopCat.simplicialRealization.map f := by
  simp

example :
    (X.map (SimplexCategory.δ (1 : Fin 3)).op ⊗ₘ
        𝟙 (SimplexCategory.toTop.obj ⦋1⦌)) ≫ ι X ⦋1⦌ =
      (𝟙 (X.obj (op ⦋2⦌)) ⊗ₘ
          SimplexCategory.toTop.map (SimplexCategory.δ (1 : Fin 3))) ≫ ι X ⦋2⦌ := by
  apply ι_condition

example (f : X ⟶ Y) (n : SimplexCategory) :
    ι X n ≫ TopCat.simplicialRealization.map f =
      (f.app (op n) ⊗ₘ 𝟙 (SimplexCategory.toTop.obj n)) ≫ ι Y n := by
  apply ι_map

example {Z : TopCat.{u}}
    (f : ∀ n : SimplexCategory,
      X.obj (op n) ⊗ SimplexCategory.toTop.obj n ⟶ Z)
    (hf : ∀ ⦃m n : SimplexCategory⦄ (α : m ⟶ n),
      (X.map α.op ⊗ₘ 𝟙 (SimplexCategory.toTop.obj m)) ≫ f m =
        (𝟙 (X.obj (op n)) ⊗ₘ SimplexCategory.toTop.map α) ≫ f n)
    (n : SimplexCategory) :
    ι X n ≫ desc f hf = f n := by
  apply ι_desc

example {Z : TopCat.{u}} (f g : TopCat.simplicialRealization.obj X ⟶ Z)
    (h : ∀ n : SimplexCategory, ι X n ≫ f = ι X n ≫ g) : f = g := by
  apply hom_ext h

example (n : SimplexCategory) :
    Sigma.ι (fun n : SimplexCategory =>
      X.obj (op n) ⊗ SimplexCategory.toTop.obj n) n ≫ presentationQuotient X = ι X n := by
  apply presentationQuotient_ι

example : IsQuotientMap (presentationQuotient X) :=
  presentationQuotient_isQuotientMap X

example (Z : TopCat.{u}) :
    TopCat.simplicialRealization.obj ((SimplicialObject.const TopCat).obj Z) ≅ Z :=
  constIso Z

example (Z : TopCat.{u}) (n : SimplexCategory) :
    ι ((SimplicialObject.const TopCat).obj Z) n ≫ (constIso Z).hom =
      CartesianMonoidalCategory.fst Z (SimplexCategory.toTop.obj n) := by
  apply ι_constIso_hom

example (Z : TopCat.{u}) :
    (constIso Z).hom ≫ (constIso Z).inv = 𝟙 _ := by
  simp

example (Z : TopCat.{u}) :
    (constIso Z).inv ≫ (constIso Z).hom = 𝟙 _ := by
  simp

example {Z W : TopCat.{u}} (f : Z ⟶ W) :
    TopCat.simplicialRealization.map ((SimplicialObject.const TopCat).map f) ≫
        (constIso W).hom =
      (constIso Z).hom ≫ f := by
  exact constNatIso.hom.naturality f

section UniverseOne

example : SimplicialObject TopCat.{1} ⥤ TopCat.{1} := TopCat.simplicialRealization

example (Z : TopCat.{1}) :
    TopCat.simplicialRealization.obj ((SimplicialObject.const TopCat).obj Z) ≅ Z :=
  constIso Z

example (X : SimplicialObject TopCat.{1}) :
    IsQuotientMap (presentationQuotient X) :=
  presentationQuotient_isQuotientMap X

end UniverseOne

section UniverseZero

example : SimplicialObject TopCat.{0} ⥤ TopCat.{0} := TopCat.simplicialRealization

example (Z : TopCat.{0}) :
    TopCat.simplicialRealization.obj ((SimplicialObject.const TopCat).obj Z) ≅ Z :=
  constIso Z

example (X : SimplicialObject TopCat.{0}) :
    IsQuotientMap (presentationQuotient X) :=
  presentationQuotient_isQuotientMap X

end UniverseZero

#check TopCat.simplicialRealization
#check ι
#check ι_condition
#check ι_map
#check desc
#check ι_desc
#check hom_ext
#check presentation
#check presentationQuotient
#check presentationQuotient_ι
#check presentationQuotient_isQuotientMap
#check constNatIso
#check constIso
#check ι_constIso_hom

#print axioms TopCat.simplicialRealization
#print axioms ι_condition
#print axioms ι_map
#print axioms ι_desc
#print axioms hom_ext
#print axioms presentationQuotient_isQuotientMap
#print axioms constNatIso
#print axioms ι_constIso_hom

end

end TopCat.SimplicialRealization
