/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementCohomology
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import MathlibExt.Algebra.Category.Grp.Monoidal
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# Tensor coefficients on small étale sites

The tensor presheaf takes the integer tensor product of section groups.
Its sheafification is the tensor coefficient sheaf.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The sectionwise integer tensor product of the original coefficient presheaves. -/
def smallEtaleTensorPresheaf (X : Scheme.{u})
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w} where
  obj U := AddCommGrpCat.of (F.obj U ⊗[ℤ] G.obj U)
  map f := AddCommGrpCat.ofHom
    (TensorProduct.map (F.map f).hom.toIntLinearMap (G.map f).hom.toIntLinearMap).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        change ((F.map (𝟙 U)).hom a) ⊗ₜ[ℤ] ((G.map (𝟙 U)).hom b) = a ⊗ₜ[ℤ] b
        rw [F.map_id, G.map_id]
        rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        change ((F.map (f ≫ g)).hom a) ⊗ₜ[ℤ] ((G.map (f ≫ g)).hom b) =
          ((F.map g).hom ((F.map f).hom a)) ⊗ₜ[ℤ]
            ((G.map g).hom ((G.map f).hom b))
        rw [F.map_comp, G.map_comp]
        rfl
    | add a b ha hb => simp only [map_add, ha, hb]

/-- Restriction of an original pure tensor is the tensor of the original restrictions. -/
theorem smallEtaleTensorPresheaf_map_tmul (X : Scheme.{u})
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w})
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (a : F.obj U) (b : G.obj U) :
    (smallEtaleTensorPresheaf.{u, w} X F G).map f (a ⊗ₜ[ℤ] b) =
      (F.map f a) ⊗ₜ[ℤ] (G.map f b) := rfl

/-- The actual tensor coefficient sheaf is the sheafification of the sectionwise tensor. -/
def smallEtaleTensorSheaf (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj)

/-- The original section tensors enter the actual tensor sheaf by the sheafification unit. -/
def smallEtaleTensorSheafSectionMap (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : X.Etaleᵒᵖ) :
    AddCommGrpCat.of (F.obj.obj U ⊗[ℤ] G.obj.obj U) ⟶
      (smallEtaleTensorSheaf.{u, w} X F G).obj.obj U :=
  (toSheafify X.smallEtaleTopology (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj)).app U

/-- The actual sheafification map respects the tensor of every original restriction. -/
theorem smallEtaleTensorSheafSectionMap_naturality (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj).map f ≫
        smallEtaleTensorSheafSectionMap.{u, w} X F G V =
      smallEtaleTensorSheafSectionMap.{u, w} X F G U ≫
        (smallEtaleTensorSheaf.{u, w} X F G).obj.map f :=
  (toSheafify X.smallEtaleTopology (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj)).naturality f

set_option backward.isDefEq.respectTransparency.types false in
/-- Original local tensor germs map to the tensor of the two original geometric germs. -/
def smallEtalePointTensorStalkMap (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (p.presheafFiber (A := AddCommGrpCat.{max u w})).obj (smallEtaleTensorPresheaf.{u, w} X F G) ⟶
      AddCommGrpCat.of ((p.presheafFiber (A := AddCommGrpCat.{max u w})).obj F ⊗[ℤ]
          (p.presheafFiber (A := AddCommGrpCat.{max u w})).obj G) :=
  p.presheafFiberDesc (A := AddCommGrpCat.{max u w})
    (fun U x => AddCommGrpCat.ofHom
      (TensorProduct.map (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F).hom.toIntLinearMap
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G).hom.toIntLinearMap).toAddMonoidHom)
    (by
      intro U V f x
      have h :
          (TensorProduct.map
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F).hom.toIntLinearMap
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G).hom.toIntLinearMap).comp
            (TensorProduct.map (F.map f.op).hom.toIntLinearMap (G.map f.op).hom.toIntLinearMap) =
          TensorProduct.map
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) V
                (p.fiber.map f x) F).hom.toIntLinearMap
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) V
                (p.fiber.map f x) G).hom.toIntLinearMap := by
        apply TensorProduct.ext'
        intro a b
        change
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F (F.map f.op a)) ⊗ₜ[ℤ]
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G (G.map f.op b)) =
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) V (p.fiber.map f x) F a) ⊗ₜ[ℤ]
            (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) V (p.fiber.map f x) G b)
        rw [p.toPresheafFiber_w_apply, p.toPresheafFiber_w_apply]
      exact congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom) h)

/-- The actual point tensor comparison has the prescribed value on every original pure tensor
germ. -/
theorem smallEtalePointTensorStalkMap_tmul (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (U : X.Etale) (x : p.fiber.obj U)
    (a : F.obj (op U)) (b : G.obj (op U)) :
    smallEtalePointTensorStalkMap.{u, w} X p F G
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
            (smallEtaleTensorPresheaf.{u, w} X F G) (a ⊗ₜ[ℤ] b)) =
      (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F a) ⊗ₜ[ℤ]
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G b) := by
  have h : p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
        (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X p F G =
      AddCommGrpCat.ofHom (TensorProduct.map
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F).hom.toIntLinearMap
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
            G).hom.toIntLinearMap).toAddMonoidHom :=
    p.toPresheafFiber_presheafFiberDesc _ _ U x
  exact ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal tensor-of-germs comparison is invertible for the same actual filtered point
fiber. -/
theorem smallEtalePointTensorStalkMap_isIso (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    IsIso (smallEtalePointTensorStalkMap.{u, w} X p F G) := by
  let e := IsColimit.coconePointUniqueUpToIso
    (p.isColimitPresheafFiberCocone (smallEtaleTensorPresheaf.{u, w} X F G))
    ((p.isColimitPresheafFiberCocone F).tensor (p.isColimitPresheafFiberCocone G))
  have h : smallEtalePointTensorStalkMap.{u, w} X p F G = e.hom := by
    apply p.presheafFiber_hom_ext
    intro U x
    change p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
      (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X p F G =
      p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
        (smallEtaleTensorPresheaf.{u, w} X F G) ≫ e.hom
    have he : p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
          (smallEtaleTensorPresheaf.{u, w} X F G) ≫ e.hom =
        AddCommGrpCat.ofHom (TensorProduct.map
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F).hom.toIntLinearMap
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
              G).hom.toIntLinearMap).toAddMonoidHom :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (p.isColimitPresheafFiberCocone (smallEtaleTensorPresheaf.{u, w} X F G))
        ((p.isColimitPresheafFiberCocone F).tensor (p.isColimitPresheafFiberCocone G))
        (op (p.fiber.elementsMk U x))
    exact (p.toPresheafFiber_presheafFiberDesc _ _ U x).trans he.symm
  rw [h]
  exact e.isIso_hom

/-- The actual tensor stalk isomorphism uses the original tensor-of-germs map. -/
def smallEtalePointTensorStalkIso (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    (p.presheafFiber (A := AddCommGrpCat.{max u w})).obj
        (smallEtaleTensorPresheaf.{u, w} X F G) ≅
      AddCommGrpCat.of ((p.presheafFiber (A := AddCommGrpCat.{max u w})).obj F ⊗[ℤ]
        (p.presheafFiber (A := AddCommGrpCat.{max u w})).obj G) := by
  let : IsIso (smallEtalePointTensorStalkMap.{u, w} X p F G) :=
    smallEtalePointTensorStalkMap_isIso.{u, w} X p F G
  exact asIso (smallEtalePointTensorStalkMap.{u, w} X p F G)

/-- The stalk of the actual tensor sheaf is the tensor of the two original stalks. -/
def smallEtalePointTensorSheafStalkIso (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (p.sheafFiber (A := AddCommGrpCat.{max u w})).obj (smallEtaleTensorSheaf.{u, w} X F G) ≅
      AddCommGrpCat.of ((p.sheafFiber (A := AddCommGrpCat.{max u w})).obj F ⊗[ℤ]
        (p.sheafFiber (A := AddCommGrpCat.{max u w})).obj G) :=
  (p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}).app
      (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj) ≪≫
    smallEtalePointTensorStalkIso.{u, w} X p F.obj G.obj

set_option backward.isDefEq.respectTransparency.types false in
/-- Original pure section tensors have the tensor of the actual original germ values. -/
theorem smallEtalePointTensorSheafStalkIso_section_tmul (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (U : X.Etale) (x : p.fiber.obj U) (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (smallEtalePointTensorSheafStalkIso.{u, w} X p F G).hom
      (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
        (smallEtaleTensorSheaf.{u, w} X F G).obj
        (smallEtaleTensorSheafSectionMap.{u, w} X F G (op U) (a ⊗ₜ[ℤ] b))) =
      (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F.obj a) ⊗ₜ[ℤ]
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G.obj b) := by
  let T := smallEtaleTensorPresheaf.{u, w} X F.obj G.obj
  let q := toSheafify X.smallEtaleTopology T
  let e := (p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}).app T
  have hq : (p.presheafFiber (A := AddCommGrpCat.{max u w})).map q ≫ e.hom = 𝟙 _ :=
    e.inv_hom_id
  have hn := p.toPresheafFiber_naturality q U x
  have hg : q.app (op U) ≫
        p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x (sheafify X.smallEtaleTopology T) ≫
        e.hom = p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x T := by
    exact (congrArg (fun l => l ≫ e.hom) hn.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun l => p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x T ≫ l) hq).trans
          (Category.comp_id _)))
  have hv := ConcreteCategory.congr_hom hg (a ⊗ₜ[ℤ] b)
  exact (congrArg (smallEtalePointTensorStalkIso.{u, w} X p F.obj G.obj).hom hv).trans
    (smallEtalePointTensorStalkMap_tmul.{u, w} X p F.obj G.obj U x a b)

/-- Two original presheaf maps induce the actual binary integer tensor map. -/
def smallEtaleTensorPresheafMap (X : Scheme.{u})
    {F F' G G' : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    smallEtaleTensorPresheaf.{u, w} X F G ⟶ smallEtaleTensorPresheaf.{u, w} X F' G' where
  app U := AddCommGrpCat.ofHom
    (TensorProduct.map (f.app U).hom.toIntLinearMap (g.app U).hom.toIntLinearMap).toAddMonoidHom
  naturality {U V} h := by
    have he :
        (TensorProduct.map (f.app V).hom.toIntLinearMap (g.app V).hom.toIntLinearMap).comp
          (TensorProduct.map (F.map h).hom.toIntLinearMap (G.map h).hom.toIntLinearMap) =
        (TensorProduct.map (F'.map h).hom.toIntLinearMap (G'.map h).hom.toIntLinearMap).comp
          (TensorProduct.map (f.app U).hom.toIntLinearMap (g.app U).hom.toIntLinearMap) := by
      apply TensorProduct.ext'
      intro a b
      change ((f.app V) (F.map h a)) ⊗ₜ[ℤ] ((g.app V) (G.map h b)) =
        (F'.map h (f.app U a)) ⊗ₜ[ℤ] (G'.map h (g.app U b))
      have hf : (f.app V) (F.map h a) = F'.map h (f.app U a) :=
        ConcreteCategory.congr_hom (f.naturality h) a
      have hg : (g.app V) (G.map h b) = G'.map h (g.app U b) :=
        ConcreteCategory.congr_hom (g.naturality h) b
      rw [hf, hg]
    exact congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom) he

/-- Two original sheaf maps induce the actual map of tensor coefficient sheaves. -/
def smallEtaleTensorSheafMap (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    smallEtaleTensorSheaf.{u, w} X F G ⟶ smallEtaleTensorSheaf.{u, w} X F' G' :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).map
    (smallEtaleTensorPresheafMap.{u, w} X f.hom g.hom)

/-- Every original pure tensor section is mapped to the tensor of its original coefficient
images. -/
theorem smallEtaleTensorSheafMap_section_tmul (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') (U : X.Etaleᵒᵖ)
    (a : F.obj.obj U) (b : G.obj.obj U) :
    (smallEtaleTensorSheafMap.{u, w} X f g).hom.app U
        (smallEtaleTensorSheafSectionMap.{u, w} X F G U (a ⊗ₜ[ℤ] b)) =
      smallEtaleTensorSheafSectionMap.{u, w} X F' G' U
        ((f.hom.app U a) ⊗ₜ[ℤ] (g.hom.app U b)) := by
  have h := congrArg (fun t => t.app U)
    (toSheafify_naturality X.smallEtaleTopology (smallEtaleTensorPresheafMap.{u, w} X f.hom g.hom))
  exact (ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor-of-germs map commutes with every original pair of coefficient morphisms. -/
theorem smallEtalePointTensorStalkMap_naturality (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    {F F' G G' : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    (p.presheafFiber (A := AddCommGrpCat.{max u w})).map
        (smallEtaleTensorPresheafMap.{u, w} X f g) ≫
      smallEtalePointTensorStalkMap.{u, w} X p F' G' =
      smallEtalePointTensorStalkMap.{u, w} X p F G ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map f).hom.toIntLinearMap
          ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map
              g).hom.toIntLinearMap).toAddMonoidHom := by
  apply p.presheafFiber_hom_ext
  intro U x
  have hf := p.toPresheafFiber_naturality f U x
  have hg := p.toPresheafFiber_naturality g U x
  have ht := p.toPresheafFiber_naturality (smallEtaleTensorPresheafMap.{u, w} X f g) U x
  have he (A B : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
      p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
        (smallEtaleTensorPresheaf.{u, w} X A B) ≫
        smallEtalePointTensorStalkMap.{u, w} X p A B =
      AddCommGrpCat.ofHom (TensorProduct.map
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x A).hom.toIntLinearMap
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
            B).hom.toIntLinearMap).toAddMonoidHom :=
    p.toPresheafFiber_presheafFiberDesc _ _ U x
  have hv :
      (TensorProduct.map
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F').hom.toIntLinearMap
        (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G').hom.toIntLinearMap).comp
        (TensorProduct.map (f.app (op U)).hom.toIntLinearMap (g.app (op U)).hom.toIntLinearMap) =
      (TensorProduct.map
        ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map f).hom.toIntLinearMap
        ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map g).hom.toIntLinearMap).comp
        (TensorProduct.map
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F).hom.toIntLinearMap
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x G).hom.toIntLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b)
      (ConcreteCategory.congr_hom hf a).symm (ConcreteCategory.congr_hom hg b).symm
  have hl : p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
      (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map
        (smallEtaleTensorPresheafMap.{u, w} X f g) ≫
        smallEtalePointTensorStalkMap.{u, w} X p F' G') =
      (smallEtaleTensorPresheafMap.{u, w} X f g).app (op U) ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x F').hom.toIntLinearMap
          (p.toPresheafFiber (A := AddCommGrpCat.{max u w}) U x
              G').hom.toIntLinearMap).toAddMonoidHom := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun l => l ≫ smallEtalePointTensorStalkMap.{u, w} X p F' G') ht).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun l => (smallEtaleTensorPresheafMap.{u, w} X f g).app (op U) ≫ l)
              (he F' G'))))
  have hr := congrArg (fun l => l ≫ AddCommGrpCat.ofHom (TensorProduct.map
      ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map f).hom.toIntLinearMap
      ((p.presheafFiber (A := AddCommGrpCat.{max u w})).map
          g).hom.toIntLinearMap).toAddMonoidHom) (he F G)
  exact hl.trans ((congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom) hv).trans
    (hr.symm.trans (Category.assoc _ _ _)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sheaf tensor stalk isomorphism commutes with original coefficient maps. -/
theorem smallEtalePointTensorSheafStalkIso_naturality (X : Scheme.{u})
    (p : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology)
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    (p.sheafFiber (A := AddCommGrpCat.{max u w})).map (smallEtaleTensorSheafMap.{u, w} X f g) ≫
        (smallEtalePointTensorSheafStalkIso.{u, w} X p F' G').hom =
      (smallEtalePointTensorSheafStalkIso.{u, w} X p F G).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          ((p.sheafFiber (A := AddCommGrpCat.{max u w})).map f).hom.toIntLinearMap
          ((p.sheafFiber (A := AddCommGrpCat.{max u w})).map
              g).hom.toIntLinearMap).toAddMonoidHom := by
  let e := p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}
  let a := smallEtaleTensorPresheafMap.{u, w} X f.hom g.hom
  have he : (p.sheafFiber (A := AddCommGrpCat.{max u w})).map
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).map a) ≫
        e.hom.app (smallEtaleTensorPresheaf.{u, w} X F'.obj G'.obj) =
      e.hom.app (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj) ≫
        (p.presheafFiber (A := AddCommGrpCat.{max u w})).map a := e.hom.naturality a
  have hn := smallEtalePointTensorStalkMap_naturality.{u, w} X p f.hom g.hom
  change _ ≫ (e.hom.app _ ≫ smallEtalePointTensorStalkMap.{u, w} X p F'.obj G'.obj) =
    (e.hom.app _ ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ smallEtalePointTensorStalkMap.{u, w} X p F'.obj G'.obj) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun l => e.hom.app (smallEtaleTensorPresheaf.{u, w} X F.obj G.obj) ≫
            l) hn).trans
          (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor presheaf map respects original coefficient composition. -/
theorem smallEtaleTensorPresheafMap_comp (X : Scheme.{u})
    {F₁ F₂ F₃ G₁ G₂ G₃ : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}}
    (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) (g₁ : G₁ ⟶ G₂) (g₂ : G₂ ⟶ G₃) :
    smallEtaleTensorPresheafMap.{u, w} X f₁ g₁ ≫ smallEtaleTensorPresheafMap.{u, w} X f₂ g₂ =
      smallEtaleTensorPresheafMap.{u, w} X (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  apply NatTrans.ext
  funext U
  exact congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom)
    (TensorProduct.map_comp (f₂.app U).hom.toIntLinearMap (g₂.app U).hom.toIntLinearMap
      (f₁.app U).hom.toIntLinearMap (g₁.app U).hom.toIntLinearMap).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor sheaf map respects original coefficient composition. -/
theorem smallEtaleTensorSheafMap_comp (X : Scheme.{u})
    {F₁ F₂ F₃ G₁ G₂ G₃ : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) (g₁ : G₁ ⟶ G₂) (g₂ : G₂ ⟶ G₃) :
    smallEtaleTensorSheafMap.{u, w} X f₁ g₁ ≫ smallEtaleTensorSheafMap.{u, w} X f₂ g₂ =
      smallEtaleTensorSheafMap.{u, w} X (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  let S := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  exact (S.map_comp (smallEtaleTensorPresheafMap.{u, w} X f₁.hom g₁.hom)
    (smallEtaleTensorPresheafMap.{u, w} X f₂.hom g₂.hom)).symm.trans
      (congrArg S.map (smallEtaleTensorPresheafMap_comp.{u, w} X f₁.hom f₂.hom g₁.hom g₂.hom))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor presheaf map preserves the original identities. -/
theorem smallEtaleTensorPresheafMap_id (X : Scheme.{u})
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    smallEtaleTensorPresheafMap.{u, w} X (𝟙 F) (𝟙 G) = 𝟙 _ := by
  apply NatTrans.ext
  funext U
  have h : TensorProduct.map (LinearMap.id : F.obj U →ₗ[ℤ] F.obj U)
      (LinearMap.id : G.obj U →ₗ[ℤ] G.obj U) = LinearMap.id := TensorProduct.map_id
  exact congrArg (fun l : F.obj U ⊗[ℤ] G.obj U →ₗ[ℤ] F.obj U ⊗[ℤ] G.obj U =>
    AddCommGrpCat.ofHom l.toAddMonoidHom) h

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor sheaf map preserves the original identities. -/
theorem smallEtaleTensorSheafMap_id (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheafMap.{u, w} X (𝟙 F) (𝟙 G) = 𝟙 _ := by
  let S := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max u w}
  exact (congrArg S.map (smallEtaleTensorPresheafMap_id.{u, w} X F.obj G.obj)).trans (S.map_id _)

/-- Original global sections have the actual binary map to sections of the tensor sheaf. -/
def smallEtaleGammaTensorMap (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    AddCommGrpCat.of
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj F ⊗[ℤ]
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj G) ⟶
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        (smallEtaleTensorSheaf.{u, w} X F G) :=
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  let U := Opposite.op (Scheme.Etale.mk (𝟙 X))
  AddCommGrpCat.ofHom (TensorProduct.map
      (S.hom.app F).hom.toIntLinearMap (S.hom.app G).hom.toIntLinearMap).toAddMonoidHom ≫
    smallEtaleTensorSheafSectionMap.{u, w} X F G U ≫
      S.inv.app (smallEtaleTensorSheaf.{u, w} X F G)

private theorem composeIsoInvHom.{vC, uC} {C : Type uC} [Category.{vC} C]
    {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (e : E ≅ D) :
    (f ≫ g ≫ e.inv) ≫ e.hom = f ≫ g := by
  rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem tensorSectionIsoValue.{s} (A B D E H : AddCommGrpCat.{s})
    (f : A ⟶ D) (g : B ⟶ E) (q : AddCommGrpCat.of (D ⊗[ℤ] E) ⟶ H)
    {K : AddCommGrpCat.{s}} (e : K ≅ H) (a : A) (b : B) :
    e.hom ((AddCommGrpCat.ofHom (TensorProduct.map f.hom.toIntLinearMap
      g.hom.toIntLinearMap).toAddMonoidHom ≫ q ≫ e.inv) (a ⊗ₜ[ℤ] b)) =
      q ((f a) ⊗ₜ[ℤ] (g b)) := by
  exact ConcreteCategory.congr_hom
    (composeIsoInvHom (AddCommGrpCat.ofHom (TensorProduct.map f.hom.toIntLinearMap
      g.hom.toIntLinearMap).toAddMonoidHom) q e) (a ⊗ₜ[ℤ] b)

set_option backward.isDefEq.respectTransparency.types false in
/-- The global-section tensor map has the literal product of original terminal-section values. -/
theorem smallEtaleGammaTensorMap_tmul (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (a : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj F)
    (b : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj G) :
    let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)
    let U : X.Etaleᵒᵖ := Opposite.op (Scheme.Etale.mk (𝟙 X))
    let sF : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj F ⟶
        F.obj.obj U := S.hom.app F
    let sG : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj G ⟶
        G.obj.obj U := S.hom.app G
    let sT : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        (smallEtaleTensorSheaf.{u, w} X F G) ⟶ (smallEtaleTensorSheaf.{u, w} X F G).obj.obj U :=
      S.hom.app (smallEtaleTensorSheaf.{u, w} X F G)
    sT (smallEtaleGammaTensorMap.{u, w} X F G (a ⊗ₜ[ℤ] b)) =
      smallEtaleTensorSheafSectionMap.{u, w} X F G U ((sF a) ⊗ₜ[ℤ] (sG b)) := by
  intro S U sF sG sT
  exact tensorSectionIsoValue _ _ _ _ _ sF sG
    (smallEtaleTensorSheafSectionMap.{u, w} X F G U)
    (S.app (smallEtaleTensorSheaf.{u, w} X F G)) a b

set_option backward.isDefEq.respectTransparency.types false in
/-- The original global-section tensor map is natural in every pair of sheaf coefficient maps. -/
theorem smallEtaleGammaTensorMap_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    AddCommGrpCat.ofHom (TensorProduct.map
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map f).hom.toIntLinearMap
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
            g).hom.toIntLinearMap).toAddMonoidHom ≫
      smallEtaleGammaTensorMap.{u, w} X F' G' =
      smallEtaleGammaTensorMap.{u, w} X F G ≫
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
          (smallEtaleTensorSheafMap.{u, w} X f g) := by
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  let U := Opposite.op (Scheme.Etale.mk (𝟙 X))
  have hF := S.hom.naturality f
  have hG := S.hom.naturality g
  have hT := S.inv.naturality (smallEtaleTensorSheafMap.{u, w} X f g)
  have hS := congrArg (fun t => t.app U)
    (toSheafify_naturality X.smallEtaleTopology (smallEtaleTensorPresheafMap.{u, w} X f.hom g.hom))
  apply ConcreteCategory.ext_apply
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      have hf := ConcreteCategory.congr_hom hF a
      have hg := ConcreteCategory.congr_hom hG b
      have ht := ConcreteCategory.congr_hom hT
        (smallEtaleTensorSheafSectionMap.{u, w} X F G U
          ((S.hom.app F a) ⊗ₜ[ℤ] (S.hom.app G b)))
      simp only [ConcreteCategory.comp_apply] at hf hg ht
      change S.inv.app (smallEtaleTensorSheaf.{u, w} X F' G')
          (smallEtaleTensorSheafSectionMap.{u, w} X F' G' U
            ((S.hom.app F' ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map f a)) ⊗ₜ[ℤ]
              (S.hom.app G' ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map g b)))) = _
      rw [hf, hg]
      exact (congrArg (S.inv.app (smallEtaleTensorSheaf.{u, w} X F' G'))
        (smallEtaleTensorSheafMap_section_tmul.{u, w} X f g U
          (S.hom.app F a) (S.hom.app G b)).symm).trans ht
  | add a b ha hb => simp only [map_add, ha, hb]

end AlgebraicGeometry.Scheme.DerivedSections
