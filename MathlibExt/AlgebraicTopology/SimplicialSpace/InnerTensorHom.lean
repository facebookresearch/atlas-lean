/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The natural inner tensor–mapping isomorphism

For every scalar and original simplicial space, the actual mapping end out
of the inner tensor is naturally isomorphic to the scalar internal Hom into
the original mapping end. The comparison is obtained from the two genuine
adjunctions by the native outer associator and right-adjoint uniqueness.
The scalar and source equations below are equalities of whole simplicial maps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped SimplicialSpace.Inner

namespace SimplicialSpace

private def innerTensorAssociator (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    innerTensorBifunctor.obj ((innerTensor K).obj X) ≅
      tensorLeft K ⋙ innerTensorBifunctor.obj X :=
  NatIso.ofComponents
    (fun R => InducedCategory.isoMk
      (Functor.isoWhiskerLeft X.diagram (tensorRightTensor K R).symm))
    (by
      intro R S f
      apply InducedCategory.hom_ext
      apply NatTrans.ext
      funext m
      change (X.diagram.obj m ⊗ K) ◁ f ≫ (α_ (X.diagram.obj m) K S).hom =
        (α_ (X.diagram.obj m) K R).hom ≫ (X.diagram.obj m ◁ (K ◁ f))
      exact associator_naturality_right (X.diagram.obj m) K f)

-- The adjunction is constructed from the actual end equivalence. Use the
-- native equality theorem, rather than presuming this is definitional.
private lemma innerTensorHomAdjunction_homEquiv (X : SimplicialSpace.{u}) :
    (innerTensorHomAdjunction₂.adj X).homEquiv =
      fun K Z => innerTensorHomEquiv K X Z := by
  change (Adjunction.mkOfHomEquiv _).homEquiv = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The native uniqueness isomorphism between the two actual right adjoints. -/
def innerTensorHomIso (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    innerHomFunctor.obj (op ((innerTensor K).obj X)) ≅
      innerHomFunctor.obj (op X) ⋙ ihom K :=
  (innerTensorHomAdjunction₂.adj ((innerTensor K).obj X)).rightAdjointUniq
    (((ihom.adjunction K).comp (innerTensorHomAdjunction₂.adj X)).ofNatIsoLeft
      (innerTensorAssociator K X).symm)


private lemma innerTensorAssociator_scalar {K L : SSet.{u}} (k : K ⟶ L)
    (X : SimplicialSpace.{u}) (R : SSet.{u}) :
    (innerTensorAssociator K X).inv.app R ≫
        (innerTensor R).map ((innerTensorBifunctor.obj X).map k) =
      (innerTensorBifunctor.obj X).map (k ▷ R) ≫
        (innerTensorAssociator L X).inv.app R := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext m
  change (α_ (X.diagram.obj m) K R).inv ≫ ((X.diagram.obj m ◁ k) ▷ R) =
    (X.diagram.obj m ◁ (k ▷ R)) ≫ (α_ (X.diagram.obj m) L R).inv
  exact (associator_inv_naturality_middle (X.diagram.obj m) k R).symm

private lemma innerTensorAssociator_source (K : SSet.{u})
    {X Y : SimplicialSpace.{u}} (x : X ⟶ Y) (R : SSet.{u}) :
    (innerTensorAssociator K X).inv.app R ≫
        (innerTensor R).map ((innerTensor K).map x) =
      (innerTensor (K ⊗ R)).map x ≫ (innerTensorAssociator K Y).inv.app R := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext m
  change (α_ (X.diagram.obj m) K R).inv ≫ ((x.hom.app m ▷ K) ▷ R) =
    (x.hom.app m ▷ (K ⊗ R)) ≫ (α_ (Y.diagram.obj m) K R).inv
  exact (associator_inv_naturality_left (x.hom.app m) K R).symm

private lemma innerTensorHomIso_characteristic (K : SSet.{u}) (X Z : SimplicialSpace.{u})
    (R : SSet.{u})
    (b : R ⟶ (innerHomFunctor.obj (op ((innerTensor K).obj X))).obj Z) :
    b ≫ (innerTensorHomIso K X).hom.app Z =
      curry (innerTensorHomEquiv (K ⊗ R) X Z
        ((innerTensorAssociator K X).inv.app R ≫
          (innerTensorHomEquiv R ((innerTensor K).obj X) Z).symm b)) := by
  let A0 := innerTensorHomAdjunction₂.adj ((innerTensor K).obj X)
  let A1 := (ihom.adjunction K).comp (innerTensorHomAdjunction₂.adj X)
  let A := A1.ofNatIsoLeft (innerTensorAssociator K X).symm
  have h : A.homEquiv R Z ((A0.homEquiv R Z).symm b) =
      b ≫ (A0.rightAdjointUniq A).hom.app Z := by
    apply (A.homEquiv R Z).symm.injective
    rw [Equiv.symm_apply_apply, A.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    exact A0.homEquiv_counit R Z b
  have hh := h.symm
  change b ≫ (innerTensorHomIso K X).hom.app Z =
    (A1.ofNatIsoLeft (innerTensorAssociator K X).symm).homEquiv R Z
      ((A0.homEquiv R Z).symm b) at hh
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply] at hh
  dsimp only [A1] at hh
  rw [Adjunction.comp_homEquiv, innerTensorHomAdjunction_homEquiv] at hh
  dsimp only [A0] at hh
  rw [innerTensorHomAdjunction_homEquiv] at hh
  exact hh

/-- Naturality in every original scalar map, with the complete internal-Hom precomposition. -/
lemma innerTensorHomIso_naturality_scalar {K L : SSet.{u}} (k : K ⟶ L)
    (X Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z ≫
        (innerTensorHomIso K X).hom.app Z =
      (innerTensorHomIso L X).hom.app Z ≫
        (pre k).app ((innerHomFunctor.obj (op X)).obj Z) := by
  suffices h : ∀ (R : SSet.{u})
      (b : R ⟶ (innerHomFunctor.obj (op ((innerTensor L).obj X))).obj Z),
      (b ≫ (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z) ≫
          (innerTensorHomIso K X).hom.app Z =
        (b ≫ (innerTensorHomIso L X).hom.app Z) ≫
          (pre k).app ((innerHomFunctor.obj (op X)).obj Z) by
    simpa only [Category.id_comp] using h _ (𝟙 _)
  intro R b
  have hb :
      (innerTensorHomEquiv R ((innerTensor K).obj X) Z).symm
          (b ≫ (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z) =
        (innerTensor R).map ((innerTensorBifunctor.obj X).map k) ≫
          (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b := by
    apply (innerTensorHomEquiv R ((innerTensor K).obj X) Z).injective
    exact ((innerTensorHomEquiv R ((innerTensor K).obj X) Z).apply_symm_apply _).trans
      (((congrArg (fun f => f ≫
          (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z)
        ((innerTensorHomEquiv R ((innerTensor L).obj X) Z).apply_symm_apply b)).symm).trans
        (innerTensorHomEquiv_source ((innerTensorBifunctor.obj X).map k) R Z _).symm)
  have hcurried :
      (b ≫ (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z) ≫
          (innerTensorHomIso K X).hom.app Z =
      curry ((k ▷ R) ≫ innerTensorHomEquiv (L ⊗ R) X Z
        ((innerTensorAssociator L X).inv.app R ≫
          (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b)) := by
    calc
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫
            (innerTensorHomEquiv R ((innerTensor K).obj X) Z).symm
              (b ≫ (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z))) :=
        innerTensorHomIso_characteristic K X Z R _
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫
            (innerTensor R).map ((innerTensorBifunctor.obj X).map k) ≫
            (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b)) :=
        congrArg (fun f => curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫ f))) hb
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorBifunctor.obj X).map (k ▷ R) ≫
            (innerTensorAssociator L X).inv.app R ≫
            (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b)) := by
        apply congrArg (fun f => curry (innerTensorHomEquiv (K ⊗ R) X Z f))
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫
              (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b)
            (innerTensorAssociator_scalar k X R)).trans (Category.assoc _ _ _))
      _ = curry ((k ▷ R) ≫ innerTensorHomEquiv (L ⊗ R) X Z
          ((innerTensorAssociator L X).inv.app R ≫
            (innerTensorHomEquiv R ((innerTensor L).obj X) Z).symm b)) :=
        congrArg curry (innerTensorHomEquiv_scalar (k ▷ R) X Z _)
  exact hcurried.trans
    ((curry_pre_app k _).symm.trans
      (congrArg (fun f => f ≫ (pre k).app ((innerHomFunctor.obj (op X)).obj Z))
        (innerTensorHomIso_characteristic L X Z R b)).symm)

/-- Naturality in every original source map, with the actual contravariant enriched end. -/
lemma innerTensorHomIso_naturality_source (K : SSet.{u})
    {X Y : SimplicialSpace.{u}} (x : X ⟶ Y) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map ((innerTensor K).map x).op).app Z ≫
        (innerTensorHomIso K X).hom.app Z =
      (innerTensorHomIso K Y).hom.app Z ≫
        (ihom K).map ((innerHomFunctor.map x.op).app Z) := by
  suffices h : ∀ (R : SSet.{u})
      (b : R ⟶ (innerHomFunctor.obj (op ((innerTensor K).obj Y))).obj Z),
      (b ≫ (innerHomFunctor.map ((innerTensor K).map x).op).app Z) ≫
          (innerTensorHomIso K X).hom.app Z =
        (b ≫ (innerTensorHomIso K Y).hom.app Z) ≫
          (ihom K).map ((innerHomFunctor.map x.op).app Z) by
    simpa only [Category.id_comp] using h _ (𝟙 _)
  intro R b
  have hb :
      (innerTensorHomEquiv R ((innerTensor K).obj X) Z).symm
          (b ≫ (innerHomFunctor.map ((innerTensor K).map x).op).app Z) =
        (innerTensor R).map ((innerTensor K).map x) ≫
          (innerTensorHomEquiv R ((innerTensor K).obj Y) Z).symm b := by
    apply (innerTensorHomEquiv R ((innerTensor K).obj X) Z).injective
    exact ((innerTensorHomEquiv R ((innerTensor K).obj X) Z).apply_symm_apply _).trans
      (((congrArg (fun f => f ≫ (innerHomFunctor.map ((innerTensor K).map x).op).app Z)
        ((innerTensorHomEquiv R ((innerTensor K).obj Y) Z).apply_symm_apply b)).symm).trans
        (innerTensorHomEquiv_source ((innerTensor K).map x) R Z _).symm)
  have hcurried :
      (b ≫ (innerHomFunctor.map ((innerTensor K).map x).op).app Z) ≫
          (innerTensorHomIso K X).hom.app Z =
      curry (innerTensorHomEquiv (K ⊗ R) X Z
        ((innerTensor (K ⊗ R)).map x ≫ (innerTensorAssociator K Y).inv.app R ≫
          (innerTensorHomEquiv R ((innerTensor K).obj Y) Z).symm b)) := by
    calc
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫
            (innerTensorHomEquiv R ((innerTensor K).obj X) Z).symm
              (b ≫ (innerHomFunctor.map ((innerTensor K).map x).op).app Z))) :=
        innerTensorHomIso_characteristic K X Z R _
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫
            (innerTensor R).map ((innerTensor K).map x) ≫
            (innerTensorHomEquiv R ((innerTensor K).obj Y) Z).symm b)) :=
        congrArg (fun f => curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensorAssociator K X).inv.app R ≫ f))) hb
      _ = curry (innerTensorHomEquiv (K ⊗ R) X Z
          ((innerTensor (K ⊗ R)).map x ≫ (innerTensorAssociator K Y).inv.app R ≫
            (innerTensorHomEquiv R ((innerTensor K).obj Y) Z).symm b)) := by
        apply congrArg (fun f => curry (innerTensorHomEquiv (K ⊗ R) X Z f))
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫
              (innerTensorHomEquiv R ((innerTensor K).obj Y) Z).symm b)
            (innerTensorAssociator_source K x R)).trans (Category.assoc _ _ _))
  exact hcurried.trans
    ((congrArg curry (innerTensorHomEquiv_source x (K ⊗ R) Z _)).trans
      ((curry_natural_right _ _).trans
        (congrArg (fun f => f ≫ (ihom K).map ((innerHomFunctor.map x.op).app Z))
          (innerTensorHomIso_characteristic K Y Z R b)).symm))

end SimplicialSpace
