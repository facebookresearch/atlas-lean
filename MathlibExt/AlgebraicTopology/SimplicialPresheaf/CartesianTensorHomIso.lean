/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalTests
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Original Cartesian tensor and scalar mapping-end transposition

All scalar mapping objects remain in the fixed SSet value universe. The
original Cartesian tensor and genuine exponential adjunction compare the
two original scalar adjunctions by native right-adjoint uniqueness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory BraidedCategory
open scoped Simplicial MonoidalCategory

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] [smallD : Small.{u} D]
  [localD : LocallySmall.{u} D]

/-- The native reassociation and braiding compare the actual original scalar left functors. -/
private def cartesianScalarLeftIso (A B : SimplicialPresheaf.{u} D) :
    scalarTensor.obj B ⋙ tensorLeft A ≅ scalarTensor.obj (B ⊗ A) :=
  Functor.associator (Functor.const Dᵒᵖ) (tensorLeft B) (tensorLeft A) ≪≫
    ((Functor.whiskeringLeft SSet.{u} (SimplicialPresheaf.{u} D)
      (SimplicialPresheaf.{u} D)).obj (Functor.const Dᵒᵖ)).mapIso
      ((tensorLeftTensor A B).symm ≪≫
        (tensoringLeft (SimplicialPresheaf.{u} D)).mapIso (β_ A B))

/-- The same composed adjunction has the literal original B tensor A as its left functor. -/
private def cartesianScalarAdjunction (A B : SimplicialPresheaf.{u} D) :
    scalarTensor.obj (B ⊗ A) ⊣ exponentialFunctor A ⋙ innerHomFunctor.obj (op B) :=
  ((scalarTensorHomAdjunction B).comp (exponentialAdjunction A)).ofNatIsoLeft
    (cartesianScalarLeftIso A B)

/-- The actual natural transposition on the original fixed-universe scalar mapping ends. -/
def cartesianTensorHomIso (A B : SimplicialPresheaf.{u} D) :
    exponentialFunctor A ⋙ innerHomFunctor.obj (op B) ≅
      innerHomFunctor.obj (op (B ⊗ A)) :=
  (cartesianScalarAdjunction A B).rightAdjointUniq (scalarTensorHomAdjunction (B ⊗ A))

omit smallD localD in
/-- The inverse left comparison is the original braiding followed by reassociation. -/
private lemma cartesianScalarLeftIso_inv_app (A B : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (cartesianScalarLeftIso A B).inv.app K =
      (β_ A B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
        (α_ A B ((Functor.const Dᵒᵖ).obj K)).hom := by
  change ((β_ A B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
    (α_ A B ((Functor.const Dᵒᵖ).obj K)).hom) ≫ 𝟙 _ = _
  simp

omit smallD localD in
/-- The forward comparison retains the original inverse associator and braiding. -/
private lemma cartesianScalarLeftIso_hom_app (A B : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (cartesianScalarLeftIso A B).hom.app K =
      (α_ A B ((Functor.const Dᵒᵖ).obj K)).inv ≫
        (β_ A B).hom ▷ (Functor.const Dᵒᵖ).obj K := by
  change 𝟙 _ ≫ ((α_ A B ((Functor.const Dᵒᵖ).obj K)).inv ≫
    (β_ A B).hom ▷ (Functor.const Dᵒᵖ).obj K) = _
  simp

/-- Native uniqueness identifies the two original transpositions of the same natural map. -/
private lemma cartesianTensorHomIso_homEquiv (A B : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : (scalarTensor.obj (B ⊗ A)).obj K ⟶ Z) :
    (cartesianScalarAdjunction A B).homEquiv K Z f ≫
        (cartesianTensorHomIso A B).hom.app Z =
      scalarTensorHomEquiv (B ⊗ A) K Z f := by
  rw [← scalarTensorHomAdjunction_homEquiv]
  change (cartesianScalarAdjunction A B).homEquiv K Z f ≫
      ((cartesianScalarAdjunction A B).rightAdjointUniq
        (scalarTensorHomAdjunction (B ⊗ A))).hom.app Z =
    (scalarTensorHomAdjunction (B ⊗ A)).homEquiv K Z f
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc,
    (((cartesianScalarAdjunction A B).rightAdjointUniq
      (scalarTensorHomAdjunction (B ⊗ A))).hom.naturality f),
    ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app]

/-- Forward transposition keeps the original scalar map, braid, and associator. -/
theorem cartesianTensorHomIso_characteristic (A B : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : A ⊗ (scalarTensor.obj B).obj K ⟶ Z) :
    scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)
        ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z f) ≫
        (cartesianTensorHomIso A B).hom.app Z =
      scalarTensorHomEquiv (B ⊗ A) K Z
        (((β_ A B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
          (α_ A B ((Functor.const Dᵒᵖ).obj K)).hom) ≫ f) := by
  have h := cartesianTensorHomIso_homEquiv A B K Z
    ((cartesianScalarLeftIso A B).inv.app K ≫ f)
  rw [cartesianScalarAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, scalarTensorHomAdjunction_homEquiv] at h
  change scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)
      ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z
        ((cartesianScalarLeftIso A B).hom.app K ≫
          (cartesianScalarLeftIso A B).inv.app K ≫ f)) ≫
      (cartesianTensorHomIso A B).hom.app Z = _ at h
  have hc : (cartesianScalarLeftIso A B).hom.app K ≫
      (cartesianScalarLeftIso A B).inv.app K ≫ f = f :=
    ((cartesianScalarLeftIso A B).app K).hom_inv_id_assoc f
  rw [hc] at h
  rw [cartesianScalarLeftIso_inv_app] at h
  exact h

/-- Inverse transposition keeps the same scalar map and the two inverse tensor maps. -/
theorem cartesianTensorHomIso_inverse_characteristic (A B : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : (scalarTensor.obj (B ⊗ A)).obj K ⟶ Z) :
    scalarTensorHomEquiv (B ⊗ A) K Z f ≫
        (cartesianTensorHomIso A B).inv.app Z =
      scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)
        ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z
          (((α_ A B ((Functor.const Dᵒᵖ).obj K)).inv ≫
            (β_ A B).hom ▷ (Functor.const Dᵒᵖ).obj K) ≫ f)) := by
  apply ((cartesianTensorHomIso A B).app Z).comp_inv_eq.mpr
  have h := cartesianTensorHomIso_homEquiv A B K Z f
  rw [cartesianScalarAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv] at h
  rw [scalarTensorHomAdjunction_homEquiv] at h
  change scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)
      ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z
        ((cartesianScalarLeftIso A B).hom.app K ≫ f)) ≫
      (cartesianTensorHomIso A B).hom.app Z = _ at h
  simp only [cartesianScalarLeftIso_hom_app] at h
  exact h.symm

/-- The same comparison acts on every original scalar map by the two actual inverse adjunctions. -/
private lemma cartesianTensorHomIso_map (A B : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ innerHom B ((exponentialFunctor A).obj Z)) :
    h ≫ (cartesianTensorHomIso A B).hom.app Z =
      scalarTensorHomEquiv (B ⊗ A) K Z
        ((cartesianScalarLeftIso A B).inv.app K ≫
          ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z).symm
            ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h)) := by
  have hc := cartesianTensorHomIso_characteristic A B K Z
    (((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z).symm
      ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hc
  exact hc.trans (congrArg
    (fun q => scalarTensorHomEquiv (B ⊗ A) K Z
      (q ≫ ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z).symm
        ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h)))
    (cartesianScalarLeftIso_inv_app A B K).symm)

omit smallD localD in
/-- The literal inverse left comparison is natural in the original source presheaf. -/
private lemma cartesianScalarLeftIso_source (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (K : SSet.{u}) :
    (cartesianScalarLeftIso A B').inv.app K ≫ A ◁ (scalarTensor.map b).app K =
      (scalarTensor.map (b ▷ A)).app K ≫ (cartesianScalarLeftIso A B).inv.app K := by
  simp only [cartesianScalarLeftIso_inv_app]
  change ((β_ A B').inv ▷ (Functor.const Dᵒᵖ).obj K ≫
      (α_ A B' ((Functor.const Dᵒᵖ).obj K)).hom) ≫
      A ◁ (b ▷ (Functor.const Dᵒᵖ).obj K) =
    (b ▷ A) ▷ (Functor.const Dᵒᵖ).obj K ≫
      ((β_ A B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
        (α_ A B ((Functor.const Dᵒᵖ).obj K)).hom)
  rw [Category.assoc, ← associator_naturality_middle,
    ← Category.assoc, ← comp_whiskerRight, ← braiding_inv_naturality_left,
    comp_whiskerRight, Category.assoc]

omit smallD localD in
/-- The same inverse left comparison is natural in the original exponential parameter. -/
private lemma cartesianScalarLeftIso_parameter {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (B : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (cartesianScalarLeftIso A' B).inv.app K ≫ a ▷ (scalarTensor.obj B).obj K =
      (scalarTensor.map (B ◁ a)).app K ≫ (cartesianScalarLeftIso A B).inv.app K := by
  simp only [cartesianScalarLeftIso_inv_app]
  change ((β_ A' B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
      (α_ A' B ((Functor.const Dᵒᵖ).obj K)).hom) ≫
      a ▷ (B ⊗ (Functor.const Dᵒᵖ).obj K) =
    (B ◁ a) ▷ (Functor.const Dᵒᵖ).obj K ≫
      ((β_ A B).inv ▷ (Functor.const Dᵒᵖ).obj K ≫
        (α_ A B ((Functor.const Dᵒᵖ).obj K)).hom)
  rw [Category.assoc, ← associator_naturality_left,
    ← Category.assoc, ← comp_whiskerRight, ← braiding_inv_naturality_right,
    comp_whiskerRight, Category.assoc]

section ExponentialSource

/-- The native mate of the original parameter map uses the two actual under-end adjunctions. -/
private def underSourceMate {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) :
    underHomFunctor.obj (op A) ⟶ underHomFunctor.obj (op A') :=
  conjugateEquiv (underHomAdjunction A) (underHomAdjunction A')
    ((tensoringLeft (SimplicialPresheaf.{u} D)).map a)

/-- The public native mate counit gives the original under-end inverse transposition. -/
private lemma underSourceMate_symm {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (X Z : SimplicialPresheaf.{u} D)
    (h : X ⟶ (underHomFunctor.obj (op A)).obj Z) :
    ((underHomAdjunction A').homEquiv X Z).symm (h ≫ (underSourceMate a).app Z) =
      a ▷ X ≫ ((underHomAdjunction A).homEquiv X Z).symm h := by
  have hc := conjugateEquiv_counit (underHomAdjunction A)
    (underHomAdjunction A') ((tensoringLeft (SimplicialPresheaf.{u} D)).map a) Z
  change A' ◁ (underSourceMate a).app Z ≫ (underHomAdjunction A').counit.app Z =
    a ▷ ((underHomFunctor.obj (op A)).obj Z) ≫
      (underHomAdjunction A).counit.app Z at hc
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  change A' ◁ (h ≫ (underSourceMate a).app Z) ≫
      (underHomAdjunction A').counit.app Z =
    a ▷ X ≫ (A ◁ h ≫ (underHomAdjunction A).counit.app Z)
  rw [whiskerLeft_comp, Category.assoc, hc,
    ← Category.assoc, whisker_exchange, Category.assoc]

/-- Native evaluation, scalar source transposition, and the actual under-end compare parameter
maps. -/
private lemma underExpEvaluationIso_source {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (d : D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ ((underHomFunctor.obj (op A)).obj Z).obj (op d)) :
    (h ≫ ((underSourceMate a).app Z).app (op d)) ≫
        (underExpEvaluationIso d A').hom.app Z =
      (h ≫ (underExpEvaluationIso d A).hom.app Z) ≫
        innerHomPre (discreteYoneda.obj d ◁ a) Z := by
  let t := ((discreteYonedaScalarAdjunction d).homEquiv K
    ((underHomFunctor.obj (op A)).obj Z)).symm h
  have hy : ((discreteYonedaScalarAdjunction d).homEquiv K
      ((underHomFunctor.obj (op A')).obj Z)).symm
        (h ≫ ((underSourceMate a).app Z).app (op d)) =
      t ≫ (underSourceMate a).app Z :=
    (discreteYonedaScalarAdjunction d).homEquiv_naturality_right_symm
      (X := K) (Y := (underHomFunctor.obj (op A)).obj Z)
      (Y' := (underHomFunctor.obj (op A')).obj Z) h ((underSourceMate a).app Z)
  have hu : ((underHomAdjunction A').homEquiv ((scalarTensor.obj
        (discreteYoneda.obj d)).obj K) Z).symm (t ≫ (underSourceMate a).app Z) =
      a ▷ (scalarTensor.obj (discreteYoneda.obj d)).obj K ≫
        ((underHomAdjunction A).homEquiv ((scalarTensor.obj
          (discreteYoneda.obj d)).obj K) Z).symm t :=
    underSourceMate_symm a _ Z t
  have hl : ((underExpEvaluationAdjunction d A').homEquiv K Z).symm
        (h ≫ ((underSourceMate a).app Z).app (op d)) =
      (cartesianScalarLeftIso A' (discreteYoneda.obj d)).inv.app K ≫
        ((underHomAdjunction A').homEquiv ((scalarTensor.obj
          (discreteYoneda.obj d)).obj K) Z).symm (t ≫ (underSourceMate a).app Z) := by
    rw [underExpEvaluationAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
      Adjunction.comp_homEquiv]
    change (cartesianScalarLeftIso A' (discreteYoneda.obj d)).inv.app K ≫
      ((underHomAdjunction A').homEquiv ((scalarTensor.obj
        (discreteYoneda.obj d)).obj K) Z).symm
        (((discreteYonedaScalarAdjunction d).homEquiv K
          ((underHomFunctor.obj (op A')).obj Z)).symm
            (h ≫ ((underSourceMate a).app Z).app (op d))) = _
    rw [hy]
  have hr : ((underExpEvaluationAdjunction d A).homEquiv K Z).symm h =
      (cartesianScalarLeftIso A (discreteYoneda.obj d)).inv.app K ≫
        ((underHomAdjunction A).homEquiv ((scalarTensor.obj
          (discreteYoneda.obj d)).obj K) Z).symm t := by
    rw [underExpEvaluationAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
      Adjunction.comp_homEquiv]
    rfl
  apply (scalarTensorHomEquiv (discreteYoneda.obj d ⊗ A') K Z).symm.injective
  calc
    _ = ((underExpEvaluationAdjunction d A').homEquiv K Z).symm
        (h ≫ ((underSourceMate a).app Z).app (op d)) :=
      underExpEvaluationIso_homEquiv_symm d A' K Z _
    _ = (cartesianScalarLeftIso A' (discreteYoneda.obj d)).inv.app K ≫
        ((underHomAdjunction A').homEquiv ((scalarTensor.obj
          (discreteYoneda.obj d)).obj K) Z).symm (t ≫ (underSourceMate a).app Z) := hl
    _ = (cartesianScalarLeftIso A' (discreteYoneda.obj d)).inv.app K ≫
        (a ▷ (scalarTensor.obj (discreteYoneda.obj d)).obj K ≫
          ((underHomAdjunction A).homEquiv ((scalarTensor.obj
            (discreteYoneda.obj d)).obj K) Z).symm t) :=
      congrArg ((cartesianScalarLeftIso A' (discreteYoneda.obj d)).inv.app K ≫ ·) hu
    _ = (scalarTensor.map (discreteYoneda.obj d ◁ a)).app K ≫
        ((cartesianScalarLeftIso A (discreteYoneda.obj d)).inv.app K ≫
          ((underHomAdjunction A).homEquiv ((scalarTensor.obj
            (discreteYoneda.obj d)).obj K) Z).symm t) := by
      rw [← Category.assoc, cartesianScalarLeftIso_parameter, Category.assoc]
    _ = (scalarTensor.map (discreteYoneda.obj d ◁ a)).app K ≫
        ((underExpEvaluationAdjunction d A).homEquiv K Z).symm h :=
      congrArg ((scalarTensor.map (discreteYoneda.obj d ◁ a)).app K ≫ ·) hr.symm
    _ = (scalarTensor.map (discreteYoneda.obj d ◁ a)).app K ≫
        (scalarTensorHomEquiv (discreteYoneda.obj d ⊗ A) K Z).symm
          (h ≫ (underExpEvaluationIso d A).hom.app Z) :=
      congrArg ((scalarTensor.map (discreteYoneda.obj d ◁ a)).app K ≫ ·)
        (underExpEvaluationIso_homEquiv_symm d A K Z h).symm
    _ = _ := (scalarTensorHomEquiv_source_symm (discreteYoneda.obj d ◁ a) K Z
        (h ≫ (underExpEvaluationIso d A).hom.app Z)).symm

/-- The actual exponential parameter map is the native mate transported by the actual comparison. -/
private lemma underExponentialIso_source {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (Z : SimplicialPresheaf.{u} D) :
    (underSourceMate a).app Z ≫ (underExponentialIso A').hom.app Z =
      (underExponentialIso A).hom.app Z ≫ exponentialSourceMap a Z := by
  apply NatTrans.ext
  funext d
  change ((underSourceMate a).app Z).app d ≫
      (underExpEvaluationIso d.unop A').hom.app Z =
    (underExpEvaluationIso d.unop A).hom.app Z ≫
      innerHomPre (discreteYoneda.obj d.unop ◁ a) Z
  have h := underExpEvaluationIso_source a d.unop
    (((underHomFunctor.obj (op A)).obj Z).obj d) Z (𝟙 _)
  rw [Category.id_comp, Category.id_comp] at h
  exact h

/-- The existing exponential source map preserves the original Cartesian transposition. -/
private lemma exponentialAdjunction_source {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (X Z : SimplicialPresheaf.{u} D) (f : A ⊗ X ⟶ Z) :
    (exponentialAdjunction A).homEquiv X Z f ≫ exponentialSourceMap a Z =
      (exponentialAdjunction A').homEquiv X Z (a ▷ X ≫ f) := by
  let s : (exponentialFunctor A).obj Z ⟶ (exponentialFunctor A').obj Z :=
    exponentialSourceMap a Z
  change (exponentialAdjunction A).homEquiv X Z f ≫ s = _
  have hu := underSourceMate_symm a X Z ((underHomAdjunction A).homEquiv X Z f)
  rw [Equiv.symm_apply_apply] at hu
  have hf : (underHomAdjunction A).homEquiv X Z f ≫ (underSourceMate a).app Z =
      (underHomAdjunction A').homEquiv X Z (a ▷ X ≫ f) := by
    apply ((underHomAdjunction A').homEquiv X Z).symm.injective
    rw [Equiv.symm_apply_apply]
    exact hu
  calc
    _ = ((underHomAdjunction A).homEquiv X Z f ≫
        (underExponentialIso A).hom.app Z) ≫ s :=
      congrArg (· ≫ s) (exponentialAdjunction_homEquiv A X Z f)
    _ = (underHomAdjunction A).homEquiv X Z f ≫
        ((underSourceMate a).app Z ≫ (underExponentialIso A').hom.app Z) := by
      exact (Category.assoc _ _ _).trans (congrArg
        ((underHomAdjunction A).homEquiv X Z f ≫ ·)
        (underExponentialIso_source a Z).symm)
    _ = (underHomAdjunction A').homEquiv X Z (a ▷ X ≫ f) ≫
        (underExponentialIso A').hom.app Z := by
      rw [← Category.assoc, hf]
    _ = _ := (exponentialAdjunction_homEquiv A' X Z (a ▷ X ≫ f)).symm

/-- The same existing parameter map preserves the original inverse Cartesian transposition. -/
private lemma exponentialAdjunction_source_symm {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (X Z : SimplicialPresheaf.{u} D)
    (h : X ⟶ (exponentialFunctor A).obj Z) :
    ((exponentialAdjunction A').homEquiv X Z).symm (h ≫ exponentialSourceMap a Z) =
      a ▷ X ≫ ((exponentialAdjunction A).homEquiv X Z).symm h := by
  have h := exponentialAdjunction_source a X Z
    (((exponentialAdjunction A).homEquiv X Z).symm h)
  rw [Equiv.apply_symm_apply] at h
  exact ((exponentialAdjunction A').homEquiv X Z).symm_apply_eq.mpr h

end ExponentialSource

/-- Scalar maps detect the source naturality of the actual transposition. -/
private lemma cartesianTensorHomIso_source_map (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ innerHom B ((exponentialFunctor A).obj Z)) :
    (h ≫ innerHomPre b ((exponentialFunctor A).obj Z)) ≫
        (cartesianTensorHomIso A B').hom.app Z =
      (h ≫ (cartesianTensorHomIso A B).hom.app Z) ≫ innerHomPre (b ▷ A) Z := by
  let γ : innerHom B ((exponentialFunctor A).obj Z) ⟶ innerHom (B ⊗ A) Z :=
    (cartesianTensorHomIso A B).hom.app Z
  let γ' : innerHom B' ((exponentialFunctor A).obj Z) ⟶ innerHom (B' ⊗ A) Z :=
    (cartesianTensorHomIso A B').hom.app Z
  change (h ≫ innerHomPre b ((exponentialFunctor A).obj Z)) ≫ γ' =
    (h ≫ γ) ≫ innerHomPre (b ▷ A) Z
  let g := ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z).symm
    ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h)
  have hc : ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B').obj K) Z).symm
      ((scalarTensorHomEquiv B' K ((exponentialFunctor A).obj Z)).symm
        (h ≫ innerHomPre b ((exponentialFunctor A).obj Z))) =
      A ◁ (scalarTensor.map b).app K ≫ g := by
    exact (congrArg
      ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B').obj K) Z).symm
      (scalarTensorHomEquiv_source_symm b K ((exponentialFunctor A).obj Z) h)).trans
      ((exponentialAdjunction A).homEquiv_naturality_left_symm
        (X := (scalarTensor.obj B).obj K) (X' := (scalarTensor.obj B').obj K)
        (Y := Z) ((scalarTensor.map b).app K)
        ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h))
  have hm : (cartesianScalarLeftIso A B').inv.app K ≫
      (A ◁ (scalarTensor.map b).app K ≫ g) =
      (scalarTensor.map (b ▷ A)).app K ≫
        ((cartesianScalarLeftIso A B).inv.app K ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (cartesianScalarLeftIso_source A b K)).trans
        (Category.assoc _ _ _))
  exact (cartesianTensorHomIso_map A B' K Z
      (h ≫ innerHomPre b ((exponentialFunctor A).obj Z))).trans
    ((congrArg (fun q => scalarTensorHomEquiv (B' ⊗ A) K Z
        ((cartesianScalarLeftIso A B').inv.app K ≫ q)) hc).trans
      ((congrArg (scalarTensorHomEquiv (B' ⊗ A) K Z) hm).trans
        ((scalarTensorHomEquiv_source (b ▷ A) K Z
            ((cartesianScalarLeftIso A B).inv.app K ≫ g)).trans
          (congrArg (· ≫ innerHomPre (b ▷ A) Z)
            (cartesianTensorHomIso_map A B K Z h).symm))))

/-- Scalar maps detect naturality in the existing original exponential parameter map. -/
private lemma cartesianTensorHomIso_parameter_map {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (B : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ innerHom B ((exponentialFunctor A).obj Z)) :
    (h ≫ innerHomPost B (exponentialSourceMap a Z)) ≫
        (cartesianTensorHomIso A' B).hom.app Z =
      (h ≫ (cartesianTensorHomIso A B).hom.app Z) ≫ innerHomPre (B ◁ a) Z := by
  let γ : innerHom B ((exponentialFunctor A).obj Z) ⟶ innerHom (B ⊗ A) Z :=
    (cartesianTensorHomIso A B).hom.app Z
  let γ' : innerHom B ((exponentialFunctor A').obj Z) ⟶ innerHom (B ⊗ A') Z :=
    (cartesianTensorHomIso A' B).hom.app Z
  change (h ≫ innerHomPost B (exponentialSourceMap a Z)) ≫ γ' =
    (h ≫ γ) ≫ innerHomPre (B ◁ a) Z
  let g := ((exponentialAdjunction A).homEquiv ((scalarTensor.obj B).obj K) Z).symm
    ((scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h)
  have hp : (scalarTensorHomEquiv B K ((exponentialFunctor A').obj Z)).symm
      (h ≫ innerHomPost B (exponentialSourceMap a Z)) =
      (scalarTensorHomEquiv B K ((exponentialFunctor A).obj Z)).symm h ≫
        exponentialSourceMap a Z := by
    have ht := (scalarTensorHomAdjunction B).homEquiv_naturality_right_symm
      (X := K) (Y := (exponentialFunctor A).obj Z)
      (Y' := (exponentialFunctor A').obj Z) h (exponentialSourceMap a Z)
    rw [scalarTensorHomAdjunction_homEquiv] at ht
    exact ht
  have hc : ((exponentialAdjunction A').homEquiv ((scalarTensor.obj B).obj K) Z).symm
      ((scalarTensorHomEquiv B K ((exponentialFunctor A').obj Z)).symm
        (h ≫ innerHomPost B (exponentialSourceMap a Z))) =
      a ▷ (scalarTensor.obj B).obj K ≫ g :=
    (congrArg ((exponentialAdjunction A').homEquiv ((scalarTensor.obj B).obj K) Z).symm hp).trans
      (exponentialAdjunction_source_symm a _ Z _)
  have hm : (cartesianScalarLeftIso A' B).inv.app K ≫
      (a ▷ (scalarTensor.obj B).obj K ≫ g) =
      (scalarTensor.map (B ◁ a)).app K ≫
        ((cartesianScalarLeftIso A B).inv.app K ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (cartesianScalarLeftIso_parameter a B K)).trans
        (Category.assoc _ _ _))
  exact (cartesianTensorHomIso_map A' B K Z
      (h ≫ innerHomPost B (exponentialSourceMap a Z))).trans
    ((congrArg (fun q => scalarTensorHomEquiv (B ⊗ A') K Z
        ((cartesianScalarLeftIso A' B).inv.app K ≫ q)) hc).trans
      ((congrArg (scalarTensorHomEquiv (B ⊗ A') K Z) hm).trans
        ((scalarTensorHomEquiv_source (B ◁ a) K Z
            ((cartesianScalarLeftIso A B).inv.app K ≫ g)).trans
          (congrArg (· ≫ innerHomPre (B ◁ a) Z)
            (cartesianTensorHomIso_map A B K Z h).symm))))

/-- The actual transposition is contravariantly natural in the original source map. -/
theorem cartesianTensorHomIso_naturality_source (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre b ((exponentialFunctor A).obj Z) ≫
        (cartesianTensorHomIso A B').hom.app Z =
      (cartesianTensorHomIso A B).hom.app Z ≫ innerHomPre (b ▷ A) Z := by
  have h := cartesianTensorHomIso_source_map A b
    (innerHom B ((exponentialFunctor A).obj Z)) Z (𝟙 _)
  exact (congrArg (· ≫ (cartesianTensorHomIso A B').hom.app Z)
      (Category.id_comp (innerHomPre b ((exponentialFunctor A).obj Z)))).symm.trans
    (h.trans (congrArg (· ≫ innerHomPre (b ▷ A) Z)
      (Category.id_comp ((cartesianTensorHomIso A B).hom.app Z))))

/-- The parameter equation uses the existing original exponential source map. -/
theorem cartesianTensorHomIso_naturality_parameter {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (B Z : SimplicialPresheaf.{u} D) :
    innerHomPost B (exponentialSourceMap a Z) ≫ (cartesianTensorHomIso A' B).hom.app Z =
      (cartesianTensorHomIso A B).hom.app Z ≫ innerHomPre (B ◁ a) Z := by
  have h := cartesianTensorHomIso_parameter_map a B
    (innerHom B ((exponentialFunctor A).obj Z)) Z (𝟙 _)
  exact (congrArg (· ≫ (cartesianTensorHomIso A' B).hom.app Z)
      (Category.id_comp (innerHomPost B (exponentialSourceMap a Z)))).symm.trans
    (h.trans (congrArg (· ≫ innerHomPre (B ◁ a) Z)
      (Category.id_comp ((cartesianTensorHomIso A B).hom.app Z))))

/-- The inverse equation retains both original inverse source components. -/
theorem cartesianTensorHomIso_inv_naturality_source (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre (b ▷ A) Z ≫ (cartesianTensorHomIso A B').inv.app Z =
      (cartesianTensorHomIso A B).inv.app Z ≫ innerHomPre b ((exponentialFunctor A).obj Z) := by
  apply ((cartesianTensorHomIso A B).app Z).eq_inv_comp.mpr
  have h := ((cartesianTensorHomIso A B').app Z).comp_inv_eq.mpr
    (cartesianTensorHomIso_naturality_source A b Z).symm
  exact (Category.assoc _ _ _).symm.trans h

/-- The inverse parameter equation retains the same original source map and inverse comparison. -/
theorem cartesianTensorHomIso_inv_naturality_parameter {A A' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (B Z : SimplicialPresheaf.{u} D) :
    innerHomPre (B ◁ a) Z ≫ (cartesianTensorHomIso A' B).inv.app Z =
      (cartesianTensorHomIso A B).inv.app Z ≫ innerHomPost B (exponentialSourceMap a Z) := by
  apply ((cartesianTensorHomIso A B).app Z).eq_inv_comp.mpr
  have h := ((cartesianTensorHomIso A' B).app Z).comp_inv_eq.mpr
    (cartesianTensorHomIso_naturality_parameter a B Z).symm
  exact (Category.assoc _ _ _).symm.trans h

/-- The two original restrictions are isomorphic as entire arrows, with both actual endpoints. -/
def cartesianTensorHomArrowIso (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (innerHomPre b ((exponentialFunctor A).obj Z)) ≅
      Arrow.mk (innerHomPre (b ▷ A) Z) :=
  Arrow.isoMk ((cartesianTensorHomIso A B).app Z) ((cartesianTensorHomIso A B').app Z)
    (cartesianTensorHomIso_naturality_source A b Z).symm

/-- The whole-arrow hom has the original source comparison as its left leg. -/
theorem cartesianTensorHomArrowIso_hom_left (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    (cartesianTensorHomArrowIso A b Z).hom.left = (cartesianTensorHomIso A B).hom.app Z := rfl

/-- The whole-arrow hom has the original target comparison as its right leg. -/
theorem cartesianTensorHomArrowIso_hom_right (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    (cartesianTensorHomArrowIso A b Z).hom.right = (cartesianTensorHomIso A B').hom.app Z := rfl

/-- The inverse whole-arrow left leg is the same original inverse comparison. -/
theorem cartesianTensorHomArrowIso_inv_left (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    (cartesianTensorHomArrowIso A b Z).inv.left = (cartesianTensorHomIso A B).inv.app Z := rfl

/-- The inverse whole-arrow right leg is the same original inverse comparison. -/
theorem cartesianTensorHomArrowIso_inv_right (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    (cartesianTensorHomArrowIso A b Z).inv.right = (cartesianTensorHomIso A B').inv.app Z := rfl

/-- Scalar realization weakness is equivalent for the two literal original restrictions. -/
theorem cartesianTensorHom_weak_iff (A : SimplicialPresheaf.{u} D)
    {B B' : SimplicialPresheaf.{u} D} (b : B' ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (innerHomPre b ((exponentialFunctor A).obj Z)) ↔
      SSet.realizationWeakEquivalences (innerHomPre (b ▷ A) Z) :=
  SSet.realizationWeakEquivalences.arrow_mk_iso_iff (cartesianTensorHomArrowIso A b Z)

namespace InjectiveKan

/-- Every original raw local test on the actual exponential is the same tensor-family test. -/
theorem isRawLocal_exponential_iff {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A Z : SimplicialPresheaf.{u} D) :
    isRawLocal S ((exponentialFunctor A).obj Z) ↔
      isRawLocal (fun j => Arrow.mk ((S j).hom ▷ A)) Z := by
  change (∀ j, SSet.realizationWeakEquivalences
    (innerHomPre (S j).hom ((exponentialFunctor A).obj Z))) ↔
    ∀ j, SSet.realizationWeakEquivalences (innerHomPre ((S j).hom ▷ A) Z)
  exact forall_congr' (fun j => cartesianTensorHom_weak_iff A (S j).hom Z)

end InjectiveKan

end SimplicialPresheaf
