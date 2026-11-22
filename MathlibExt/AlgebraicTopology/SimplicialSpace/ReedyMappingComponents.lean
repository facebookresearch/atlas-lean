/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerStrongDeformationWeakEquivalence
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Inner mapping components and Reedy left homotopy

The existing inner one-simplex precylinder is a good native cylinder for the
actual named Reedy model. Components of the original inner mapping end are
its native left-homotopy classes, naturally in both original variables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner

namespace SimplicialSpace.ReedyModel

section
attribute [local instance] modelCategory

/-- The native cylinder whose underlying data are the existing inner
one-simplex precylinder, for the same named Reedy model. -/
def innerOneSimplexCylinder (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Cylinder X := by
  exact
    { __ := innerOneSimplexPrecylinder.app X
      weakEquivalence_π :=
        (HomotopicalAlgebra.weakEquivalence_iff _).mpr
          (innerOneSimplex_projection_weakEquivalence X) }

/-- The cylinder retains the complete original precylinder, including its
two ordered endpoints and projection. -/
theorem innerOneSimplexCylinder_toPrecylinder (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (innerOneSimplexCylinder X).toPrecylinder =
      innerOneSimplexPrecylinder.app X := rfl

@[reassoc]
private lemma inl_boundaryIso (X : SimplicialSpace.{u}) :
    coprod.inl ≫ (innerOneSimplexBoundaryDomainIso X).hom =
      innerTensorUnitIso.inv.app X ≫ (innerTensorBifunctor.obj X).map coprod.inl := by
  simp only [innerOneSimplexBoundaryDomainIso, Iso.trans_hom, asIso_hom]
  simp only [coprod.inl_map_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k => innerTensorUnitIso.inv.app X ≫ k)
    (inl_coprodComparison (innerTensorBifunctor.obj X) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

@[reassoc]
private lemma inr_boundaryIso (X : SimplicialSpace.{u}) :
    coprod.inr ≫ (innerOneSimplexBoundaryDomainIso X).hom =
      innerTensorUnitIso.inv.app X ≫ (innerTensorBifunctor.obj X).map coprod.inr := by
  simp only [innerOneSimplexBoundaryDomainIso, Iso.trans_hom, asIso_hom]
  simp only [coprod.inr_map_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k => innerTensorUnitIso.inv.app X ≫ k)
    (inr_coprodComparison (innerTensorBifunctor.obj X) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

private lemma boundary_eq (X : SimplicialSpace.{u}) :
    (innerOneSimplexBoundaryDomainIso X).hom ≫
        (innerTensorBifunctor.obj X).map innerOneSimplexUnitBoundary =
      (innerOneSimplexPrecylinder.app X).i := by
  change _ = coprod.desc ((innerOneSimplexEndpoint 0).app X)
    ((innerOneSimplexEndpoint 1).app X)
  apply coprod.hom_ext
  · rw [coprod.inl_desc, inl_boundaryIso_assoc,
      ← (innerTensorBifunctor.obj X).map_comp,
      inl_innerOneSimplexUnitBoundary]
    rfl
  · rw [coprod.inr_desc, inr_boundaryIso_assoc,
      ← (innerTensorBifunctor.obj X).map_comp,
      inr_innerOneSimplexUnitBoundary]
    rfl

/-- The same actual inner one-simplex cylinder has a cofibrant boundary. -/
theorem innerOneSimplexCylinder_isGood (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (innerOneSimplexCylinder X).IsGood := by
  constructor
  change Cofibration (innerOneSimplexPrecylinder.app X).i
  rw [← boundary_eq X]
  apply (SimplicialSpace.ReedyModel.cofibration_iff _).mpr
  have hmono : Mono ((innerTensorBifunctor.obj X).map innerOneSimplexUnitBoundary) := by
    apply (mono_forget_map_iff _).mp
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro m
    change Mono ((tensorLeft (X.diagram.obj m)).map innerOneSimplexUnitBoundary)
    infer_instance
  let _ := hmono
  infer_instance

private abbrev mappingObject (X Y : SimplicialSpace.{u}) : SSet.{u} :=
  (innerHomFunctor.obj (op X)).obj Y

private def degreeEquiv (X Y : SimplicialSpace.{u}) (n : SimplexCategory) :
    (mappingObject X Y).obj (op n) ≃ ((innerTensor (SSet.stdSimplex.obj n)).obj X ⟶ Y) :=
  (SSet.yonedaEquiv (X := mappingObject X Y) (n := n)).symm.trans
    (innerTensorHomEquiv (SSet.stdSimplex.obj n) X Y).symm

private def zeroTensorIso : innerTensor (Δ[0] : SSet.{u}) ≅ 𝟭 SimplicialSpace.{u} :=
  innerTensorBifunctor.flip.mapIso innerOneSimplexUnitZeroIso.symm ≪≫ innerTensorUnitIso

private lemma tensorHom_degree (X Y : SimplicialSpace.{u}) (n : SimplexCategory)
    (z : (mappingObject X Y).obj (op n)) :
    innerTensorHomEquiv (SSet.stdSimplex.obj n) X Y (degreeEquiv X Y n z) =
      SSet.yonedaEquiv.symm z := by
  exact (innerTensorHomEquiv (SSet.stdSimplex.obj n) X Y).apply_symm_apply _

private lemma tensorHom_unit (X Y : SimplicialSpace.{u}) (f : X ⟶ Y) :
    innerTensorHomEquiv (𝟙_ SSet.{u}) X Y (innerTensorUnitIso.hom.app X ≫ f) =
      eHomEquiv SSet.{u} f := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} := enrichedCategorySelf _
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} := enrichedOrdinaryCategorySelf _
  apply innerHom_ext X Y
  intro m
  rw [innerTensorHomEquiv_π]
  change curry ((ρ_ (X.diagram.obj m)).hom ≫ f.hom.app m) =
    Enriched.FunctorCategory.homEquiv SSet.{u} f.hom ≫
      Enriched.FunctorCategory.enrichedHomπ SSet.{u} X.diagram Y.diagram m
  rw [Enriched.FunctorCategory.homEquiv_apply_π]
  rfl

private lemma vertex_yoneda (X Y : SimplicialSpace.{u}) (f : X ⟶ Y) :
    SSet.yonedaEquiv.symm (innerHomEquiv X Y f) =
      innerOneSimplexUnitZeroIso.inv ≫ eHomEquiv SSet.{u} f := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  change (eHomEquiv SSet.{u} f).app (op ⦋0⦌) PUnit.unit =
    (eHomEquiv SSet.{u} f).app (op ⦋0⦌) _
  let _ : Subsingleton ((𝟙_ SSet.{u}).obj (op ⦋0⦌)) :=
    inferInstanceAs (Subsingleton PUnit.{u + 1})
  exact congrArg ((eHomEquiv SSet.{u} f).app (op ⦋0⦌)) (Subsingleton.elim _ _)

private lemma degree_zero (X Y : SimplicialSpace.{u})
    (z : (mappingObject X Y).obj (op ⦋0⦌)) :
    degreeEquiv X Y ⦋0⦌ z =
      zeroTensorIso.hom.app X ≫ (innerHomEquiv X Y).symm z := by
  obtain ⟨f, rfl⟩ := (innerHomEquiv X Y).surjective z
  rw [Equiv.symm_apply_apply]
  apply (innerTensorHomEquiv (Δ[0] : SSet.{u}) X Y).injective
  rw [tensorHom_degree]
  change _ = innerTensorHomEquiv (Δ[0] : SSet.{u}) X Y
    ((innerTensorBifunctor.obj X).map innerOneSimplexUnitZeroIso.inv ≫
      (innerTensorUnitIso.hom.app X ≫ f))
  rw [innerTensorHomEquiv_scalar, tensorHom_unit]
  exact vertex_yoneda X Y f

private lemma degree_operator (X Y : SimplicialSpace.{u})
    {m n : SimplexCategory} (a : m ⟶ n)
    (z : (mappingObject X Y).obj (op n)) :
    degreeEquiv X Y m ((mappingObject X Y).map a.op z) =
      (innerTensorBifunctor.obj X).map (SSet.stdSimplex.map a) ≫ degreeEquiv X Y n z := by
  apply (innerTensorHomEquiv (SSet.stdSimplex.obj m) X Y).injective
  rw [tensorHom_degree, innerTensorHomEquiv_scalar, tensorHom_degree]
  change _ = SSet.stdSimplex.map a ≫ SSet.yonedaEquiv.symm z
  exact (SSet.yonedaEquiv_symm_naturality_left a z).symm

private lemma degree_source {X' X Y : SimplicialSpace.{u}} (a : X' ⟶ X)
    (n : SimplexCategory) (z : (mappingObject X Y).obj (op n)) :
    degreeEquiv X' Y n (((innerHomFunctor.map a.op).app Y).app (op n) z) =
      (innerTensor (SSet.stdSimplex.obj n)).map a ≫ degreeEquiv X Y n z := by
  apply (innerTensorHomEquiv (SSet.stdSimplex.obj n) X' Y).injective
  rw [tensorHom_degree, innerTensorHomEquiv_source, tensorHom_degree]
  change _ = SSet.yonedaEquiv.symm z ≫ (innerHomFunctor.map a.op).app Y
  exact (SSet.yonedaEquiv_symm_comp z ((innerHomFunctor.map a.op).app Y)).symm

private lemma degree_target {X Y Y' : SimplicialSpace.{u}} (b : Y ⟶ Y')
    (n : SimplexCategory) (z : (mappingObject X Y).obj (op n)) :
    degreeEquiv X Y' n (((innerHomFunctor.obj (op X)).map b).app (op n) z) =
      degreeEquiv X Y n z ≫ b := by
  apply (innerTensorHomEquiv (SSet.stdSimplex.obj n) X Y').injective
  rw [tensorHom_degree, innerTensorHomEquiv_target, tensorHom_degree]
  change _ = SSet.yonedaEquiv.symm z ≫ (innerHomFunctor.obj (op X)).map b
  exact (SSet.yonedaEquiv_symm_comp z ((innerHomFunctor.obj (op X)).map b)).symm

private lemma endpoint_degree (X Y : SimplicialSpace.{u}) (ε : Fin 2)
    (z : (mappingObject X Y).obj (op ⦋1⦌)) :
    (innerOneSimplexPrecylinder.app X).endpoint ε ≫ degreeEquiv X Y ⦋1⦌ z =
      (innerHomEquiv X Y).symm ((mappingObject X Y).δ (Fin.rev ε) z) := by
  have h : (zeroTensorIso.app X).inv ≫
      ((innerTensorBifunctor.obj X).map (SSet.stdSimplex.map (SimplexCategory.δ (Fin.rev ε))) ≫
        degreeEquiv X Y ⦋1⦌ z) =
      (innerHomEquiv X Y).symm ((mappingObject X Y).δ (Fin.rev ε) z) := by
    rw [← degree_operator, degree_zero]
    change (zeroTensorIso.app X).inv ≫ ((zeroTensorIso.app X).hom ≫ _) = _
    simp
    rfl
  rw [Precylinder.app_endpoint, innerOneSimplexPrecylinder_endpoint]
  simp only [innerOneSimplexUnitPoint, Category.assoc]
  change (zeroTensorIso.app X).inv ≫
    ((innerTensorBifunctor.obj X).map (SSet.stdSimplex.map (SimplexCategory.δ (Fin.rev ε))) ≫
      degreeEquiv X Y ⦋1⦌ z) = _
  exact h

private def edgeHomotopy {X Y : SimplicialSpace.{u}}
    {z₀ z₁ : (mappingObject X Y).obj (op ⦋0⦌)}
    (e : (mappingObject X Y).Edge z₀ z₁) :
    (innerOneSimplexCylinder X).LeftHomotopy
      ((innerHomEquiv X Y).symm z₀) ((innerHomEquiv X Y).symm z₁) where
  h := degreeEquiv X Y ⦋1⦌ e.edge
  h₀ := by
    have h := endpoint_degree X Y 0 e.edge
    change (innerOneSimplexCylinder X).i₀ ≫ degreeEquiv X Y ⦋1⦌ e.edge =
      (innerHomEquiv X Y).symm ((mappingObject X Y).δ (1 : Fin 2) e.edge) at h
    rw [e.src_eq] at h
    exact h
  h₁ := by
    have h := endpoint_degree X Y 1 e.edge
    change (innerOneSimplexCylinder X).i₁ ≫ degreeEquiv X Y ⦋1⦌ e.edge =
      (innerHomEquiv X Y).symm ((mappingObject X Y).δ (0 : Fin 2) e.edge) at h
    rw [e.tgt_eq] at h
    exact h

private def homotopyEdge {X Y : SimplicialSpace.{u}} {f g : X ⟶ Y}
    (h : (innerOneSimplexCylinder X).LeftHomotopy f g) :
    (mappingObject X Y).Edge (innerHomEquiv X Y f) (innerHomEquiv X Y g) where
  edge := (degreeEquiv X Y ⦋1⦌).symm h.h
  src_eq := by
    apply (innerHomEquiv X Y).symm.injective
    rw [Equiv.symm_apply_apply]
    have hh := endpoint_degree X Y 0 ((degreeEquiv X Y ⦋1⦌).symm h.h)
    change (innerOneSimplexCylinder X).i₀ ≫
      degreeEquiv X Y ⦋1⦌ ((degreeEquiv X Y ⦋1⦌).symm h.h) =
        (innerHomEquiv X Y).symm ((mappingObject X Y).δ (1 : Fin 2) _) at hh
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans h.h₀
  tgt_eq := by
    apply (innerHomEquiv X Y).symm.injective
    rw [Equiv.symm_apply_apply]
    have hh := endpoint_degree X Y 1 ((degreeEquiv X Y ⦋1⦌).symm h.h)
    change (innerOneSimplexCylinder X).i₁ ≫
      degreeEquiv X Y ⦋1⦌ ((degreeEquiv X Y ⦋1⦌).symm h.h) =
        (innerHomEquiv X Y).symm ((mappingObject X Y).δ (0 : Fin 2) _) at hh
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm.trans h.h₁

private def relationEdge {X Y : SimplicialSpace.{u}} [IsCofibrant X] [IsFibrant Y]
    {f g : X ⟶ Y} (h : LeftHomotopyRel f g) :
    (mappingObject X Y).Edge (innerHomEquiv X Y f) (innerHomEquiv X Y g) := by
  let _ : (innerOneSimplexCylinder X).IsGood := innerOneSimplexCylinder_isGood X
  exact homotopyEdge (h.leftHomotopy (innerOneSimplexCylinder X))

private def toClass (X Y : SimplicialSpace.{u}) :
    SSet.π₀ (mappingObject X Y) → LeftHomotopyClass X Y :=
  SSet.π₀.lift (fun z => LeftHomotopyClass.mk ((innerHomEquiv X Y).symm z))
    (fun _ _ e => LeftHomotopyClass.sound (edgeHomotopy e).leftHomotopyRel)

private def fromClass (X Y : SimplicialSpace.{u}) [IsCofibrant X] [IsFibrant Y] :
    LeftHomotopyClass X Y → SSet.π₀ (mappingObject X Y) :=
  Quot.lift (fun f => SSet.π₀.mk (innerHomEquiv X Y f))
    (fun _ _ h => SSet.π₀.sound (relationEdge h))

/-- Components of the original inner mapping end are exactly left-homotopy
classes for the actual named Reedy model. -/
def mappingComponentEquiv (X Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X] [IsFibrant Y],
      SSet.π₀ ((innerHomFunctor.obj (op X)).obj Y) ≃ LeftHomotopyClass X Y := by
  intro hX hY
  exact
    { toFun := toClass X Y
      invFun := fromClass X Y
      left_inv := by
        intro q
        induction q using SSet.π₀.rec with
        | mk z =>
          change SSet.π₀.mk (innerHomEquiv X Y ((innerHomEquiv X Y).symm z)) = SSet.π₀.mk z
          rw [Equiv.apply_symm_apply]
      right_inv := by
        intro q
        obtain ⟨f, rfl⟩ := q.mk_surjective
        change LeftHomotopyClass.mk ((innerHomEquiv X Y).symm (innerHomEquiv X Y f)) =
          LeftHomotopyClass.mk f
        rw [Equiv.symm_apply_apply] }

/-- The component represented by an original vertex goes to its original
ordinary-map class. -/
@[simp]
theorem mappingComponentEquiv_mk (X Y : SimplicialSpace.{u})
    (z : ((innerHomFunctor.obj (op X)).obj Y).obj (op ⦋0⦌)) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X] [IsFibrant Y],
      mappingComponentEquiv X Y (SSet.π₀.mk z) =
        LeftHomotopyClass.mk ((innerHomEquiv X Y).symm z) := by
  intro hX hY
  rfl

/-- An original ordinary-map class goes to its represented vertex component. -/
@[simp]
theorem mappingComponentEquiv_symm_mk (X Y : SimplicialSpace.{u}) (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X] [IsFibrant Y],
      (mappingComponentEquiv X Y).symm (LeftHomotopyClass.mk f) =
        SSet.π₀.mk (innerHomEquiv X Y f) := by
  intro hX hY
  rfl

/-- Equality of represented components is precisely native model left homotopy. -/
theorem mappingComponent_mk_eq_iff (X Y : SimplicialSpace.{u}) (f g : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X] [IsFibrant Y],
      SSet.π₀.mk (innerHomEquiv X Y f) = SSet.π₀.mk (innerHomEquiv X Y g) ↔
        LeftHomotopyRel f g := by
  intro hX hY
  constructor
  · intro h
    have h' := congrArg (mappingComponentEquiv X Y) h
    rw [mappingComponentEquiv_mk, mappingComponentEquiv_mk] at h'
    have hc : LeftHomotopyClass.mk f = LeftHomotopyClass.mk g := by
      simpa only [Equiv.symm_apply_apply] using h'
    exact (LeftHomotopyClass.mk_eq_mk_iff f g).mp hc
  · intro h
    apply (mappingComponentEquiv X Y).injective
    rw [mappingComponentEquiv_mk, mappingComponentEquiv_mk]
    simpa only [Equiv.symm_apply_apply] using LeftHomotopyClass.sound h

private lemma zero_source {X' X Y : SimplicialSpace.{u}} (a : X' ⟶ X)
    (z : (mappingObject X Y).obj (op ⦋0⦌)) :
    (innerHomEquiv X' Y).symm (((innerHomFunctor.map a.op).app Y).app (op ⦋0⦌) z) =
      a ≫ (innerHomEquiv X Y).symm z := by
  apply (cancel_epi (zeroTensorIso.hom.app X')).mp
  have h := degree_source a ⦋0⦌ z
  rw [degree_zero, degree_zero] at h
  rw [← Category.assoc, zeroTensorIso.hom.naturality a, Functor.id_map, Category.assoc] at h
  exact h

private lemma zero_target {X Y Y' : SimplicialSpace.{u}} (b : Y ⟶ Y')
    (z : (mappingObject X Y).obj (op ⦋0⦌)) :
    (innerHomEquiv X Y').symm (((innerHomFunctor.obj (op X)).map b).app (op ⦋0⦌) z) =
      (innerHomEquiv X Y).symm z ≫ b := by
  apply (cancel_epi (zeroTensorIso.hom.app X)).mp
  have h := degree_target b ⦋0⦌ z
  simpa only [degree_zero, Category.assoc] using h

/-- Original source precomposition on native left-homotopy classes, for a
fibrant target in the same named Reedy model. -/
def leftHomotopyClassPrecomp {X' X Y : SimplicialSpace.{u}} (a : X' ⟶ X) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsFibrant Y], LeftHomotopyClass X Y → LeftHomotopyClass X' Y := by
  intro hY
  exact Quot.lift (fun f => LeftHomotopyClass.mk (a ≫ f))
    (fun _ _ h => LeftHomotopyClass.sound (h.precomp a))

/-- Source precomposition retains the original ordinary representative. -/
@[simp]
theorem leftHomotopyClassPrecomp_mk {X' X Y : SimplicialSpace.{u}}
    (a : X' ⟶ X) (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsFibrant Y],
      leftHomotopyClassPrecomp a (LeftHomotopyClass.mk f) =
        LeftHomotopyClass.mk (a ≫ f) := by
  intro hY
  rfl

/-- Original contravariant source composition agrees on mapping components
and native left-homotopy classes. -/
theorem mappingComponentEquiv_precompose {X' X Y : SimplicialSpace.{u}}
    (a : X' ⟶ X) (q : SSet.π₀ ((innerHomFunctor.obj (op X)).obj Y)) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X'] [IsCofibrant X] [IsFibrant Y],
      mappingComponentEquiv X' Y (SSet.mapπ₀ ((innerHomFunctor.map a.op).app Y) q) =
        leftHomotopyClassPrecomp a (mappingComponentEquiv X Y q) := by
  intro hX' hX hY
  induction q using SSet.π₀.rec with
  | mk z =>
    rw [SSet.mapπ₀_mk, mappingComponentEquiv_mk, mappingComponentEquiv_mk,
      leftHomotopyClassPrecomp_mk]
    exact congrArg LeftHomotopyClass.mk (zero_source a z)

/-- Original covariant target composition agrees on mapping components
and native left-homotopy classes. -/
theorem mappingComponentEquiv_postcompose {X Y Y' : SimplicialSpace.{u}}
    (b : Y ⟶ Y') (q : SSet.π₀ ((innerHomFunctor.obj (op X)).obj Y)) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    ∀ [IsCofibrant X] [IsFibrant Y] [IsFibrant Y'],
      mappingComponentEquiv X Y' (SSet.mapπ₀ ((innerHomFunctor.obj (op X)).map b) q) =
        (mappingComponentEquiv X Y q).postcomp b := by
  intro hX hY hY'
  induction q using SSet.π₀.rec with
  | mk z =>
    rw [SSet.mapπ₀_mk, mappingComponentEquiv_mk, mappingComponentEquiv_mk,
      LeftHomotopyClass.postcomp_mk]
    exact congrArg LeftHomotopyClass.mk (zero_target b z)

end
end SimplicialSpace.ReedyModel
