/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.TrivialCofibrationStrongDeformation
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerSM7

/-!
# The inner one-simplex cylinder on simplicial spaces

The standard one-simplex acts in the inner simplicial direction.  Its two
vertices and projection to the tensor unit give a native functorial
precylinder.  The boundary corner of a Reedy trivial cofibration is the actual
inner pushout-product with the two-vertex boundary, hence is again a trivial
cofibration.  The generic model-category constructor then supplies strict
strong deformation data between fibrant objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalCategory CartesianMonoidalCategory
open scoped MonoidalCategory Simplicial SimplicialSpace.Inner

namespace SimplicialSpace

/-- The simplicial tensor unit is the standard zero-simplex. -/
def innerOneSimplexUnitZeroIso :
    (𝟙_ SSet.{u}) ≅ (Δ[0] : SSet.{u}) :=
  isTerminalTensorUnit.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀.{u}

/-- Tensoring in the inner direction with the simplicial tensor unit is
canonically the identity. -/
def innerTensorUnitIso :
    innerTensor (𝟙_ SSet.{u}) ≅ 𝟭 SimplicialSpace.{u} :=
  NatIso.ofComponents
    (fun X => InducedCategory.isoMk
      (Functor.isoWhiskerLeft X.diagram (rightUnitorNatIso SSet.{u})))
    (by
      intro X Y f
      apply InducedCategory.hom_ext
      apply NatTrans.ext
      funext m
      exact MonoidalCategory.rightUnitor_naturality (f.hom.app m))

/-- Vertex `ε` of the inner standard one-simplex, with the monoidal unit as
domain.  Endpoint `0` is the face opposite `1`, and endpoint `1` is the face
opposite `0`. -/
def innerOneSimplexUnitPoint (ε : Fin 2) :
    (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  innerOneSimplexUnitZeroIso.hom ≫
    SSet.stdSimplex.δ (Fin.rev ε)

/-- Endpoint zero is the face opposite vertex `1`, hence the initial vertex of
the standard one-simplex. -/
@[simp]
theorem innerOneSimplexUnitPoint_zero :
    innerOneSimplexUnitPoint (0 : Fin 2) =
      innerOneSimplexUnitZeroIso.hom ≫ SSet.stdSimplex.δ (1 : Fin 2) :=
  rfl

/-- Endpoint one is the face opposite vertex `0`, hence the terminal vertex of
the standard one-simplex. -/
@[simp]
theorem innerOneSimplexUnitPoint_one :
    innerOneSimplexUnitPoint (1 : Fin 2) =
      innerOneSimplexUnitZeroIso.hom ≫ SSet.stdSimplex.δ (0 : Fin 2) :=
  rfl

/-- The endpoint transformation for the inner one-simplex cylinder. -/
def innerOneSimplexEndpoint (ε : Fin 2) :
    𝟭 SimplicialSpace.{u} ⟶ innerTensor (Δ[1] : SSet.{u}) where
  app X := innerTensorUnitIso.inv.app X ≫
    (innerTensorBifunctor.obj X).map (innerOneSimplexUnitPoint ε)
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    change f.hom.app m ≫ (ρ_ (Y.diagram.obj m)).inv ≫
        (Y.diagram.obj m ◁ innerOneSimplexUnitPoint ε) =
      (ρ_ (X.diagram.obj m)).inv ≫
        (X.diagram.obj m ◁ innerOneSimplexUnitPoint ε) ≫
          (f.hom.app m ▷ (Δ[1] : SSet.{u}))
    calc
      _ = ((ρ_ (X.diagram.obj m)).inv ≫
          (f.hom.app m ▷ (𝟙_ SSet.{u}))) ≫
            (Y.diagram.obj m ◁ innerOneSimplexUnitPoint ε) := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (Y.diagram.obj m ◁ innerOneSimplexUnitPoint ε))
          (rightUnitor_inv_naturality (f.hom.app m))
      _ = (ρ_ (X.diagram.obj m)).inv ≫
          ((X.diagram.obj m ◁ innerOneSimplexUnitPoint ε) ≫
            (f.hom.app m ▷ (Δ[1] : SSet.{u}))) := by
        simpa only [Category.assoc] using congrArg
          (fun k => (ρ_ (X.diagram.obj m)).inv ≫ k)
          (whisker_exchange (f.hom.app m) (innerOneSimplexUnitPoint ε)).symm
      _ = _ := rfl

/-- Projection from the inner one-simplex cylinder to the original space. -/
def innerOneSimplexProjection :
    innerTensor (Δ[1] : SSet.{u}) ⟶ 𝟭 SimplicialSpace.{u} where
  app X := (innerTensorBifunctor.obj X).map (toUnit (Δ[1] : SSet.{u})) ≫
    innerTensorUnitIso.hom.app X
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    change (f.hom.app m ▷ (Δ[1] : SSet.{u})) ≫
        (Y.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
          (ρ_ (Y.diagram.obj m)).hom =
      (X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
        (ρ_ (X.diagram.obj m)).hom ≫ f.hom.app m
    calc
      _ = ((X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
          (f.hom.app m ▷ (𝟙_ SSet.{u}))) ≫
            (ρ_ (Y.diagram.obj m)).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (ρ_ (Y.diagram.obj m)).hom)
          (whisker_exchange (f.hom.app m) (toUnit (Δ[1] : SSet.{u}))).symm
      _ = (X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
          ((ρ_ (X.diagram.obj m)).hom ≫ f.hom.app m) := by
        simpa only [Category.assoc] using congrArg
          (fun k => (X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫ k)
          (rightUnitor_naturality (f.hom.app m))
      _ = _ := rfl

/-- The functorial precylinder given by tensoring with the inner standard
one-simplex. -/
def innerOneSimplexPrecylinder : Precylinder (𝟭 SimplicialSpace.{u}) where
  I := innerTensor (Δ[1] : SSet.{u})
  i₀ := innerOneSimplexEndpoint 0
  i₁ := innerOneSimplexEndpoint 1
  π := innerOneSimplexProjection
  i₀_π := by
    ext X
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    change (ρ_ (X.diagram.obj m)).inv ≫
        (X.diagram.obj m ◁ innerOneSimplexUnitPoint 0) ≫
          (X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
            (ρ_ (X.diagram.obj m)).hom = 𝟙 (X.diagram.obj m)
    have h : innerOneSimplexUnitPoint (0 : Fin 2) ≫
        toUnit (Δ[1] : SSet.{u}) = 𝟙 (𝟙_ SSet.{u}) :=
      isTerminalTensorUnit.hom_ext _ _
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h]
    simp
  i₁_π := by
    ext X
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    change (ρ_ (X.diagram.obj m)).inv ≫
        (X.diagram.obj m ◁ innerOneSimplexUnitPoint 1) ≫
          (X.diagram.obj m ◁ toUnit (Δ[1] : SSet.{u})) ≫
            (ρ_ (X.diagram.obj m)).hom = 𝟙 (X.diagram.obj m)
    have h : innerOneSimplexUnitPoint (1 : Fin 2) ≫
        toUnit (Δ[1] : SSet.{u}) = 𝟙 (𝟙_ SSet.{u}) :=
      isTerminalTensorUnit.hom_ext _ _
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h]
    simp

@[simp]
theorem innerOneSimplexPrecylinder_I :
    innerOneSimplexPrecylinder.{u}.I = innerTensor (Δ[1] : SSet.{u}) :=
  rfl

@[simp]
theorem innerOneSimplexPrecylinder_endpoint (X : SimplicialSpace.{u})
    (ε : Fin 2) :
    (innerOneSimplexPrecylinder.endpoint ε).app X =
      innerTensorUnitIso.inv.app X ≫
        (innerTensorBifunctor.obj X).map (innerOneSimplexUnitPoint ε) := by
  fin_cases ε <;> rfl

@[simp]
theorem innerOneSimplexPrecylinder_projection (X : SimplicialSpace.{u}) :
    (innerOneSimplexPrecylinder.app X).π =
      (innerTensorBifunctor.obj X).map (toUnit (Δ[1] : SSet.{u})) ≫
        innerTensorUnitIso.hom.app X :=
  rfl

private def innerOneSimplexBoundaryFaces :
    Fin 2 → ((Δ[0] : SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) :=
  fun j => if j = 0 then
    innerOneSimplexUnitZeroIso.inv ≫
      (coprod.inr : (𝟙_ SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))
  else
    innerOneSimplexUnitZeroIso.inv ≫
      (coprod.inl : (𝟙_ SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))

private def innerOneSimplexBoundaryDomainInv :
    (∂Δ[1] : SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) := by
  have h : SSet.boundary.IsCompatible innerOneSimplexBoundaryFaces.{u} := by
    rw [SSet.boundary.isCompatible_zero_iff_true]
    trivial
  exact h.desc

@[reassoc (attr := simp)]
private theorem boundary_ι_zero_innerOneSimplexBoundaryDomainInv :
    SSet.boundary.ι (0 : Fin 2) ≫ innerOneSimplexBoundaryDomainInv =
      innerOneSimplexUnitZeroIso.inv ≫
        (coprod.inr : (𝟙_ SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) := by
  simp [innerOneSimplexBoundaryDomainInv, innerOneSimplexBoundaryFaces]

@[reassoc (attr := simp)]
private theorem boundary_ι_one_innerOneSimplexBoundaryDomainInv :
    SSet.boundary.ι (1 : Fin 2) ≫ innerOneSimplexBoundaryDomainInv =
      innerOneSimplexUnitZeroIso.inv ≫
        (coprod.inl : (𝟙_ SSet.{u}) ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) := by
  simp [innerOneSimplexBoundaryDomainInv, innerOneSimplexBoundaryFaces]

/-- The two copies of the simplicial tensor unit are canonically the boundary
of the standard one-simplex, in endpoint order. -/
def innerOneSimplexUnitBoundaryDomainIso :
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ≅ (∂Δ[1] : SSet.{u}) where
  hom := coprod.desc
    (innerOneSimplexUnitZeroIso.hom ≫ SSet.boundary.ι (1 : Fin 2))
    (innerOneSimplexUnitZeroIso.hom ≫ SSet.boundary.ι (0 : Fin 2))
  inv := innerOneSimplexBoundaryDomainInv
  hom_inv_id := by
    apply coprod.hom_ext <;> simp
  inv_hom_id := by
    apply SSet.boundary.hom_ext
    intro j
    fin_cases j <;> simp

/-- The two endpoint units included in the standard one-simplex. -/
def innerOneSimplexUnitBoundary :
    (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  innerOneSimplexUnitBoundaryDomainIso.hom ≫ (SSet.boundary 1).ι

instance innerOneSimplexUnitBoundary_mono :
    Mono innerOneSimplexUnitBoundary.{u} := by
  dsimp [innerOneSimplexUnitBoundary]
  infer_instance

@[reassoc (attr := simp)]
theorem inl_innerOneSimplexUnitBoundary :
    coprod.inl ≫ innerOneSimplexUnitBoundary.{u} =
      innerOneSimplexUnitPoint 0 := by
  simp [innerOneSimplexUnitBoundary, innerOneSimplexUnitBoundaryDomainIso,
    innerOneSimplexUnitPoint]

@[reassoc (attr := simp)]
theorem inr_innerOneSimplexUnitBoundary :
    coprod.inr ≫ innerOneSimplexUnitBoundary.{u} =
      innerOneSimplexUnitPoint 1 := by
  simp [innerOneSimplexUnitBoundary, innerOneSimplexUnitBoundaryDomainIso,
    innerOneSimplexUnitPoint]

/-- The native boundary of the inner cylinder is the tensor of its scalar
two-point boundary. -/
def innerOneSimplexBoundaryDomainIso (X : SimplicialSpace.{u}) :
    X ⨿ X ≅ (innerTensorBifunctor.obj X).obj
      ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) := by
  let _ : (innerTensorBifunctor.obj X).IsLeftAdjoint :=
    (innerTensorHomAdjunction₂.adj X).isLeftAdjoint
  exact (asIso (coprod.map (innerTensorUnitIso.inv.app X)
      (innerTensorUnitIso.inv.app X))) ≪≫
    asIso (coprodComparison (innerTensorBifunctor.obj X)
      (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

@[reassoc]
private theorem inl_innerOneSimplexBoundaryDomainIso
    (X : SimplicialSpace.{u}) :
    coprod.inl ≫ (innerOneSimplexBoundaryDomainIso X).hom =
      innerTensorUnitIso.inv.app X ≫
        (innerTensorBifunctor.obj X).map coprod.inl := by
  simp only [innerOneSimplexBoundaryDomainIso, Iso.trans_hom, asIso_hom]
  simp only [coprod.inl_map_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k => innerTensorUnitIso.inv.app X ≫ k)
    (inl_coprodComparison (innerTensorBifunctor.obj X)
      (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

@[reassoc]
private theorem inr_innerOneSimplexBoundaryDomainIso
    (X : SimplicialSpace.{u}) :
    coprod.inr ≫ (innerOneSimplexBoundaryDomainIso X).hom =
      innerTensorUnitIso.inv.app X ≫
        (innerTensorBifunctor.obj X).map coprod.inr := by
  simp only [innerOneSimplexBoundaryDomainIso, Iso.trans_hom, asIso_hom]
  simp only [coprod.inr_map_assoc]
  simpa only [Category.assoc] using congrArg
    (fun k => innerTensorUnitIso.inv.app X ≫ k)
    (inr_coprodComparison (innerTensorBifunctor.obj X)
      (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

private theorem innerOneSimplexBoundaryDomainIso_hom_boundary
    (X : SimplicialSpace.{u}) :
    (innerOneSimplexBoundaryDomainIso X).hom ≫
        (innerTensorBifunctor.obj X).map innerOneSimplexUnitBoundary =
      (innerOneSimplexPrecylinder.app X).i := by
  change (innerOneSimplexBoundaryDomainIso X).hom ≫
      (innerTensorBifunctor.obj X).map innerOneSimplexUnitBoundary =
    coprod.desc ((innerOneSimplexEndpoint 0).app X)
      ((innerOneSimplexEndpoint 1).app X)
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    rw [inl_innerOneSimplexBoundaryDomainIso_assoc,
      ← (innerTensorBifunctor.obj X).map_comp,
      inl_innerOneSimplexUnitBoundary]
    rfl
  · rw [coprod.inr_desc]
    rw [inr_innerOneSimplexBoundaryDomainIso_assoc,
      ← (innerTensorBifunctor.obj X).map_comp,
      inr_innerOneSimplexUnitBoundary]
    rfl

private theorem innerOneSimplexBoundaryDomainIso_naturality
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) :
    (innerOneSimplexBoundaryDomainIso X).hom ≫
        (innerTensor ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).map i =
      coprod.map i i ≫ (innerOneSimplexBoundaryDomainIso Y).hom := by
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc,
      inl_innerOneSimplexBoundaryDomainIso_assoc]
    rw [(innerTensorBifunctor.map i).naturality]
    rw [← innerTensorUnitIso.inv.naturality_assoc]
    simpa only [Functor.id_map, Category.assoc] using congrArg
      (fun k => i ≫ k) (inl_innerOneSimplexBoundaryDomainIso Y).symm
  · simp only [coprod.inr_map_assoc,
      inr_innerOneSimplexBoundaryDomainIso_assoc]
    rw [(innerTensorBifunctor.map i).naturality]
    rw [← innerTensorUnitIso.inv.naturality_assoc]
    simpa only [Functor.id_map, Category.assoc] using congrArg
      (fun k => i ≫ k) (inr_innerOneSimplexBoundaryDomainIso Y).symm

/-- The specified boundary corner of the inner one-simplex precylinder as
native inner pushout-product data.  Its corner arrow is definitionally the
existing `Precylinder.boundaryCorner`. -/
def innerOneSimplexBoundaryPushoutObjObj {X Y : SimplicialSpace.{u}}
    (i : X ⟶ Y) :
    innerTensorBifunctor.PushoutObjObj i innerOneSimplexUnitBoundary where
  pt := pushout (coprod.map i i) (innerOneSimplexPrecylinder.app X).i
  inl := (innerOneSimplexBoundaryDomainIso Y).inv ≫ pushout.inl _ _
  inr := pushout.inr _ _
  isPushout := by
    refine (IsPushout.of_hasPushout (coprod.map i i)
      (innerOneSimplexPrecylinder.app X).i).of_iso
        (innerOneSimplexBoundaryDomainIso X)
        (innerOneSimplexBoundaryDomainIso Y) (Iso.refl _) (Iso.refl _)
        ?_ ?_ ?_ ?_
    · exact (innerOneSimplexBoundaryDomainIso_naturality i).symm
    · exact (innerOneSimplexBoundaryDomainIso_hom_boundary X).symm
    · simp
    · simp
  ι := innerOneSimplexPrecylinder.boundaryCorner i
  inl_ι := by
    rw [Category.assoc, Precylinder.inl_boundaryCorner]
    rw [← innerOneSimplexBoundaryDomainIso_hom_boundary Y]
    simp
  inr_ι := by
    simpa only [innerOneSimplexPrecylinder] using
      innerOneSimplexPrecylinder.inr_boundaryCorner i

namespace ReedyModel

/-- Boundary corners of Reedy trivial cofibrations are trivial cofibrations for
the inner one-simplex precylinder. -/
theorem innerOneSimplex_boundaryCorner_trivialCofibration
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialCofibrations SimplicialSpace.{u} i →
      trivialCofibrations SimplicialSpace.{u}
        (innerOneSimplexPrecylinder.boundaryCorner i) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hi
  let sq := innerOneSimplexBoundaryPushoutObjObj i
  change trivialCofibrations SimplicialSpace.{u} sq.ι
  apply inner_pushoutObjObj_trivialCofibration_of_left
    i innerOneSimplexUnitBoundary sq hi
  rw [SSet.modelCategoryQuillen.cofibrations_eq]
  exact monomorphisms.infer_property innerOneSimplexUnitBoundary

/-- A Reedy trivial cofibration between fibrant simplicial spaces has strict
strong deformation data for the actual inner one-simplex cylinder. -/
theorem nonempty_innerStrongDeformationData_of_trivialCofibration
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialCofibrations SimplicialSpace.{u} i →
      IsFibrant X → IsFibrant Y →
        Nonempty (innerOneSimplexPrecylinder.StrongDeformationData i) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  intro hi hX hY
  exact innerOneSimplexPrecylinder.nonempty_strongDeformationData_of_trivialCofibration
    i hi (innerOneSimplex_boundaryCorner_trivialCofibration i hi) hX hY

end ReedyModel
end SimplicialSpace
