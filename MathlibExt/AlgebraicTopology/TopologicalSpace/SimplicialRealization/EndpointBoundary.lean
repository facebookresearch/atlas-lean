/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import MathlibExt.Topology.Category.TopCat.EndpointFixedCorrection
public import MathlibExt.Topology.Category.TopCat.PushoutHomotopyDescent
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary

/-!
# The actual endpoint-boundary pushout for a realized monomorphism

The original boundary inclusion of the simplicial interval, together with
an actual simplicial monomorphism, gives a monic pushout-product. Ordinary
realization and the finite-parameter product comparison give the actual
endpoint-retuning cofibration into the literal interval/source carrier.
The active simplicial source and target are arbitrary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open scoped Simplicial MonoidalCategory TopCat.modelCategory

universe u

namespace SSet

/-- The original pushout-product is monic, derived from the SAME actual
range factorization and original union-product subcomplex inclusion. -/
public theorem pushoutProduct_mono_of_mono
    {K X Y : SSet.{u}} (S : K.Subcomplex) (i : X ⟶ Y) [Mono i] :
    Mono ((Arrow.mk S.ι □ Arrow.mk i).hom) := by
  let T := Subcomplex.range i
  have hComm : (asIso (Subcomplex.toRange i)).hom ≫ T.ι = i ≫ (Iso.refl Y).hom := by
    change Subcomplex.toRange i ≫ (Subcomplex.range i).ι = i ≫ 𝟙 Y
    exact (Subcomplex.toRange_ι i).trans (Category.comp_id i).symm
  let e : Arrow.mk i ≅ Arrow.mk T.ι :=
    Arrow.isoMk (asIso (Subcomplex.toRange i)) (Iso.refl Y) hComm
  let eProd : (Arrow.mk S.ι □ Arrow.mk i) ≅ Arrow.mk (S.unionProd T).ι :=
    ((MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk S.ι)).mapIso e) ≪≫
      (Subcomplex.unionProd.ιIso S T).symm
  have hUnion : (MorphismProperty.monomorphisms SSet.{u})
      (Arrow.mk (S.unionProd T).ι).hom := by
    change Mono (S.unionProd T).ι
    infer_instance
  change (MorphismProperty.monomorphisms SSet.{u})
    (Arrow.mk S.ι □ Arrow.mk i).hom
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff eProd).2 hUnion

/-- The ordinary realization product identification uses ONLY the
finite parameter factor K; the active target Y remains arbitrary. -/
public def finiteLeftTensorRealizationIso (K Y : SSet.{u}) [K.Finite] :
    SSet.toTop.obj (K ⊗ Y) ≅ SSet.toTop.obj K ⨯ SSet.toTop.obj Y := by
  letI : IsIso (Limits.prodComparison SSet.toTop K Y) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary K Y
  exact SSet.toTop.mapIso ((CartesianMonoidalCategory.tensorLeftIsoProd K).app Y) ≪≫
    asIso (Limits.prodComparison SSet.toTop K Y)

/-- The ORIGINAL simplicial-interval realization clock and actual
ordinary product identify the target with the literal I×Y carrier. -/
public def endpointBoundaryTargetIso (Y : SSet.{u}) :
    SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ Y) ≅
      TopCat.of (unitInterval × SSet.toTop.obj Y) := by
  let clock : SSet.toTop.obj (Δ[1] : SSet.{u}) ≃ₜ unitInterval :=
    (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI.{u}).trans TopCat.I.homeomorph.{u}
  exact finiteLeftTensorRealizationIso (Δ[1] : SSet.{u}) Y ≪≫
    TopCat.prodIsoProd (SSet.toTop.obj (Δ[1] : SSet.{u})) (SSet.toTop.obj Y) ≪≫
      TopCat.isoOfHomeo (clock.prodCongr (Homeomorph.refl (SSet.toTop.obj Y)))

/-- The ACTUAL original interval-boundary/transition pushout map, with
its SAME original simplicial map i and literal interval/source target. -/
public def realizedEndpointBoundaryArrow {X Y : SSet.{u}} (i : X ⟶ Y) :
    Arrow TopCat.{u} :=
  let p := Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i
  Arrow.mk (SSet.toTop.map p.hom ≫ (endpointBoundaryTargetIso Y).hom)

/-- Computed whole value of the ORIGINAL boundary arrow, available without
reducing an opaque Arrow wrapper in another declaration. -/
public theorem realizedEndpointBoundaryArrow_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    realizedEndpointBoundaryArrow i =
      Arrow.mk (SSet.toTop.map (Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i).hom ≫
        (endpointBoundaryTargetIso Y).hom) := by
  rfl

/-- The actual endpoint-boundary map is a Hurewicz cofibration, from the
derived original pushout-product Mono and actual ordinary realization. -/
public theorem realizedEndpointBoundary_isHurewiczCofibration
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.IsHurewiczCofibration (realizedEndpointBoundaryArrow i).hom := by
  let p : Arrow SSet.{u} := Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i
  let _ : Mono p.hom := pushoutProduct_mono_of_mono (SSet.boundary.{u} 1) i
  change TopCat.IsHurewiczCofibration
    (SSet.toTop.map p.hom ≫ (endpointBoundaryTargetIso Y).hom)
  have hMono : TopCat.IsHurewiczCofibration (SSet.toTop.map p.hom) :=
    SSet.toTop_map_isHurewiczCofibration p.hom
  have hIso : TopCat.IsHurewiczCofibration (endpointBoundaryTargetIso Y).hom :=
    TopCat.hurewiczCofibrations_iso (endpointBoundaryTargetIso Y)
  exact @TopCat.hurewiczCofibrations_comp.{u}
    (SSet.toTop.obj p.left) (SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ Y))
    (TopCat.of (unitInterval × SSet.toTop.obj Y))
    (SSet.toTop.map p.hom) (endpointBoundaryTargetIso Y).hom hMono hIso

/-- The SAME actual endpoint-boundary map is also a model cofibration;
no lifting, NDR, compatibility or retuning outcome is supplied. -/
public theorem realizedEndpointBoundary_cofibration
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Cofibration (realizedEndpointBoundaryArrow i).hom := by
  let p : Arrow SSet.{u} := Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i
  let _ : Mono p.hom := pushoutProduct_mono_of_mono (SSet.boundary.{u} 1) i
  have hMap : Cofibration (SSet.toTop.map p.hom) :=
    (cofibration_iff _).mpr (SSet.toTop_map_mem_realizedBoundaryLLP p.hom)
  change Cofibration (SSet.toTop.map p.hom ≫ (endpointBoundaryTargetIso Y).hom)
  exact (cofibration_iff _).mpr
    (MorphismProperty.RespectsIso.postcomp (cofibrations TopCat.{u})
      (endpointBoundaryTargetIso Y).hom (SSet.toTop.map p.hom) hMap.mem)

end SSet

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory

namespace SSet

/-- The ACTUAL original interval-boundary/transition Leibniz pushout data.
Every object/map is the SAME canonical pushout used in227's boundary arrow. -/
public def endpointBoundaryPushoutData {X Y : SSet.{u}} (i : X ⟶ Y) :
    (curriedTensor SSet.{u}).PushoutObjObj (SSet.boundary.{u} 1).ι i :=
  Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (SSet.boundary.{u} 1).ι i

/-- Computed data of the SAME chosen canonical pushout. -/
public theorem endpointBoundaryPushoutData_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundaryPushoutData i =
      Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
        (SSet.boundary.{u} 1).ι i := by
  rfl

/-- The canonical pushout data and ORIGINAL Leibniz construction give the
SAME whole Arrow, including both its actual source and actual target. -/
public theorem endpointBoundaryPushoutData_arrow_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    Arrow.mk (endpointBoundaryPushoutData i).ι =
      Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i := by
  rw [endpointBoundaryPushoutData_eq]
  rfl

/-- Actual equality of the original chosen pushout point and Arrow source. -/
public theorem endpointBoundaryPushoutData_pt_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    (endpointBoundaryPushoutData i).pt =
      (Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i).left :=
  congrArg (fun p : Arrow SSet.{u} => p.left) (endpointBoundaryPushoutData_arrow_eq i)

/-- Actual equality of the original tensor target and Arrow target. -/
public theorem endpointBoundaryPushoutData_target_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ Y =
      (Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i).right :=
  congrArg (fun p : Arrow SSet.{u} => p.right) (endpointBoundaryPushoutData_arrow_eq i)

/-- Whole Arrow equality computes its original morphism with BOTH typed
source and target transports. -/
private theorem endpointArrow_hom_cast {p q : Arrow SSet.{u}} (h : p = q) :
    eqToHom (congrArg (fun a : Arrow SSet.{u} => a.left) h) ≫ q.hom ≫
      eqToHom (congrArg (fun a : Arrow SSet.{u} => a.right) h).symm = p.hom := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The SAME original inclusion is the original Leibniz morphism, with the
actual chosen point and target equalities retained in its typed formula. -/
public theorem endpointBoundaryPushoutData_hom {X Y : SSet.{u}} (i : X ⟶ Y) :
    (endpointBoundaryPushoutData i).ι =
      eqToHom (endpointBoundaryPushoutData_pt_eq i) ≫
        (Arrow.mk (SSet.boundary.{u} 1).ι □ Arrow.mk i).hom ≫
          eqToHom (endpointBoundaryPushoutData_target_eq i).symm :=
  (endpointArrow_hom_cast (endpointBoundaryPushoutData_arrow_eq i)).symm

/-- The actual first original leg has its whole original transition-product composite. -/
public theorem endpointBoundaryPushout_side_fac {X Y : SSet.{u}} (i : X ⟶ Y) :
    (endpointBoundaryPushoutData i).inl ≫ (endpointBoundaryPushoutData i).ι =
      (Δ[1] : SSet.{u}) ◁ i :=
  (endpointBoundaryPushoutData i).inl_ι

/-- The actual second original leg has its whole original endpoint-product composite. -/
public theorem endpointBoundaryPushout_end_fac {X Y : SSet.{u}} (i : X ⟶ Y) :
    (endpointBoundaryPushoutData i).inr ≫ (endpointBoundaryPushoutData i).ι =
      (SSet.boundary.{u} 1).ι ▷ Y :=
  (endpointBoundaryPushoutData i).inr_ι

/-- The two original legs form their ACTUAL entire simplicial pushout. -/
public theorem endpointBoundaryPushout_isPushout {X Y : SSet.{u}} (i : X ⟶ Y) :
    IsPushout
      ((SSet.boundary.{u} 1).ι ▷ X)
      ((SSet.boundary.{u} 1 : SSet.{u}) ◁ i)
      (endpointBoundaryPushoutData i).inl
      (endpointBoundaryPushoutData i).inr :=
  (endpointBoundaryPushoutData i).isPushout

/-- The ORIGINAL boundary morphism with its actual chosen pushout source
and literal interval target both written explicitly in its type. -/
public def endpointBoundaryMap {X Y : SSet.{u}} (i : X ⟶ Y) :
    SSet.toTop.obj (endpointBoundaryPushoutData i).pt ⟶
      TopCat.of (unitInterval × SSet.toTop.obj Y) :=
  SSet.toTop.map (endpointBoundaryPushoutData i).ι ≫ (endpointBoundaryTargetIso Y).hom

/-- Computed whole value of the typed ORIGINAL boundary map. -/
public theorem endpointBoundaryMap_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundaryMap i =
      SSet.toTop.map (endpointBoundaryPushoutData i).ι ≫ (endpointBoundaryTargetIso Y).hom := by
  rfl

/-- The typed map is EXACTLY the original realized boundary Arrow, on its
entire chosen pushout source and the SAME original interval target clock. -/
public theorem endpointBoundaryMap_arrow_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    Arrow.mk (endpointBoundaryMap i) = realizedEndpointBoundaryArrow i := by
  rw [realizedEndpointBoundaryArrow_eq, endpointBoundaryMap_eq,
    endpointBoundaryPushoutData_eq]
  rfl

/-- The original realized Arrow has the actual chosen realized pushout source. -/
public theorem realizedEndpointBoundaryArrow_left {X Y : SSet.{u}} (i : X ⟶ Y) :
    (realizedEndpointBoundaryArrow i).left =
      SSet.toTop.obj (endpointBoundaryPushoutData i).pt :=
  (congrArg (fun p : Arrow TopCat.{u} => p.left) (endpointBoundaryMap_arrow_eq i)).symm

/-- The original realized Arrow has its literal original interval/source target. -/
public theorem realizedEndpointBoundaryArrow_right {X Y : SSet.{u}} (i : X ⟶ Y) :
    (realizedEndpointBoundaryArrow i).right =
      TopCat.of (unitInterval × SSet.toTop.obj Y) :=
  (congrArg (fun p : Arrow TopCat.{u} => p.right) (endpointBoundaryMap_arrow_eq i)).symm

/-- The typed ORIGINAL boundary map inherits its Hurewicz property from
its actual whole Arrow identity and the derived original Mono proof. -/
public theorem endpointBoundaryMap_isHurewiczCofibration
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.IsHurewiczCofibration (endpointBoundaryMap i) := by
  have h : TopCat.hurewiczCofibrations.{u} (realizedEndpointBoundaryArrow i).hom :=
    realizedEndpointBoundary_isHurewiczCofibration i
  have hEq : TopCat.hurewiczCofibrations.{u} (endpointBoundaryMap i) =
      TopCat.hurewiczCofibrations.{u} (realizedEndpointBoundaryArrow i).hom :=
    congrArg
      (fun p : Arrow TopCat.{u} => TopCat.hurewiczCofibrations.{u} p.hom)
      (endpointBoundaryMap_arrow_eq i)
  exact @Eq.mpr
    (TopCat.hurewiczCofibrations.{u} (endpointBoundaryMap i))
    (TopCat.hurewiczCofibrations.{u} (realizedEndpointBoundaryArrow i).hom)
    hEq (@h)

/-- The ORIGINAL side leg on its entire original ordinary realization. -/
public def endpointBoundarySideRealization {X Y : SSet.{u}} (i : X ⟶ Y) :
    SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ X) ⟶
      SSet.toTop.obj (endpointBoundaryPushoutData i).pt :=
  SSet.toTop.map (endpointBoundaryPushoutData i).inl

/-- Computed whole value of the ORIGINAL realized side leg. -/
public theorem endpointBoundarySideRealization_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundarySideRealization i = SSet.toTop.map (endpointBoundaryPushoutData i).inl := by
  rfl

/-- The ORIGINAL endpoint leg on its entire original ordinary realization. -/
public def endpointBoundaryEndRealization {X Y : SSet.{u}} (i : X ⟶ Y) :
    SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ Y) ⟶
      SSet.toTop.obj (endpointBoundaryPushoutData i).pt :=
  SSet.toTop.map (endpointBoundaryPushoutData i).inr

/-- Computed whole value of the ORIGINAL realized endpoint leg. -/
public theorem endpointBoundaryEndRealization_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundaryEndRealization i = SSet.toTop.map (endpointBoundaryPushoutData i).inr := by
  rfl

/-- The WHOLE original ordinary side-leg factorization, with the
SAME original interval/source target clock and ORIGINAL transition i. -/
public theorem endpointBoundarySideRealization_fac {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundarySideRealization i ≫ endpointBoundaryMap i =
      SSet.toTop.map ((Δ[1] : SSet.{u}) ◁ i) ≫ (endpointBoundaryTargetIso Y).hom := by
  rw [endpointBoundarySideRealization_eq, endpointBoundaryMap_eq]
  rw [← Category.assoc, ← Functor.map_comp, endpointBoundaryPushout_side_fac]

/-- The WHOLE original ordinary endpoint-leg factorization, with
SAME original interval/source target clock and BOTH original faces. -/
public theorem endpointBoundaryEndRealization_fac {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundaryEndRealization i ≫ endpointBoundaryMap i =
      SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ Y) ≫
        (endpointBoundaryTargetIso Y).hom := by
  rw [endpointBoundaryEndRealization_eq, endpointBoundaryMap_eq]
  rw [← Category.assoc, ← Functor.map_comp, endpointBoundaryPushout_end_fac]

/-- EVERY original realized side point has the exact original
transition-product image in the literal interval/source target. -/
public theorem endpointBoundarySideRealization_apply
    {X Y : SSet.{u}} (i : X ⟶ Y)
    (x : SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ X)) :
    endpointBoundaryMap i (endpointBoundarySideRealization i x) =
      (endpointBoundaryTargetIso Y).hom
        (SSet.toTop.map ((Δ[1] : SSet.{u}) ◁ i) x) :=
  ConcreteCategory.congr_hom (endpointBoundarySideRealization_fac i) x

/-- EVERY original realized endpoint-leg point has its exact original
boundary-product image, retaining BOTH original time faces. -/
public theorem endpointBoundaryEndRealization_apply
    {X Y : SSet.{u}} (i : X ⟶ Y)
    (x : SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ Y)) :
    endpointBoundaryMap i (endpointBoundaryEndRealization i x) =
      (endpointBoundaryTargetIso Y).hom
        (SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ Y) x) :=
  ConcreteCategory.congr_hom (endpointBoundaryEndRealization_fac i) x

/-- Ordinary realization preserves the ACTUAL original full pushout,
providing whole gluing with the ORIGINAL side and endpoint legs. -/
public theorem endpointBoundaryRealization_isPushout {X Y : SSet.{u}} (i : X ⟶ Y) :
    IsPushout
      (SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ X))
      (SSet.toTop.map ((SSet.boundary.{u} 1 : SSet.{u}) ◁ i))
      (endpointBoundarySideRealization i) (endpointBoundaryEndRealization i) := by
  rw [endpointBoundarySideRealization_eq, endpointBoundaryEndRealization_eq]
  exact SSet.toTop.map_isPushout (endpointBoundaryPushout_isPushout i)

end SSet

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory ContinuousMap

namespace SSet

/-- The tensor-to-chosen-product comparison has its actual first projection. -/
private theorem endpointTensorToProduct_fst (K X : SSet.{u}) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫ Limits.prod.fst =
      CartesianMonoidalCategory.fst K X :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct K X)
    (limit.isLimit _) ⟨WalkingPair.left⟩

/-- The tensor-to-chosen-product comparison has its actual second projection. -/
private theorem endpointTensorToProduct_snd (K X : SSet.{u}) :
    ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫ Limits.prod.snd =
      CartesianMonoidalCategory.snd K X :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct K X)
    (limit.isLimit _) ⟨WalkingPair.right⟩

/-- Naturality of the actual tensor-to-chosen-product comparison in both factors. -/
private theorem endpointTensorToProduct_natural
    {K L X Y : SSet.{u}} (f : K ⟶ L) (g : X ⟶ Y) :
    (f ⊗ₘ g) ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom =
      ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
        Limits.prod.map f g := by
  apply Limits.prod.hom_ext
  · calc
      ((f ⊗ₘ g) ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom) ≫
          Limits.prod.fst = (f ⊗ₘ g) ≫ CartesianMonoidalCategory.fst L Y := by
            rw [Category.assoc, endpointTensorToProduct_fst]
      _ = CartesianMonoidalCategory.fst K X ≫ f :=
        CartesianMonoidalCategory.tensorHom_fst f g
      _ = (((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
          Limits.prod.fst) ≫ f := by rw [endpointTensorToProduct_fst]
      _ = (((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
          Limits.prod.map f g) ≫ Limits.prod.fst := by
            simp only [Category.assoc, Limits.prod.map_fst]
  · calc
      ((f ⊗ₘ g) ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom) ≫
          Limits.prod.snd = (f ⊗ₘ g) ≫ CartesianMonoidalCategory.snd L Y := by
            rw [Category.assoc, endpointTensorToProduct_snd]
      _ = CartesianMonoidalCategory.snd K X ≫ g :=
        CartesianMonoidalCategory.tensorHom_snd f g
      _ = (((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
          Limits.prod.snd) ≫ g := by rw [endpointTensorToProduct_snd]
      _ = (((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
          Limits.prod.map f g) ≫ Limits.prod.snd := by
            simp only [Category.assoc, Limits.prod.map_snd]

/-- The original finite-parameter realization product isomorphism is natural
in BOTH factors. Only K and L are finite; X and Y remain arbitrary. -/
public theorem finiteLeftTensorRealizationIso_natural
    {K L X Y : SSet.{u}} [K.Finite] [L.Finite]
    (f : K ⟶ L) (g : X ⟶ Y) :
    SSet.toTop.map (f ⊗ₘ g) ≫ (finiteLeftTensorRealizationIso L Y).hom =
      (finiteLeftTensorRealizationIso K X).hom ≫
        Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g) := by
  change SSet.toTop.map (f ⊗ₘ g) ≫
      (SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom ≫
        Limits.prodComparison SSet.toTop L Y) =
    (SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
      Limits.prodComparison SSet.toTop K X) ≫
        Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g)
  calc
    SSet.toTop.map (f ⊗ₘ g) ≫
        (SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom ≫
          Limits.prodComparison SSet.toTop L Y) =
      SSet.toTop.map
        ((f ⊗ₘ g) ≫ ((CartesianMonoidalCategory.tensorLeftIsoProd L).app Y).hom) ≫
          Limits.prodComparison SSet.toTop L Y := by
            rw [Functor.map_comp, Category.assoc]
    _ = SSet.toTop.map
        (((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
          Limits.prod.map f g) ≫ Limits.prodComparison SSet.toTop L Y := by
            rw [endpointTensorToProduct_natural]
    _ = SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
        (SSet.toTop.map (Limits.prod.map f g) ≫
          Limits.prodComparison SSet.toTop L Y) := by
            rw [Functor.map_comp, Category.assoc]
    _ = SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
        (Limits.prodComparison SSet.toTop K X ≫
          Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g)) := by
            rw [Limits.prodComparison_natural]
    _ = (SSet.toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd K).app X).hom ≫
        Limits.prodComparison SSet.toTop K X) ≫
          Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g) :=
            (Category.assoc _ _ _).symm

/-- The actual ordinary chosen product computes both mapped coordinates. -/
private theorem endpointProduct_map_apply
    {A B C D : TopCat.{u}} (f : A ⟶ B) (g : C ⟶ D) (z : ↑(A ⨯ C)) :
    (TopCat.prodIsoProd B D).hom (Limits.prod.map f g z) =
      (f ((TopCat.prodIsoProd A C).hom z).1,
        g ((TopCat.prodIsoProd A C).hom z).2) := by
  change ((Limits.prod.fst : B ⨯ D ⟶ B) (Limits.prod.map f g z),
      (Limits.prod.snd : B ⨯ D ⟶ D) (Limits.prod.map f g z)) =
    (f ((Limits.prod.fst : A ⨯ C ⟶ A) z),
      g ((Limits.prod.snd : A ⨯ C ⟶ C) z))
  exact Prod.ext
    (ConcreteCategory.congr_hom (Limits.prod.map_fst f g) z)
    (ConcreteCategory.congr_hom (Limits.prod.map_snd f g) z)

/-- The original realization functor evaluates its actual identity map. -/
private theorem endpointToTop_id_apply (K : SSet.{u}) (z : SSet.toTop.obj K) :
    SSet.toTop.map (𝟙 K) z = z := by
  simpa only [CategoryTheory.id_apply] using
    ConcreteCategory.congr_hom (SSet.toTop.map_id K) z

/-- Every original tensor-realization point has the natural plain-product
coordinates under the actual finite-parameter comparison. -/
public theorem finiteLeftTensorRealizationIso_natural_apply
    {K L X Y : SSet.{u}} [K.Finite] [L.Finite]
    (f : K ⟶ L) (g : X ⟶ Y) (z : SSet.toTop.obj (K ⊗ X)) :
    (TopCat.prodIsoProd (SSet.toTop.obj L) (SSet.toTop.obj Y)).hom
        ((finiteLeftTensorRealizationIso L Y).hom (SSet.toTop.map (f ⊗ₘ g) z)) =
      (SSet.toTop.map f
          ((TopCat.prodIsoProd (SSet.toTop.obj K) (SSet.toTop.obj X)).hom
            ((finiteLeftTensorRealizationIso K X).hom z)).1,
        SSet.toTop.map g
          ((TopCat.prodIsoProd (SSet.toTop.obj K) (SSet.toTop.obj X)).hom
            ((finiteLeftTensorRealizationIso K X).hom z)).2) := by
  have h : (finiteLeftTensorRealizationIso L Y).hom (SSet.toTop.map (f ⊗ₘ g) z) =
      Limits.prod.map (SSet.toTop.map f) (SSet.toTop.map g)
        ((finiteLeftTensorRealizationIso K X).hom z) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (finiteLeftTensorRealizationIso_natural f g) z
  rw [h]
  exact endpointProduct_map_apply _ _ _

/-- The clock is the SAME original simplex-to-TopCat-I-to-unitInterval clock. -/
public def endpointIntervalClock :
    SSet.toTop.obj (Δ[1] : SSet.{u}) ≃ₜ unitInterval :=
  (TopCat.homeoOfIso SSet.stdSimplex.toTopObjIsoI.{u}).trans TopCat.I.homeomorph.{u}

/-- Whole plain-product computation of the original interval target isomorphism. -/
private theorem endpointBoundaryTargetIso_hom_apply (Y : SSet.{u})
    (z : SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ Y)) :
    (endpointBoundaryTargetIso Y).hom z =
      (endpointIntervalClock.{u}
          ((TopCat.prodIsoProd (SSet.toTop.obj (Δ[1] : SSet.{u}))
            (SSet.toTop.obj Y)).hom
              ((finiteLeftTensorRealizationIso (Δ[1] : SSet.{u}) Y).hom z)).1,
        ((TopCat.prodIsoProd (SSet.toTop.obj (Δ[1] : SSet.{u}))
          (SSet.toTop.obj Y)).hom
            ((finiteLeftTensorRealizationIso (Δ[1] : SSet.{u}) Y).hom z)).2) := by
  rfl

/-- The original boundary parameter map is induced by its actual inclusion
and the SAME original interval realization clock. -/
public def endpointBoundaryParameter :
    C(SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}), unitInterval) :=
  { toFun := fun b => endpointIntervalClock.{u} (SSet.toTop.map (SSet.boundary.{u} 1).ι b)
    continuous_toFun := endpointIntervalClock.{u}.continuous.comp
      (SSet.toTop.map (SSet.boundary.{u} 1).ι).hom.continuous }

/-- The SAME original boundary parameter computes at EVERY actual point. -/
public theorem endpointBoundaryParameter_apply
    (b : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u})) :
    endpointBoundaryParameter.{u} b =
      endpointIntervalClock.{u} (SSet.toTop.map (SSet.boundary.{u} 1).ι b) := by
  rfl

/-- The original side-product target map retains the literal interval coordinate. -/
private theorem endpointBoundaryTargetIso_natural_apply
    {X Y : SSet.{u}} (i : X ⟶ Y)
    (z : SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ X)) :
    (endpointBoundaryTargetIso Y).hom (SSet.toTop.map ((Δ[1] : SSet.{u}) ◁ i) z) =
      (((endpointBoundaryTargetIso X).hom z).1,
        SSet.toTop.map i ((endpointBoundaryTargetIso X).hom z).2) := by
  have h := finiteLeftTensorRealizationIso_natural_apply (𝟙 (Δ[1] : SSet.{u})) i z
  rw [MonoidalCategory.id_tensorHom] at h
  rw [endpointToTop_id_apply] at h
  have hclock := congrArg
    (fun p : SSet.toTop.obj (Δ[1] : SSet.{u}) × SSet.toTop.obj Y =>
      (endpointIntervalClock.{u} p.1, p.2)) h
  have hTarget := congrArg
    (fun p : unitInterval × SSet.toTop.obj X => (p.1, SSet.toTop.map i p.2))
    (endpointBoundaryTargetIso_hom_apply X z)
  exact (endpointBoundaryTargetIso_hom_apply Y
    (SSet.toTop.map ((Δ[1] : SSet.{u}) ◁ i) z)).trans
      (hclock.trans hTarget.symm)

/-- The SAME original side leg, reparameterized through its actual interval product iso. -/
public def endpointBoundarySideLeg {X Y : SSet.{u}} (i : X ⟶ Y) :
    TopCat.of (unitInterval × SSet.toTop.obj X) ⟶
      SSet.toTop.obj (endpointBoundaryPushoutData i).pt :=
  (endpointBoundaryTargetIso X).inv ≫ endpointBoundarySideRealization i

/-- Computed whole value of the ORIGINAL literal side leg. -/
public theorem endpointBoundarySideLeg_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundarySideLeg i =
      (endpointBoundaryTargetIso X).inv ≫ endpointBoundarySideRealization i := by
  rfl

/-- EVERY original side point has its literal (t,x) transition-product image. -/
public theorem endpointBoundarySideLeg_apply
    {X Y : SSet.{u}} (i : X ⟶ Y) (t : unitInterval) (x : SSet.toTop.obj X) :
    endpointBoundaryMap i (endpointBoundarySideLeg i (t, x)) =
      (t, SSet.toTop.map i x) := by
  rw [endpointBoundarySideLeg_eq]
  change endpointBoundaryMap i
      (endpointBoundarySideRealization i ((endpointBoundaryTargetIso X).inv (t, x))) = _
  rw [endpointBoundarySideRealization_apply, endpointBoundaryTargetIso_natural_apply]
  have h : (endpointBoundaryTargetIso X).hom
      ((endpointBoundaryTargetIso X).inv (t, x)) = (t, x) := by
    simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
      ConcreteCategory.congr_hom (endpointBoundaryTargetIso X).inv_hom_id (t, x)
  rw [h]

/-- The original endpoint-product source is identified with its actual plain product. -/
public def endpointBoundaryEndSourceIso (Y : SSet.{u}) :
    SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ Y) ≅
      TopCat.of (SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}) × SSet.toTop.obj Y) :=
  finiteLeftTensorRealizationIso (SSet.boundary.{u} 1 : SSet.{u}) Y ≪≫
    TopCat.prodIsoProd (SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}))
      (SSet.toTop.obj Y)

/-- Computed plain-product value of the SAME original endpoint source iso. -/
public theorem endpointBoundaryEndSourceIso_hom_apply (Y : SSet.{u})
    (z : SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ Y)) :
    (endpointBoundaryEndSourceIso Y).hom z =
      (TopCat.prodIsoProd (SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}))
        (SSet.toTop.obj Y)).hom
          ((finiteLeftTensorRealizationIso (SSet.boundary.{u} 1 : SSet.{u}) Y).hom z) := by
  rfl

/-- Every original endpoint-product point has its actual parameter and source coordinates. -/
private theorem endpointBoundaryEndProduct_apply (Y : SSet.{u})
    (b : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u})) (y : SSet.toTop.obj Y) :
    (endpointBoundaryTargetIso Y).hom
        (SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ Y)
          ((endpointBoundaryEndSourceIso Y).inv (b, y))) =
      (endpointBoundaryParameter.{u} b, y) := by
  let z := (endpointBoundaryEndSourceIso Y).inv (b, y)
  have hz : (TopCat.prodIsoProd
      (SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u})) (SSet.toTop.obj Y)).hom
        ((finiteLeftTensorRealizationIso (SSet.boundary.{u} 1 : SSet.{u}) Y).hom z) =
      (b, y) :=
    (endpointBoundaryEndSourceIso_hom_apply Y z).symm.trans
      (TopCat.inv_hom_id_apply (endpointBoundaryEndSourceIso Y) (b, y))
  have h0 := finiteLeftTensorRealizationIso_natural_apply
    (SSet.boundary.{u} 1).ι (𝟙 Y) z
  rw [MonoidalCategory.tensorHom_id] at h0
  have hMapped := congrArg
    (fun p : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}) × SSet.toTop.obj Y =>
      (SSet.toTop.map (SSet.boundary.{u} 1).ι p.1, SSet.toTop.map (𝟙 Y) p.2)) hz
  have h : (TopCat.prodIsoProd (SSet.toTop.obj (Δ[1] : SSet.{u}))
      (SSet.toTop.obj Y)).hom
        ((finiteLeftTensorRealizationIso (Δ[1] : SSet.{u}) Y).hom
          (SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ Y) z)) =
      (SSet.toTop.map (SSet.boundary.{u} 1).ι b, y) :=
    h0.trans (hMapped.trans (Prod.ext rfl (endpointToTop_id_apply Y y)))
  have hclock := congrArg
    (fun p : SSet.toTop.obj (Δ[1] : SSet.{u}) × SSet.toTop.obj Y =>
      (endpointIntervalClock.{u} p.1, p.2)) h
  exact (endpointBoundaryTargetIso_hom_apply Y
    (SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ Y) z)).trans
      (hclock.trans (Prod.ext (endpointBoundaryParameter_apply b).symm rfl))

/-- The SAME original endpoint leg, reparameterized through its actual boundary product iso. -/
public def endpointBoundaryEndLeg {X Y : SSet.{u}} (i : X ⟶ Y) :
    TopCat.of (SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}) × SSet.toTop.obj Y) ⟶
      SSet.toTop.obj (endpointBoundaryPushoutData i).pt :=
  (endpointBoundaryEndSourceIso Y).inv ≫ endpointBoundaryEndRealization i

/-- Computed whole value of the ORIGINAL literal endpoint leg. -/
public theorem endpointBoundaryEndLeg_eq {X Y : SSet.{u}} (i : X ⟶ Y) :
    endpointBoundaryEndLeg i =
      (endpointBoundaryEndSourceIso Y).inv ≫ endpointBoundaryEndRealization i := by
  rfl

/-- EVERY original endpoint-leg point has its literal parameter/source image. -/
public theorem endpointBoundaryEndLeg_apply
    {X Y : SSet.{u}} (i : X ⟶ Y)
    (b : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u})) (y : SSet.toTop.obj Y) :
    endpointBoundaryMap i (endpointBoundaryEndLeg i (b, y)) =
      (endpointBoundaryParameter b, y) := by
  rw [endpointBoundaryEndLeg_eq]
  change endpointBoundaryMap i
      (endpointBoundaryEndRealization i ((endpointBoundaryEndSourceIso Y).inv (b, y))) = _
  rw [endpointBoundaryEndRealization_apply]
  exact endpointBoundaryEndProduct_apply Y b y

end SSet

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial ContinuousMap

namespace SSet

/-- The original delta-one face has the original clock value zero at EVERY point. -/
private theorem endpointIntervalClock_face_one
    (x : SSet.toTop.obj (Δ[0] : SSet.{u})) :
    endpointIntervalClock.{u} (SSet.toTop.map (stdSimplex.δ (1 : Fin 2)) x) = 0 := by
  have hVertex :
      ⦋1⦌.toTopHomeo (SSet.toTop.map (stdSimplex.δ (1 : Fin 2)) x) =
        StdSimplex.single (0 : Fin 2) := by
    refine (SimplexCategory.toTopHomeo_naturality_apply
      (SimplexCategory.δ (1 : Fin 2)) x).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo x) (StdSimplex.single 0),
      StdSimplex.map_single]
    rfl
  change TopCat.I.homeomorph.{u}
      (TopCat.stdSimplexHomeomorphI.{u}
        (⦋1⦌.toTopHomeo (SSet.toTop.map (stdSimplex.δ (1 : Fin 2)) x))) = 0
  rw [hVertex, TopCat.stdSimplexHomeomorphI_vertex_zero.{u}, TopCat.I.homeomorph_zero.{u}]

/-- The original delta-zero face has the original clock value one at EVERY point. -/
private theorem endpointIntervalClock_face_zero
    (x : SSet.toTop.obj (Δ[0] : SSet.{u})) :
    endpointIntervalClock.{u} (SSet.toTop.map (stdSimplex.δ (0 : Fin 2)) x) = 1 := by
  have hVertex :
      ⦋1⦌.toTopHomeo (SSet.toTop.map (stdSimplex.δ (0 : Fin 2)) x) =
        StdSimplex.single (1 : Fin 2) := by
    refine (SimplexCategory.toTopHomeo_naturality_apply
      (SimplexCategory.δ (0 : Fin 2)) x).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo x) (StdSimplex.single 0),
      StdSimplex.map_single]
    rfl
  change TopCat.I.homeomorph.{u}
      (TopCat.stdSimplexHomeomorphI.{u}
        (⦋1⦌.toTopHomeo (SSet.toTop.map (stdSimplex.δ (0 : Fin 2)) x))) = 1
  rw [hVertex, TopCat.stdSimplexHomeomorphI_vertex_one.{u}, TopCat.I.homeomorph_one.{u}]

/-- EVERY actual realized boundary parameter lies on one of the TWO original
endpoint faces. The range assertion is derived from the original finite face geometry. -/
public theorem endpointBoundaryParameter_eq_zero_or_one
    (b : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u})) :
    endpointBoundaryParameter b = 0 ∨ endpointBoundaryParameter b = 1 := by
  let q : SSet.toTop.obj (Δ[1] : SSet.{u}) :=
    SSet.toTop.map (SSet.boundary.{u} 1).ι b
  have hq : q ∈ Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} 1).ι) := ⟨b, rfl⟩
  obtain ⟨i, y, hy⟩ := boundary.exists_face_of_mem_realizedBoundaryRange 1 q hq
  let e := stdSimplex.faceSingletonComplIso (n := 0) i
  let x : SSet.toTop.obj (Δ[0] : SSet.{u}) := SSet.toTop.map e.inv y
  have he : e.hom ≫ (stdSimplex.face (n := 1) {i}ᶜ).ι = stdSimplex.δ i :=
    stdSimplex.faceSingletonComplIso_hom_ι i
  have hm : e.inv ≫ stdSimplex.δ i = (stdSimplex.face (n := 1) {i}ᶜ).ι := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hFace : SSet.toTop.map (stdSimplex.δ i) x = q := by
    calc
      SSet.toTop.map (stdSimplex.δ i) x =
          SSet.toTop.map (stdSimplex.face (n := 1) {i}ᶜ).ι y := by
        simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom (SSet.toTop.congr_map hm) y
      _ = q := hy
  have hParam : endpointBoundaryParameter.{u} b =
      endpointIntervalClock.{u} (SSet.toTop.map (stdSimplex.δ i) x) :=
    (endpointBoundaryParameter_apply b).trans
      (congrArg endpointIntervalClock.{u} hFace.symm)
  have hiNat : i.val = 0 ∨ i.val = 1 := by
    have hBound : i.val < 2 := i.isLt
    omega
  have hi : i = (0 : Fin 2) ∨ i = (1 : Fin 2) :=
    hiNat.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases hi with hi | hi
  · right
    rw [hi] at hParam
    exact hParam.trans (endpointIntervalClock_face_zero x)
  · left
    rw [hi] at hParam
    exact hParam.trans (endpointIntervalClock_face_one x)

/-- The original zero endpoint is the realization of the actual delta-one boundary face. -/
public def endpointBoundaryZero : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}) :=
  SSet.toTop.map (SSet.boundary.ι.{u} (1 : Fin 2)) default

/-- Computed value of the SAME original zero face point. -/
public theorem endpointBoundaryZero_eq :
    endpointBoundaryZero.{u} =
      SSet.toTop.map (SSet.boundary.ι.{u} (1 : Fin 2)) default := by
  rfl

/-- The original one endpoint is the realization of the actual delta-zero boundary face. -/
public def endpointBoundaryOne : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}) :=
  SSet.toTop.map (SSet.boundary.ι.{u} (0 : Fin 2)) default

/-- Computed value of the SAME original one face point. -/
public theorem endpointBoundaryOne_eq :
    endpointBoundaryOne.{u} =
      SSet.toTop.map (SSet.boundary.ι.{u} (0 : Fin 2)) default := by
  rfl

/-- The actual original zero endpoint maps to the SAME literal original clock zero. -/
public theorem endpointBoundaryParameter_zero :
    endpointBoundaryParameter endpointBoundaryZero.{u} = 0 := by
  rw [endpointBoundaryZero_eq, endpointBoundaryParameter_apply]
  have h : SSet.toTop.map (SSet.boundary.{u} 1).ι
      (SSet.toTop.map (SSet.boundary.ι.{u} (1 : Fin 2)) default) =
        SSet.toTop.map (stdSimplex.δ (1 : Fin 2)) default := by
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (SSet.toTop.congr_map (SSet.boundary.ι_ι.{u} (1 : Fin 2))) default
  exact (congrArg endpointIntervalClock.{u} h).trans (endpointIntervalClock_face_one default)

/-- The actual original one endpoint maps to the SAME literal original clock one. -/
public theorem endpointBoundaryParameter_one :
    endpointBoundaryParameter endpointBoundaryOne.{u} = 1 := by
  rw [endpointBoundaryOne_eq, endpointBoundaryParameter_apply]
  have h : SSet.toTop.map (SSet.boundary.{u} 1).ι
      (SSet.toTop.map (SSet.boundary.ι.{u} (0 : Fin 2)) default) =
        SSet.toTop.map (stdSimplex.δ (0 : Fin 2)) default := by
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (SSet.toTop.congr_map (SSet.boundary.ι_ι.{u} (0 : Fin 2))) default
  exact (congrArg endpointIntervalClock.{u} h).trans (endpointIntervalClock_face_zero default)

end SSet

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial MonoidalCategory ContinuousMap

namespace SSet

/-- The actual interval-boundary pushout extends a prescribed WHOLE local
comparison and retains its complete source restriction and BOTH fixed faces. -/
public theorem nonempty_endpointBoundaryCorrection
    {X Y : SSet.{u}} {Z : TopCat.{u}} (i : X ⟶ Y) [Mono i]
    {f₀ f₁ : SSet.toTop.obj Y ⟶ Z} (raw : TopCat.Homotopy f₀ f₁)
    (selected : C(unitInterval × SSet.toTop.obj X, Z))
    (P : ContinuousMap.HomotopyRel
      (raw.compContinuousMap (SSet.toTop.map i).hom).toContinuousMap selected
      (TopCat.homotopyEndpointFaces (SSet.toTop.obj X))) :
    Nonempty {c : TopCat.EndpointFixedCorrection raw //
      ∀ (s t : unitInterval) (x : SSet.toTop.obj X),
        c.comparison (s, (t, SSet.toTop.map i x)) = P (s, (t, x))} := by
  let A := SSet.toTop.obj ((Δ[1] : SSet.{u}) ⊗ X)
  let B := SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ Y)
  let C := SSet.toTop.obj ((SSet.boundary.{u} 1 : SSet.{u}) ⊗ X)
  let D := SSet.toTop.obj (endpointBoundaryPushoutData i).pt
  let f : C ⟶ A := SSet.toTop.map ((SSet.boundary.{u} 1).ι ▷ X)
  let g : C ⟶ B := SSet.toTop.map ((SSet.boundary.{u} 1 : SSet.{u}) ◁ i)
  let a : A ⟶ D := endpointBoundarySideRealization i
  let b : B ⟶ D := endpointBoundaryEndRealization i
  let j : D ⟶ TopCat.of (unitInterval × SSet.toTop.obj Y) :=
    endpointBoundaryMap i
  let sq : IsPushout f g a b := endpointBoundaryRealization_isPushout i
  let a₀ : A ⟶ Z := a ≫ j ≫ TopCat.ofHom raw.toContinuousMap
  let a₁ : A ⟶ Z := (endpointBoundaryTargetIso X).hom ≫ TopCat.ofHom selected
  let b₀ : B ⟶ Z := b ≫ j ≫ TopCat.ofHom raw.toContinuousMap
  have hSideInitial (z : A) :
      (raw.compContinuousMap (SSet.toTop.map i).hom).toContinuousMap
          ((endpointBoundaryTargetIso X).hom z) = a₀ z := by
    change raw.toContinuousMap
        (((endpointBoundaryTargetIso X).hom z).1,
          SSet.toTop.map i ((endpointBoundaryTargetIso X).hom z).2) =
      raw.toContinuousMap (j (a z))
    have hCoordinate : j (a z) =
        (((endpointBoundaryTargetIso X).hom z).1,
          SSet.toTop.map i ((endpointBoundaryTargetIso X).hom z).2) :=
      (endpointBoundarySideRealization_apply i z).trans
        (endpointBoundaryTargetIso_natural_apply i z)
    exact congrArg raw.toContinuousMap hCoordinate.symm
  let HA : TopCat.Homotopy a₀ a₁ :=
    { toFun := fun z => P (z.1, (endpointBoundaryTargetIso X).hom z.2)
      continuous_toFun := P.continuous.comp
        (continuous_fst.prodMk
          ((endpointBoundaryTargetIso X).hom.hom.continuous.comp continuous_snd))
      map_zero_left := fun z =>
        (P.apply_zero ((endpointBoundaryTargetIso X).hom z)).trans (hSideInitial z)
      map_one_left := fun z => P.apply_one ((endpointBoundaryTargetIso X).hom z) }
  let HB : TopCat.Homotopy b₀ b₀ := TopCat.Homotopy.refl b₀
  have hOverlap (s : unitInterval) (w : C) : HA (s, f w) = HB (s, g w) := by
    let z := (endpointBoundaryEndSourceIso X).hom w
    let β := z.1
    let x := z.2
    let p := (endpointBoundaryTargetIso X).hom (f w)
    have hRaw : (endpointBoundaryEndSourceIso X).inv (β, x) = w := by
      change (endpointBoundaryEndSourceIso X).inv
        ((endpointBoundaryEndSourceIso X).hom w) = w
      exact TopCat.hom_inv_id_apply (endpointBoundaryEndSourceIso X) w
    have hCoordinates : p = (endpointBoundaryParameter β, x) := by
      have h := endpointBoundaryEndProduct_apply X β x
      rw [hRaw] at h
      exact h
    have hFaces : p ∈ TopCat.homotopyEndpointFaces (SSet.toTop.obj X) := by
      change p.1 = 0 ∨ p.1 = 1
      rw [hCoordinates]
      exact endpointBoundaryParameter_eq_zero_or_one β
    have hSquare : a (f w) = b (g w) := ConcreteCategory.congr_hom sq.w w
    change P (s, p) = b₀ (g w)
    exact (P.eq_fst s hFaces).trans
      ((hSideInitial (f w)).trans
        (congrArg (fun z : D => raw.toContinuousMap (j z)) hSquare))
  have h₀ : f ≫ a₀ = g ≫ b₀ := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    change a₀ (f w) = b₀ (g w)
    exact (HA.apply_zero (f w)).symm.trans
      ((hOverlap 0 w).trans (HB.apply_zero (g w)))
  have h₁ : f ≫ a₁ = g ≫ b₀ := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    change a₁ (f w) = b₀ (g w)
    exact (HA.apply_one (f w)).symm.trans
      ((hOverlap 1 w).trans (HB.apply_one (g w)))
  let boundary := TopCat.Homotopy.descOfIsPushout sq HA HB h₀ h₁ hOverlap
  have hDescZero : sq.desc a₀ b₀ h₀ = j ≫ TopCat.ofHom raw.toContinuousMap := by
    apply sq.hom_ext
    · rw [sq.inl_desc]
    · rw [sq.inr_desc]
  have hBoundaryZero (z : D) : boundary.toContinuousMap (0, z) =
      raw.toContinuousMap (j z) :=
    (boundary.apply_zero z).trans (ConcreteCategory.congr_hom hDescZero z)
  have hCofibration : TopCat.IsHurewiczCofibration j :=
    endpointBoundaryMap_isHurewiczCofibration i
  obtain ⟨d⟩ : Nonempty (Topology.HomotopyExtensionData j.hom raw.toContinuousMap
      boundary.toContinuousMap hBoundaryZero) :=
    hCofibration raw.toContinuousMap boundary.toContinuousMap hBoundaryZero
  have hSide (s t : unitInterval) (x : SSet.toTop.obj X) :
      d.extension (s, (t, SSet.toTop.map i x)) = P (s, (t, x)) := by
    let z := (endpointBoundaryTargetIso X).inv (t, x)
    have hLeg : j (a z) = (t, SSet.toTop.map i x) := by
      change j (endpointBoundarySideLeg i (t, x)) = (t, SSet.toTop.map i x)
      exact endpointBoundarySideLeg_apply i t x
    calc
      d.extension (s, (t, SSet.toTop.map i x)) = d.extension (s, j (a z)) :=
        congrArg (fun p => d.extension (s, p)) hLeg.symm
      _ = boundary.toContinuousMap (s, a z) := d.extension_subspace s (a z)
      _ = HA (s, z) :=
        TopCat.Homotopy.descOfIsPushout_apply_inl sq HA HB h₀ h₁ hOverlap s z
      _ = P (s, (t, x)) :=
        congrArg (fun p => P (s, p))
          (TopCat.inv_hom_id_apply (endpointBoundaryTargetIso X) (t, x))
  have hEnd (s : unitInterval)
      (β : SSet.toTop.obj (SSet.boundary.{u} 1 : SSet.{u}))
      (y : SSet.toTop.obj Y) :
      d.extension (s, (endpointBoundaryParameter β, y)) =
        raw.toContinuousMap (endpointBoundaryParameter β, y) := by
    let z := (endpointBoundaryEndSourceIso Y).inv (β, y)
    have hLeg : j (b z) = (endpointBoundaryParameter β, y) := by
      change j (endpointBoundaryEndLeg i (β, y)) = (endpointBoundaryParameter β, y)
      exact endpointBoundaryEndLeg_apply i β y
    calc
      d.extension (s, (endpointBoundaryParameter β, y)) = d.extension (s, j (b z)) :=
        congrArg (fun p => d.extension (s, p)) hLeg.symm
      _ = boundary.toContinuousMap (s, b z) := d.extension_subspace s (b z)
      _ = HB (s, z) :=
        TopCat.Homotopy.descOfIsPushout_apply_inr sq HA HB h₀ h₁ hOverlap s z
      _ = raw.toContinuousMap (j (b z)) := by rfl
      _ = raw.toContinuousMap (endpointBoundaryParameter β, y) :=
        congrArg raw.toContinuousMap hLeg
  have hFixedZero (s : unitInterval) (y : SSet.toTop.obj Y) :
      d.extension (s, (0, y)) = raw.toContinuousMap (0, y) := by
    simpa only [endpointBoundaryParameter_zero] using hEnd s endpointBoundaryZero y
  have hFixedOne (s : unitInterval) (y : SSet.toTop.obj Y) :
      d.extension (s, (1, y)) = raw.toContinuousMap (1, y) := by
    simpa only [endpointBoundaryParameter_one] using hEnd s endpointBoundaryOne y
  let corrected : TopCat.Homotopy f₀ f₁ :=
    { toFun := fun p => d.extension (1, p)
      continuous_toFun := d.extension.continuous.comp
        (continuous_const.prodMk continuous_id)
      map_zero_left := fun y => (hFixedZero 1 y).trans (raw.apply_zero y)
      map_one_left := fun y => (hFixedOne 1 y).trans (raw.apply_one y) }
  let Q : ContinuousMap.HomotopyRel raw.toContinuousMap corrected.toContinuousMap
      (TopCat.homotopyEndpointFaces (SSet.toTop.obj Y)) :=
    { toContinuousMap := d.extension
      map_zero_left := d.extension_zero
      map_one_left := fun _ => rfl
      prop' := by
        intro s p hp
        rcases p with ⟨t, y⟩
        change t = 0 ∨ t = 1 at hp
        rcases hp with ht | ht
        · subst t
          exact hFixedZero s y
        · subst t
          exact hFixedOne s y }
  refine ⟨⟨{ corrected := corrected, comparison := Q }, ?_⟩⟩
  intro s t x
  exact hSide s t x

end SSet

end
