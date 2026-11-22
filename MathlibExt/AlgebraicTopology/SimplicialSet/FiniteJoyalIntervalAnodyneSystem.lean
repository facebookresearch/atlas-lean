/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalRightLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneMonomorphisms
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonomorphismProductCorners
public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Auxiliary anodyne maps and the finite-interval cylinder

The actual auxiliary lifting class contains every endpoint corner of a
monomorphism and is closed under pushout product with every monomorphism.
The boundary corner is the corresponding product with the interval boundary.
These give the two corner axioms for the specified exact product cylinder.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet.joyalInterval

variable {A B K L X Y : SSet.{u}}

local instance : auxiliaryAnodyneExtensions.{u}.RespectsIso :=
  inferInstanceAs (auxiliaryGenerators.{u}.rlp.llp.RespectsIso)

/-- Endpoint corners of all monomorphisms belong to the auxiliary left class. -/
lemma auxiliaryAnodyneExtensions.endpointCorner (i : A ⟶ B) [Mono i] (ε : Fin 2) :
    auxiliaryAnodyneExtensions (productPrecylinder.endpointCorner i ε) := by
  intro X Y p hp
  have hNF : auxiliaryNaiveFibrations p := by
    simpa only [auxiliaryNaiveFibrations_eq_generatorRlp] using hp
  have h := ((auxiliaryNaiveFibrations_iff_monomorphisms p).mp hNF).2 ε i
    (MorphismProperty.monomorphisms.infer_property i)
  exact (endpointCorner_hasLiftingProperty_iff i p ε).mpr h

private def endpointCornerArrowIso (i : A ⟶ B) (ε : Fin 2) :
    Arrow.mk (productPrecylinder.endpointCorner i ε) ≅ Arrow.mk (unitPoint ε) □ Arrow.mk i :=
  Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk (unitPoint ε))
    (f₁' := Arrow.mk (unitPoint ε)) (f₂ := Arrow.mk i)
    (endpointCornerPushoutObjObj i ε)
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (unitPoint ε) i)
    (Iso.refl _)

private lemma endpointPushoutProduct (i : A ⟶ B) [Mono i] (ε : Fin 2) :
    auxiliaryAnodyneExtensions (Arrow.mk (unitPoint ε) □ Arrow.mk i).hom :=
  (auxiliaryAnodyneExtensions.arrow_iso_iff (endpointCornerArrowIso i ε)).mp
    (auxiliaryAnodyneExtensions.endpointCorner i ε)

private lemma generatorPushoutProduct (i : A ⟶ B) (hi : auxiliaryGenerators i)
    (j : K ⟶ L) [Mono j] :
    auxiliaryAnodyneExtensions (Arrow.mk i □ Arrow.mk j).hom := by
  rcases hi with hi | hi
  · have hinner : innerAnodyneExtensions i := MorphismProperty.le_llp_rlp _ _ hi
    exact MorphismProperty.antitone_llp
      (MorphismProperty.antitone_rlp
        (show innerHornInclusions ≤ auxiliaryGenerators from fun _ _ _ h ↦ Or.inl h))
      _ (innerAnodyneExtensions_pushoutObjObjι'
        (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j) hinner)
  · cases hi with
    | mk k =>
      have hmono : Mono (Arrow.mk (boundary k.1).ι □ Arrow.mk j).hom :=
        (monomorphism_product_corner (boundary k.1).ι j).1
      have hAn := endpointPushoutProduct (Arrow.mk (boundary k.1).ι □ Arrow.mk j).hom k.2
      let e₀ : (Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} k.1).ι k.2) □
          Arrow.mk j) ≅ (Arrow.mk (unitPoint.{u} k.2) □ Arrow.mk (boundary.{u} k.1).ι) □
            Arrow.mk j :=
        (MonoidalCategory.Arrow.pushoutProduct.flip.obj (Arrow.mk j)).mapIso
          (endpointCornerArrowIso (boundary.{u} k.1).ι k.2)
      let e₁ : ((Arrow.mk (unitPoint.{u} k.2) □ Arrow.mk (boundary.{u} k.1).ι) □
          Arrow.mk j) ≅ Arrow.mk (unitPoint.{u} k.2) □
            (Arrow.mk (boundary.{u} k.1).ι □ Arrow.mk j) :=
        MonoidalCategory.Arrow.PushoutProduct.associator
          (C := SSet.{u}) (Arrow.mk (unitPoint.{u} k.2))
          (Arrow.mk (boundary.{u} k.1).ι) (Arrow.mk j)
      let e : (Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} k.1).ι k.2) □
          Arrow.mk j) ≅ Arrow.mk (unitPoint k.2) □
            (Arrow.mk (boundary k.1).ι □ Arrow.mk j) :=
        e₀ ≪≫ e₁
      exact (auxiliaryAnodyneExtensions.arrow_iso_iff e).mpr hAn

/-- The auxiliary class is stable under pushout product with any monomorphism. -/
lemma auxiliaryAnodyneExtensions.pushoutProduct (i : A ⟶ B)
    (hi : auxiliaryAnodyneExtensions i) (j : K ⟶ L) [Mono j] :
    auxiliaryAnodyneExtensions (Arrow.mk i □ Arrow.mk j).hom := by
  intro X Y p hp
  let Q := op (Arrow.mk j) ⋔ Arrow.mk p
  have hQ : auxiliaryGenerators.rlp Q.hom := by
    intro A' B' g hg
    have hgj : HasLiftingProperty (Arrow.mk g □ Arrow.mk j).hom p :=
      generatorPushoutProduct g hg j p hp
    exact MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mp hgj
  have hig : HasLiftingProperty i Q.hom := hi Q.hom hQ
  exact MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mpr hig

private def unitBoundary : (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}) ⟶ joyalInterval :=
  coprod.desc (unitPoint 0) (unitPoint 1)

private instance mono_unitBoundary : Mono unitBoundary.{u} := by
  have h : unitBoundary.{u} =
      coprod.map (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀.{u}).hom
        (isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀.{u}).hom ≫
          endpointCoprod.{u} := by
    apply coprod.hom_ext <;> simp [unitBoundary, unitPoint]
  rw [h]
  infer_instance

private def boundaryDomainIso (X : SSet.{u}) :
    X ⨿ X ≅ ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ⊗ X :=
  (asIso (coprod.map (λ_ X).inv (λ_ X).inv)) ≪≫
    asIso (coprodComparison (tensorRight X) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}))

private lemma boundaryDomainIso_hom_boundary (X : SSet.{u}) :
    (boundaryDomainIso X).hom ≫ unitBoundary ▷ X = (productPrecylinder.app X).i := by
  apply coprod.hom_ext
  · simpa [boundaryDomainIso, unitBoundary, coprodComparison,
      ← MonoidalCategory.comp_whiskerRight] using
      (productPrecylinder_endpoint_unitor X 0).symm
  · simpa [boundaryDomainIso, unitBoundary, coprodComparison,
      ← MonoidalCategory.comp_whiskerRight] using
      (productPrecylinder_endpoint_unitor X 1).symm

private lemma boundaryDomainIso_naturality (i : A ⟶ B) :
    (boundaryDomainIso A).hom ≫ ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ◁ i =
      coprod.map i i ≫ (boundaryDomainIso B).hom := by
  apply coprod.hom_ext
  · simp only [boundaryDomainIso, Iso.trans_hom, asIso_hom, Category.assoc,
      coprod.inl_map_assoc]
    have hA : (coprod.inl : (𝟙_ SSet.{u}) ⊗ A ⟶ _) ≫
        coprodComparison (tensorRight A) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) =
        (coprod.inl : (𝟙_ SSet.{u}) ⟶ _) ▷ A :=
      inl_coprodComparison (tensorRight A) (𝟙_ SSet.{u}) (𝟙_ SSet.{u})
    have hB : (coprod.inl : (𝟙_ SSet.{u}) ⊗ B ⟶ _) ≫
        coprodComparison (tensorRight B) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) =
        (coprod.inl : (𝟙_ SSet.{u}) ⟶ _) ▷ B :=
      inl_coprodComparison (tensorRight B) (𝟙_ SSet.{u}) (𝟙_ SSet.{u})
    have hA' := congrArg (fun f : (𝟙_ SSet.{u}) ⊗ A ⟶
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ⊗ A ↦
      (λ_ A).inv ≫ f ≫ ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ◁ i) hA
    have hB' := congrArg (fun f : (𝟙_ SSet.{u}) ⊗ B ⟶
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ⊗ B ↦
      i ≫ (λ_ B).inv ≫ f) hB
    apply hA'.trans
    apply Eq.trans _ hB'.symm
    have hex : (coprod.inl : (𝟙_ SSet.{u}) ⟶ _) ▷ A ≫
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ◁ i =
        (𝟙_ SSet.{u}) ◁ i ≫ (coprod.inl : (𝟙_ SSet.{u}) ⟶ _) ▷ B :=
      (whisker_exchange (coprod.inl : (𝟙_ SSet.{u}) ⟶
        (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) i).symm
    calc
      _ = (λ_ A).inv ≫ ((𝟙_ SSet.{u}) ◁ i ≫ coprod.inl ▷ B) :=
        congrArg ((λ_ A).inv ≫ ·) hex
      _ = i ≫ (λ_ B).inv ≫ coprod.inl ▷ B := by
        have h := congrArg (fun f : A ⟶ (𝟙_ SSet.{u}) ⊗ B ↦
          f ≫ (coprod.inl : (𝟙_ SSet.{u}) ⟶
            (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ▷ B)
          (leftUnitor_inv_naturality i).symm
        simpa only [Category.assoc] using h
  · simp only [boundaryDomainIso, Iso.trans_hom, asIso_hom, Category.assoc,
      coprod.inr_map_assoc]
    have hA : (coprod.inr : (𝟙_ SSet.{u}) ⊗ A ⟶ _) ≫
        coprodComparison (tensorRight A) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) =
        (coprod.inr : (𝟙_ SSet.{u}) ⟶ _) ▷ A :=
      inr_coprodComparison (tensorRight A) (𝟙_ SSet.{u}) (𝟙_ SSet.{u})
    have hB : (coprod.inr : (𝟙_ SSet.{u}) ⊗ B ⟶ _) ≫
        coprodComparison (tensorRight B) (𝟙_ SSet.{u}) (𝟙_ SSet.{u}) =
        (coprod.inr : (𝟙_ SSet.{u}) ⟶ _) ▷ B :=
      inr_coprodComparison (tensorRight B) (𝟙_ SSet.{u}) (𝟙_ SSet.{u})
    have hA' := congrArg (fun f : (𝟙_ SSet.{u}) ⊗ A ⟶
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ⊗ A ↦
      (λ_ A).inv ≫ f ≫ ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ◁ i) hA
    have hB' := congrArg (fun f : (𝟙_ SSet.{u}) ⊗ B ⟶
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ⊗ B ↦
      i ≫ (λ_ B).inv ≫ f) hB
    apply hA'.trans
    apply Eq.trans _ hB'.symm
    have hex : (coprod.inr : (𝟙_ SSet.{u}) ⟶ _) ▷ A ≫
        ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ◁ i =
        (𝟙_ SSet.{u}) ◁ i ≫ (coprod.inr : (𝟙_ SSet.{u}) ⟶ _) ▷ B :=
      (whisker_exchange (coprod.inr : (𝟙_ SSet.{u}) ⟶
        (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) i).symm
    calc
      _ = (λ_ A).inv ≫ ((𝟙_ SSet.{u}) ◁ i ≫ coprod.inr ▷ B) :=
        congrArg ((λ_ A).inv ≫ ·) hex
      _ = i ≫ (λ_ B).inv ≫ coprod.inr ▷ B := by
        have h := congrArg (fun f : A ⟶ (𝟙_ SSet.{u}) ⊗ B ↦
          f ≫ (coprod.inr : (𝟙_ SSet.{u}) ⟶
            (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) ▷ B)
          (leftUnitor_inv_naturality i).symm
        simpa only [Category.assoc] using h

private def boundaryCornerPushoutObjObj (i : A ⟶ B) :
    (curriedTensor SSet.{u}).PushoutObjObj unitBoundary i where
  pt := pushout (coprod.map i i) (productPrecylinder.app A).i
  inl := pushout.inr _ _
  inr := (boundaryDomainIso B).inv ≫ pushout.inl _ _
  isPushout := by
    refine (IsPushout.of_hasPushout (coprod.map i i) (productPrecylinder.app A).i).flip.of_iso
      (boundaryDomainIso A) (Iso.refl _) (boundaryDomainIso B) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (boundaryDomainIso_hom_boundary A).symm
    · exact (boundaryDomainIso_naturality i).symm
    · simp
    · simp
  ι := productPrecylinder.boundaryCorner i
  inl_ι := by simp
  inr_ι := by
    rw [Category.assoc, Precylinder.inl_boundaryCorner]
    rw [← boundaryDomainIso_hom_boundary B]
    simp

/-- Boundary-cylinder corners of actual auxiliary anodyne maps are anodyne. -/
lemma auxiliaryAnodyneExtensions.boundaryCorner (i : A ⟶ B)
    (hi : auxiliaryAnodyneExtensions i) :
    auxiliaryAnodyneExtensions (productPrecylinder.boundaryCorner i) := by
  let sq := boundaryCornerPushoutObjObj i
  let e : Arrow.mk sq.ι ≅ Arrow.mk unitBoundary □ Arrow.mk i :=
    Functor.PushoutObjObj.ι_iso_of_iso_left
      (F := curriedTensor SSet.{u}) (f₁ := Arrow.mk unitBoundary)
      (f₁' := Arrow.mk unitBoundary) (f₂ := Arrow.mk i) sq
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) unitBoundary i)
      (Iso.refl _)
  have hAn := auxiliaryAnodyneExtensions.pushoutProduct i hi unitBoundary
  have hflip : auxiliaryAnodyneExtensions (Arrow.mk unitBoundary □ Arrow.mk i).hom :=
    (auxiliaryAnodyneExtensions.arrow_iso_iff
      (MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk i) (Arrow.mk unitBoundary))).mp hAn
  exact (auxiliaryAnodyneExtensions.arrow_iso_iff e).mpr hflip

/-- The actual finite-interval class satisfies all native anodyne-system fields. -/
instance productPrecylinder_isAnodyneSystem :
    productPrecylinder.{u}.IsAnodyneSystem.{u} auxiliaryAnodyneExtensions where
  le_monomorphisms := auxiliaryAnodyneExtensions_le_monomorphisms
  exists_generators := by
    refine ⟨AuxiliaryGeneratorIndex.{u},
      fun i ↦ (auxiliaryGeneratorArrow i).left,
      fun i ↦ (auxiliaryGeneratorArrow i).right,
      fun i ↦ (auxiliaryGeneratorArrow i).hom, mono_auxiliaryGeneratorArrow, ?_⟩
    change auxiliaryGenerators.rlp.llp = _
    rw [auxiliaryGenerators_eq_ofHoms]
  endpoint_corner := auxiliaryAnodyneExtensions.endpointCorner
  boundary_corner := auxiliaryAnodyneExtensions.boundaryCorner

end SSet.joyalInterval
