/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialUnitScalarFunctor
import Mathlib.CategoryTheory.Enriched.HomCongr

/-!
# Canonical enriched Hom isomorphisms retain every scalar composition map

The Iso.eHomCongr has its same complete Hom maps and
both inverse identities. Read those maps in the canonical 
scalar categories using the unit-coefficient functor. The full
unit and all two-input composition equations follow there by
the supplied isomorphism identities, for every simplex.
No component-only or Kan-space replacement is used.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace SSet
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- Every scalar operator retains the same full unit-coefficient map. -/
theorem unitScalarFunctor_operator {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    {x y : ForgetEnrichment SSet.{u} C} (f : x ⟶ y) :
    (scalarOperator θ).map ((unitScalarFunctor C q).map f) = (unitScalarFunctor C r).map f :=
  (NatTrans.naturality_apply (ForgetEnrichment.homTo SSet.{u} f) θ PUnit.unit).symm

/-- The same canonical enriched Hom isomorphism reads as its scalar
conjugation. -/
theorem homCongr_scalar (q : SimplexCategoryᵒᵖ)
    {x y x' y' : ForgetEnrichment SSet.{u} C} (α : x ≅ x') (β : y ≅ y')
    (h : (x ⟶[SSet.{u}] y).obj q) :
    (Iso.eHomCongr SSet.{u} α β).hom.app q h =
      (unitScalarFunctor C q).map α.inv ≫ h ≫ (unitScalarFunctor C q).map β.hom := by
  let Fq := unitScalarFunctor C q
  let f : Fq.obj x ⟶ Fq.obj y := h
  let a := Fq.mapIso α
  let b := Fq.mapIso β
  change (a.inv ≫ f) ≫ b.hom = a.inv ≫ f ≫ b.hom
  exact Category.assoc _ _ _

/-- The canonical same Hom isomorphism retains every enriched identity map. -/
theorem homCongr_identity {x x' : ForgetEnrichment SSet.{u} C} (α : x ≅ x') :
    eId SSet.{u} x ≫ (Iso.eHomCongr SSet.{u} α α).hom = eId SSet.{u} x' := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  change (Iso.eHomCongr SSet.{u} α α).hom.app q ((eId SSet.{u} x).app q PUnit.unit) =
    (eId SSet.{u} x').app q PUnit.unit
  rw [homCongr_scalar C]
  let a := (unitScalarFunctor C q).mapIso α
  change a.inv ≫ 𝟙 ((unitScalarFunctor C q).obj x) ≫ a.hom = 𝟙 ((unitScalarFunctor C q).obj x')
  exact (congrArg (fun h => a.inv ≫ h) (Category.id_comp a.hom)).trans a.inv_hom_id

/-- The canonical same Hom isomorphisms preserve the enriched
Composition object. -/
theorem homCongr_composition {x y z x' y' z' : ForgetEnrichment SSet.{u} C}
    (α : x ≅ x') (β : y ≅ y') (γ : z ≅ z') :
    eComp SSet.{u} x y z ≫ (Iso.eHomCongr SSet.{u} α γ).hom =
      ((Iso.eHomCongr SSet.{u} α β).hom ⊗ₘ (Iso.eHomCongr SSet.{u} β γ).hom) ≫
        eComp SSet.{u} x' y' z' := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  change (Iso.eHomCongr SSet.{u} α γ).hom.app q ((eComp SSet.{u} x y z).app q p) =
    (eComp SSet.{u} x' y' z').app q
      ((Iso.eHomCongr SSet.{u} α β).hom.app q p.1, (Iso.eHomCongr SSet.{u} β γ).hom.app q p.2)
  rw [homCongr_scalar, homCongr_scalar, homCongr_scalar]
  let Fq := unitScalarFunctor C q
  let f : Fq.obj x ⟶ Fq.obj y := p.1
  let g : Fq.obj y ⟶ Fq.obj z := p.2
  let a := Fq.mapIso α
  let b := Fq.mapIso β
  let c := Fq.mapIso γ
  change a.inv ≫ (f ≫ g) ≫ c.hom = (a.inv ≫ f ≫ b.hom) ≫ (b.inv ≫ g ≫ c.hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SSet
