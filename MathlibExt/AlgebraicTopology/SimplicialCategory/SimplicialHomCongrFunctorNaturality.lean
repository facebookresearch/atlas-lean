/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialHomCongrFullMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialUnitScalarFunctorNaturality

/-!
# The SAME whole enriched Hom isomorphism commutes with every original full functor map

Canonical full Hom congruence is read in the original scalar categories.
The SAME original scalarFunctor preserves all coefficient compositions
and retains every unit-coordinate image. This proves the full enriched
map square, at independent source, target and coefficient universes.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D]

/-- Every SAME original enriched functor preserves the actual full canonical source and
target Hom isomorphisms. -/
theorem homCongr_functor_natural (F : EnrichedFunctor SSet.{u} C D)
    {x y x' y' : ForgetEnrichment SSet.{u} C} (α : x ≅ x') (β : y ≅ y') :
    F.map (ForgetEnrichment.to SSet.{u} x) (ForgetEnrichment.to SSet.{u} y) ≫
        (Iso.eHomCongr SSet.{u} (F.forget.mapIso α) (F.forget.mapIso β)).hom =
      (Iso.eHomCongr SSet.{u} α β).hom ≫
        F.map (ForgetEnrichment.to SSet.{u} x') (ForgetEnrichment.to SSet.{u} y') := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  let U := unitScalarFunctor C q
  let V := unitScalarFunctor D q
  let Q := scalarFunctor F q
  let h : U.obj x ⟶ U.obj y := p
  let a := U.mapIso α
  let b := U.mapIso β
  have he := homCongr_scalar D q (F.forget.mapIso α) (F.forget.mapIso β)
    ((F.map (ForgetEnrichment.to SSet.{u} x) (ForgetEnrichment.to SSet.{u} y)).app q p)
  have hs := homCongr_scalar C q α β p
  have ha : V.map (F.forget.map α.inv) = Q.map a.inv := unitScalarFunctor_forget_map F q α.inv
  have hb : V.map (F.forget.map β.hom) = Q.map b.hom := unitScalarFunctor_forget_map F q β.hom
  have hm : Q.map (a.inv ≫ h ≫ b.hom) = Q.map a.inv ≫ Q.map h ≫ Q.map b.hom :=
    (Q.map_comp _ _).trans (congrArg (fun h => Q.map a.inv ≫ h) (Q.map_comp _ _))
  have hc : V.map (F.forget.map α.inv) ≫ Q.map h ≫ V.map (F.forget.map β.hom) =
      Q.map (a.inv ≫ h ≫ b.hom) :=
    ((congrArg₂ (fun f g => f ≫ Q.map h ≫ g) ha hb).trans hm.symm)
  exact he.trans (hc.trans (congrArg Q.map hs.symm))

end SSet
