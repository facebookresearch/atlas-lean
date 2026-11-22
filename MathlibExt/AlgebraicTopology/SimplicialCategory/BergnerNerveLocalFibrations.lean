/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerLocalClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentComponentHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveInnerFibration
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveTrivialFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations

/-!
# Actual Bergner local fibrations give categorical fibrations of the same nerve

At genuinely locally Kan original targets, the actual scalar fibration
data makes the source locally Kan. The original component readback is
fully faithful and bijective on individual objects, so its genuine strict
inverse transports the same component isofibration to the actual nerve
homotopy-category functor. The full original nerve is therefore a
categorical fibration. The original global C0 right class gives genuine
nerve boundary RLP at the same targets. No enriched model or Quillen
equivalence is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner
open CoherentRealization

/-- The original coherent-nerve component readback is bijective on the SAME individual original objects. -/
theorem componentRead_objects_bijective (C : Carrier.{u}) :
    Function.Bijective (ComponentHomotopyCategory.readFunctor C).obj := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := ComponentHomotopyCategory.object_surjective C a
    obtain ⟨y, rfl⟩ := ComponentHomotopyCategory.object_surjective C b
    have hxy : x = y := h
    exact congrArg (MappingHoHom.object (C := C)) hxy
  · intro x
    exact ⟨MappingHoHom.object x, ComponentHomotopyCategory.readFunctor_obj C x⟩

/-- Local Kan Homs make the SAME original readback a strict category isomorphism, with its actual object bijection. -/
theorem componentRead_isIso (C : Carrier.{u})
    (hC : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    (ComponentHomotopyCategory.readFunctor C).IsIso := {
  faithful := (ComponentHomotopyCategory.fullyFaithful C hC).faithful
  full := (ComponentHomotopyCategory.fullyFaithful C hC).full
  bijective_obj := componentRead_objects_bijective C }

private theorem source_hom_kan {C D : Carrier.{u}} (F : C ⟶ D)
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hF : ∀ x y : C, Fibration (F.map x y)) (x y : C) : SSet.KanComplex (x ⟶[SSet.{u}] y) := by
  let _ := hD (F.obj x) (F.obj y)
  let _ := hF x y
  exact isFibrant_of_fibration (F.map x y)

/-- The SAME ordinary homotopy-category nerve map lifts actual isomorphisms from the original component-fibration
data. -/
theorem localFibration_nerve_hoIsofibration {C D : Carrier.{u}} (F : C ⟶ D)
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) (hF : localFibrations F) :
    (SSet.mapHomotopyCategory (coherentNerveFunctor.map F)).IsIsofibration := by
  let hC := source_hom_kan F hD hF.1
  let _ := componentRead_isIso C hC
  let _ := componentRead_isIso D hD
  let _ : (ComponentCategory.mapFunctor F).IsIsofibration := hF.2
  let R := ComponentHomotopyCategory.readFunctor C
  let S := ComponentHomotopyCategory.readFunctor D
  let eD := S.asIsomorphism
  let N := SSet.mapHomotopyCategory (coherentNerveFunctor.map F)
  have hIso : ((R ⋙ ComponentCategory.mapFunctor F) ⋙ eD.inverse).IsIsofibration := by infer_instance
  have hn : N ⋙ S = R ⋙ ComponentCategory.mapFunctor F := ComponentHomotopyCategory.naturality F
  have hL : (N ⋙ S) ⋙ eD.inverse = N :=
    (CategoryTheory.Functor.assoc N S eD.inverse).trans
      ((congrArg (fun G => N ⋙ G) eD.unit_eq.symm).trans (CategoryTheory.Functor.comp_id N))
  have hEq : N = (R ⋙ ComponentCategory.mapFunctor F) ⋙ eD.inverse :=
    hL.symm.trans (congrArg (fun G => G ⋙ eD.inverse) hn)
  exact (congrArg (fun G : (coherentNerveFunctor.obj C).HomotopyCategory ⥤
    (coherentNerveFunctor.obj D).HomotopyCategory => G.IsIsofibration) hEq).mpr hIso

/-- An actual original Bergner local fibration into a locally Kan target gives a categorical fibration of its SAME
full coherent nerve. -/
theorem localFibration_nerve_categoricalFibration {C D : Carrier.{u}} (F : C ⟶ D)
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) (hF : localFibrations F) :
    SSet.categoricalFibrations (coherentNerveFunctor.map F) := by
  let hC := source_hom_kan F hD hF.1
  let _ := coherentNerve_quasicategory C hC
  let _ := coherentNerve_quasicategory D hD
  exact (SSet.categoricalFibrations_iff_innerFibration_and_hoIsofibration _).mpr
    ⟨NerveInnerFibration.innerFibration F hF.1, localFibration_nerve_hoIsofibration F hD hF⟩

/-- The genuine global generating-cofibration right class gives full boundary RLP of the SAME original nerve at a
locally Kan target. -/
theorem generatingCofibrations_right_nerve_boundaryRLP {C D : Carrier.{u}} (F : C ⟶ D)
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) (hF : generatingCofibrations.rlp F) :
    SSet.modelCategoryQuillen.I.rlp (coherentNerveFunctor.map F) := by
  have h := (generatingCofibrations_rlp_original_iff F).mp hF
  exact NerveTrivialFibrations.boundaryRLP F hD h.1 h.2

/-- Every original simplicial mono lifts through that SAME full nerve; the original global generator right class
supplies the lift input. -/
theorem generatingCofibrations_right_nerve_mono_lifting {C D : Carrier.{u}} (F : C ⟶ D)
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) (hF : generatingCofibrations.rlp F)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] : HasLiftingProperty i (coherentNerveFunctor.map F) := by
  have h := (generatingCofibrations_rlp_original_iff F).mp hF
  exact NerveTrivialFibrations.hasLiftingProperty_mono F hD h.1 h.2 i

end CategoryTheory.SimplicialEnrichment.Bergner
