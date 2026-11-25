/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Structured replacements and their original underlying comparisons

The complete given factor records construct the actual Q and R functors in
the original structured and base models. Their original counits and units
give the whole underlying weak zigzags. Only creation of weak equivalences
and fibrations is used; underlying cofibrancy is not asserted.

The original forgetful functor preserves every weak map. Its direct
localization is naturally isomorphic to its actual chosen right derived
functor on the generated R objects, at all original objects and morphisms.

Source: the structured replacement contract R1 in the spectra blueprint;
Hovey, Model Categories, Chapter 1; Schwede--Shipley, Lemma A.3.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.Functor

namespace HomotopicalAlgebra.StructuredReplacementComparisons

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  (U : D ⥤ C)
  (FcC : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (FfC : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (FcD : FunctorialFactorizationData (cofibrations D) (trivialFibrations D))
  (FfD : FunctorialFactorizationData (trivialCofibrations D) (fibrations D))

local notation "qC" => GeneratedFunctorialReplacements.replacementsOfFactors FcC FfC
local notation "qD" => GeneratedFunctorialReplacements.replacementsOfFactors FcD FfD
local notation "πC" => MorphismProperty.Q (weakEquivalences C)
local notation "πD" => MorphismProperty.Q (weakEquivalences D)
local notation "HC" => MorphismProperty.Localization (weakEquivalences C)
local notation "HD" => MorphismProperty.Localization (weakEquivalences D)

/-- The original structured Q counit is forgotten as a whole natural transformation. -/
def underlyingQCounit : (qD).Q ⋙ U ⟶ U :=
  whiskerRight (qD).q U ≫ U.leftUnitor.hom

/-- The original base Q counit gives the other whole leg of the same underlying zigzag. -/
def baseQCounit : U ⋙ (qC).Q ⟶ U :=
  whiskerLeft U (qC).q ≫ U.rightUnitor.hom

omit [ModelCategory C] in
/-- The structured Q leg has exactly the original forgotten counit component. -/
theorem underlyingQCounit_app (X : D) :
    (underlyingQCounit U FcD FfD).app X = U.map ((qD).q.app X) := by
  simp only [underlyingQCounit, NatTrans.comp_app, whiskerRight_app,
    Functor.leftUnitor_hom_app]
  erw [Category.comp_id]

omit [ModelCategory D] in
/-- The base Q leg has exactly the original base counit component. -/
theorem baseQCounit_app (X : D) :
    (baseQCounit U FcC FfC).app X = (qC).q.app (U.obj X) := by
  simp only [baseQCounit, NatTrans.comp_app, whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  erw [Category.comp_id]

/-- The original structured R unit is forgotten as a whole natural transformation. -/
def underlyingRUnit : U ⟶ (qD).R ⋙ U :=
  U.leftUnitor.inv ≫ whiskerRight (qD).r U

/-- The forgotten structured R object maps to its actual base R replacement. -/
def fibrantZigzagLeft : (qD).R ⋙ U ⟶ ((qD).R ⋙ U) ⋙ (qC).R :=
  ((qD).R ⋙ U).rightUnitor.inv ≫ whiskerLeft ((qD).R ⋙ U) (qC).r

/-- Applying the original base R to the forgotten structured unit gives the other zigzag leg. -/
def fibrantZigzagRight : U ⋙ (qC).R ⟶ ((qD).R ⋙ U) ⋙ (qC).R :=
  whiskerRight (underlyingRUnit U FcD FfD) (qC).R

omit [ModelCategory C] in
/-- The original structured unit is the complete source component of the forgotten R map. -/
theorem underlyingRUnit_app (X : D) :
    (underlyingRUnit U FcD FfD).app X = U.map ((qD).r.app X) := by
  simp only [underlyingRUnit, NatTrans.comp_app, whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp]

/-- The first fibrant zigzag leg is the same original base R unit. -/
theorem fibrantZigzagLeft_app (X : D) :
    (fibrantZigzagLeft U FcC FfC FcD FfD).app X = (qC).r.app (U.obj ((qD).R.obj X)) := by
  simp only [fibrantZigzagLeft, NatTrans.comp_app, whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp]
  rfl

/-- The second fibrant zigzag leg is the original base R-map of the forgotten structured R unit. -/
theorem fibrantZigzagRight_app (X : D) :
    (fibrantZigzagRight U FcC FfC FcD FfD).app X = (qC).R.map (U.map ((qD).r.app X)) := by
  rw [fibrantZigzagRight, whiskerRight_app, underlyingRUnit_app]

variable (hW : weakEquivalences D = (weakEquivalences C).inverseImage U)

include hW in
/-- Creation of weak equivalences proves weakness of every actual forgotten Q counit. -/
theorem underlyingQCounit_weak (X : D) :
    weakEquivalences C ((underlyingQCounit U FcD FfD).app X) := by
  rw [underlyingQCounit_app]
  have h := ((qD).q_trivialFibration X).2
  rw [hW] at h
  exact h

omit [ModelCategory D] in
/-- Every actual base Q leg in the original underlying zigzag is weak. -/
theorem baseQCounit_weak (X : D) :
    weakEquivalences C ((baseQCounit U FcC FfC).app X) := by
  rw [baseQCounit_app]
  exact ((qC).q_trivialFibration (U.obj X)).2

include hW in
/-- Every original forgotten structured R unit is weak by the created class. -/
theorem underlyingRUnit_weak (X : D) :
    weakEquivalences C ((underlyingRUnit U FcD FfD).app X) := by
  rw [underlyingRUnit_app]
  have h := ((qD).r_trivialCofibration X).2
  rw [hW] at h
  exact h

/-- The first actual fibrant comparison leg is weak at every original structured object. -/
theorem fibrantZigzagLeft_weak (X : D) :
    weakEquivalences C ((fibrantZigzagLeft U FcC FfC FcD FfD).app X) := by
  rw [fibrantZigzagLeft_app]
  exact ((qC).r_trivialCofibration _).2

include hW in
/-- The second actual fibrant comparison leg is weak by the original base R preservation. -/
theorem fibrantZigzagRight_weak (X : D) :
    weakEquivalences C ((fibrantZigzagRight U FcC FfC FcD FfD).app X) := by
  rw [fibrantZigzagRight_app]
  have h := underlyingRUnit_weak U FcD FfD hW X
  rw [underlyingRUnit_app] at h
  exact (qC).r_map_weak _ h

/-- The entire original underlying Q zigzag gives a natural isomorphism after base localization. -/
def underlyingQComparisonIso : ((qD).Q ⋙ U) ⋙ πC ≅ (U ⋙ (qC).Q) ⋙ πC := by
  let tD := whiskerRight (underlyingQCounit U FcD FfD) πC
  let tC := whiskerRight (baseQCounit U FcC FfC) πC
  let : ∀ X : D, IsIso (tD.app X) := fun X =>
    Localization.inverts πC (weakEquivalences C) _ (underlyingQCounit_weak U FcD FfD hW X)
  let : ∀ X : D, IsIso (tC.app X) := fun X =>
    Localization.inverts πC (weakEquivalences C) _ (baseQCounit_weak U FcC FfC X)
  let : IsIso tD := NatIso.isIso_of_isIso_app _
  let : IsIso tC := NatIso.isIso_of_isIso_app _
  exact asIso tD ≪≫ (asIso tC).symm

/-- Both original fibrant zigzag legs give the whole natural base-localized R comparison. -/
def underlyingRComparisonIso : ((qD).R ⋙ U) ⋙ πC ≅ (U ⋙ (qC).R) ⋙ πC := by
  let tD := whiskerRight (fibrantZigzagLeft U FcC FfC FcD FfD) πC
  let tC := whiskerRight (fibrantZigzagRight U FcC FfC FcD FfD) πC
  let : ∀ X : D, IsIso (tD.app X) := fun X =>
    Localization.inverts πC (weakEquivalences C) _ (fibrantZigzagLeft_weak U FcC FfC FcD FfD X)
  let : ∀ X : D, IsIso (tC.app X) := fun X =>
    Localization.inverts πC (weakEquivalences C) _ (fibrantZigzagRight_weak U FcC FfC FcD FfD hW X)
  let : IsIso tD := NatIso.isIso_of_isIso_app _
  let : IsIso tC := NatIso.isIso_of_isIso_app _
  exact asIso tD ≪≫ (asIso tC).symm

/-- The original forgetful functor acts directly on every original weak-localized object and arrow.
-/
def localizedForgetful : HD ⥤ HC :=
  Localization.Construction.lift (U ⋙ πC) (by
    intro X Y f hf
    have h := hf
    rw [hW] at h
    exact Localization.inverts πC (weakEquivalences C) _ h)

/-- The whole original forgetful functor is retained before source localization. -/
theorem localizedForgetful_projection : πD ⋙ localizedForgetful U hW = U ⋙ πC :=
  Localization.Construction.fac _ _

instance localizedForgetfulLifting :
    Localization.Lifting πD (weakEquivalences D) (U ⋙ πC) (localizedForgetful U hW) :=
  ⟨eqToIso (localizedForgetful_projection U hW)⟩

variable {L : C ⥤ D} (adj : L ⊣ U)
  (hF : fibrations D = (fibrations C).inverseImage U)

include hW hF in
/-- The actual free/forget adjunction is Quillen from the two created classes. -/
theorem actualQuillen : adj.IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    exact hF.le f hf
  · intro X Y f hf
    change (fibrations D ⊓ weakEquivalences D) f at hf
    rw [hF, hW] at hf
    exact hf

include hW hF adj in
/-- The forgotten original structured R object is fibrant; no underlying Q cofibrancy is inferred.
-/
theorem underlyingR_fibrant (X : D) : IsFibrant (U.obj ((qD).R.obj X)) := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) ((qD).r_fibrant X)

/-- The original structured R factory computes the actual chosen right derived forgetful functor. -/
def chosenRight : HD ⥤ HC := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact DerivedFunctorCoherence.right adj (qD)

instance chosenRightLifting :
    Localization.Lifting πD (weakEquivalences D) ((qD).R ⋙ U ⋙ πC)
      (chosenRight U FcD FfD hW adj hF) := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact ⟨eqToIso (DerivedFunctorCoherence.right_projection adj (qD))⟩

/-- The complete original forgotten R unit is an Iso after base projection at every source object.
-/
def rawRightComparisonIso : U ⋙ πC ≅ (qD).R ⋙ U ⋙ πC := by
  let t := whiskerRight (underlyingRUnit U FcD FfD) πC
  let : ∀ X : D, IsIso (t.app X) := fun X =>
    Localization.inverts πC (weakEquivalences C) _ (underlyingRUnit_weak U FcD FfD hW X)
  let : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

/-- The full localized forgetful functor agrees naturally with its actual chosen right derived
functor. -/
def derivedForgetfulIso : localizedForgetful U hW ≅ chosenRight U FcD FfD hW adj hF :=
  Localization.liftNatIso πD (weakEquivalences D) (U ⋙ πC) ((qD).R ⋙ U ⋙ πC)
    (localizedForgetful U hW) (chosenRight U FcD FfD hW adj hF)
    (rawRightComparisonIso U FcD FfD hW)

/-- The chosen right functor has its complete right derived universal property with the original
R-unit comparison. -/
theorem chosenRight_isDerived :
    letI : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
    (chosenRight U FcD FfD hW adj hF).IsRightDerivedFunctor
      (DerivedFunctorCoherence.rightComparison adj (qD)) (weakEquivalences D) := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact DerivedFunctorCoherence.rightIsDerived adj (qD)

/-- Every original represented arrow retains its actual structured R-map and original forgetful map.
-/
theorem chosenRight_map {X Y : D} (f : X ⟶ Y) :
    (chosenRight U FcD FfD hW adj hF).map ((πD).map f) =
      (πC).map (U.map ((qD).R.map f)) := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact DerivedFunctorCoherence.right_map adj (qD) f

/-- The direct localized forgetful map is the original forgetful map on every source arrow. -/
theorem localizedForgetful_map {X Y : D} (f : X ⟶ Y) :
    (localizedForgetful U hW).map ((πD).map f) = (πC).map (U.map f) :=
  Functor.congr_hom (localizedForgetful_projection U hW) f

/-- The source component of the whole raw comparison is the original forgotten R-unit map. -/
theorem rawRightComparisonIso_hom_app (X : D) :
    (rawRightComparisonIso U FcD FfD hW).hom.app X = (πC).map (U.map ((qD).r.app X)) := by
  change (πC).map ((underlyingRUnit U FcD FfD).app X) = _
  rw [underlyingRUnit_app]

/-- Every original projected object retains the actual source R-unit and both complete liftings. -/
theorem derivedForgetfulIso_hom_app (X : D) :
    (derivedForgetfulIso U FcD FfD hW adj hF).hom.app ((πD).obj X) =
      (Localization.Lifting.iso πD (weakEquivalences D) (U ⋙ πC) (localizedForgetful U hW)).hom.app
        X ≫
        (πC).map (U.map ((qD).r.app X)) ≫
          (Localization.Lifting.iso πD (weakEquivalences D) ((qD).R ⋙ U ⋙ πC)
            (chosenRight U FcD FfD hW adj hF)).inv.app X := by
  rw [derivedForgetfulIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    rawRightComparisonIso_hom_app]

/-- Complete constructed replacement data and full underlying comparisons for an actual structured
model. -/
structure ComparisonData where
  /-- The constructed original base Q/R and both complete original factor records. -/
  base : GeneratedFunctorialReplacements.Data (C := C)
  /-- The constructed original structured Q/R and both complete original factor records. -/
  structured : GeneratedFunctorialReplacements.Data (C := D)
  /-- The whole actual underlying cofibrant replacement comparison. -/
  qComparison : (structured.Q ⋙ U) ⋙ πC ≅ (U ⋙ base.Q) ⋙ πC
  /-- The whole actual underlying fibrant replacement comparison. -/
  rComparison : (structured.R ⋙ U) ⋙ πC ≅ (U ⋙ base.R) ⋙ πC
  /-- The original forgetful functor localized directly. -/
  direct : HD ⥤ HC
  /-- The chosen right derived forgetful functor. -/
  chosen : HD ⥤ HC
  /-- The full natural comparison between those original functors. -/
  derivedIso : direct ≅ chosen
  /-- The complete original structured R-unit comparison. -/
  rightComparison : U ⋙ πC ⟶ πD ⋙ chosen
  /-- Its full right derived universal property. -/
  isRightDerived : chosen.IsRightDerivedFunctor rightComparison (weakEquivalences D)

/-- The four actual original factor records and created classes construct the whole R1 comparison
package. -/
def construct : ComparisonData U := by
  let : adj.IsQuillenAdjunction := actualQuillen U hW adj hF
  exact
    { base := qC
      structured := qD
      qComparison := underlyingQComparisonIso U FcC FfC FcD FfD hW
      rComparison := underlyingRComparisonIso U FcC FfC FcD FfD hW
      direct := localizedForgetful U hW
      chosen := chosenRight U FcD FfD hW adj hF
      derivedIso := derivedForgetfulIso U FcD FfD hW adj hF
      rightComparison := DerivedFunctorCoherence.rightComparison adj (qD)
      isRightDerived := chosenRight_isDerived U FcD FfD hW adj hF }

/-- The complete constructed package retains all four original factor records without changing any
Arrow field. -/
theorem construct_original_factors :
    (construct U FcC FfC FcD FfD hW adj hF).base.cofibrantFactor = FcC ∧
      (construct U FcC FfC FcD FfD hW adj hF).base.fibrantFactor = FfC ∧
      (construct U FcC FfC FcD FfD hW adj hF).structured.cofibrantFactor = FcD ∧
      (construct U FcC FfC FcD FfD hW adj hF).structured.fibrantFactor = FfD :=
  ⟨rfl, rfl, rfl, rfl⟩

end HomotopicalAlgebra.StructuredReplacementComparisons
