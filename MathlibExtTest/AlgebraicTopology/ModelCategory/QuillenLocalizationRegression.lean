/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# A localization regression for the derived equivalence of a Quillen equivalence

The model structure on `Type` has every map a weak equivalence, the isomorphisms as
cofibrations and every map a fibration. It is installed only through local instances.

* `Empty → Unit` is a weak equivalence that is not an isomorphism; its image under the
  localization functor `(weakEquivalences Type).Q` is an isomorphism.
* `Empty` and `Unit` are not isomorphic, but become isomorphic after localization.
* For the Quillen adjunction `Typeᵒᵖᵒᵖ ≌ Type` with these weak equivalences, the canonical
  derived comparison at `Empty` is an isomorphism onto the localized `Empty`, the derived
  functor of the derived equivalence sends the localized non-isomorphism to an
  isomorphism, and the five provider statements hold.
-/

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra Opposite

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenLocalizationRegression

/-- Every map in `Type` is a weak equivalence. -/
@[instance_reducible]
def allWeakEquivalences : CategoryWithWeakEquivalences (Type) := ⟨⊤⟩

/-- The cofibrations in `Type` are the isomorphisms. -/
@[instance_reducible]
def isoCofibrations : CategoryWithCofibrations (Type) := ⟨isomorphisms _⟩

/-- Every map in `Type` is a fibration. -/
@[instance_reducible]
def allFibrations : CategoryWithFibrations (Type) := ⟨⊤⟩

attribute [local instance] allWeakEquivalences isoCofibrations allFibrations

lemma top_isStableUnderRetracts : (⊤ : MorphismProperty (Type)).IsStableUnderRetracts :=
  ⟨fun _ _ => trivial⟩

lemma isIso_of_cofibration {X Y : Type} (f : X ⟶ Y) [h : Cofibration f] : IsIso f :=
  (cofibration_iff f).1 h

/-- `Type` with all maps as weak equivalences, isomorphisms as cofibrations and all maps as
fibrations is a model category. -/
@[instance_reducible]
def contractibleModel : ModelCategory (Type) where
  categoryWithFibrations := allFibrations
  categoryWithCofibrations := isoCofibrations
  categoryWithWeakEquivalences := allWeakEquivalences
  cm2 := inferInstanceAs (⊤ : MorphismProperty (Type)).HasTwoOutOfThreeProperty
  cm3a := top_isStableUnderRetracts
  cm3b := top_isStableUnderRetracts
  cm3c := inferInstanceAs (isomorphisms (Type)).IsStableUnderRetracts
  cm4a i _ _ _ _ := by
    have := isIso_of_cofibration i
    infer_instance
  cm4b i _ _ _ _ := by
    have := isIso_of_cofibration i
    infer_instance
  cm5a := ⟨fun f => ⟨{
    Z := _
    i := 𝟙 _
    p := f
    hi := ⟨isomorphisms.infer_property _, trivial⟩
    hp := trivial }⟩⟩
  cm5b := ⟨fun f => ⟨{
    Z := _
    i := 𝟙 _
    p := f
    hi := isomorphisms.infer_property _
    hp := ⟨trivial, trivial⟩ }⟩⟩

attribute [local instance] contractibleModel

/-- The weak equivalence `Empty → Unit`. -/
def emptyToUnit : (Empty : Type) ⟶ Unit := TypeCat.ofHom (fun x => nomatch x)

lemma emptyToUnit_weakEquivalence : weakEquivalences (Type) emptyToUnit := trivial

/-- `Empty → Unit` is not an isomorphism. -/
lemma emptyToUnit_not_isIso : ¬ IsIso emptyToUnit := by
  intro h
  exact (inv emptyToUnit ()).elim

/-- `Empty` and `Unit` are not isomorphic in `Type`. -/
lemma empty_not_iso_unit : IsEmpty ((Empty : Type) ≅ Unit) :=
  ⟨fun e => (e.inv ()).elim⟩

/-- The localization inverts the non-isomorphism `Empty → Unit`. -/
lemma isIso_Q_emptyToUnit : IsIso ((weakEquivalences (Type)).Q.map emptyToUnit) :=
  Localization.inverts _ (weakEquivalences (Type)) _ emptyToUnit_weakEquivalence

/-- After localization, `Empty` and `Unit` are isomorphic. -/
noncomputable def localizedEmptyIsoUnit :
    (weakEquivalences (Type)).Q.obj Empty ≅ (weakEquivalences (Type)).Q.obj Unit :=
  have := isIso_Q_emptyToUnit
  asIso ((weakEquivalences (Type)).Q.map emptyToUnit)

/-- The adjunction of the equivalence `Typeᵒᵖᵒᵖ ≌ Type`. -/
abbrev opOpAdj : unopUnop (Type) ⊣ opOp (Type) := (opOpEquivalence (Type)).toAdjunction

/-- It is a Quillen adjunction. -/
lemma opOpAdj_isQuillen : CategoryTheory.Adjunction.IsQuillenAdjunction opOpAdj where
  preservesCofibrations := fun _ _ _ hf => hf
  preservesTrivialCofibrations := fun _ _ _ hf => hf

attribute [local instance] opOpAdj_isQuillen

instance : IsIso opOpAdj.unit := inferInstanceAs (IsIso (opOpEquivalence (Type)).unitIso.hom)

instance : IsIso opOpAdj.counit :=
  inferInstanceAs (IsIso (opOpEquivalence (Type)).counitIso.hom)

lemma opOp_hL :
    weakEquivalences (Type)ᵒᵖᵒᵖ ≤ (weakEquivalences (Type)).inverseImage (unopUnop (Type)) :=
  fun _ _ _ _ => trivial

lemma opOp_hR :
    weakEquivalences (Type) ≤ (weakEquivalences (Type)ᵒᵖᵒᵖ).inverseImage (opOp (Type)) :=
  fun _ _ _ _ => trivial

/-- The localized non-isomorphism in `Typeᵒᵖᵒᵖ`. -/
noncomputable abbrev localizedSourceMap :=
  (weakEquivalences (Type)ᵒᵖᵒᵖ).Q.map emptyToUnit.op.op

/-- The derived comparison at `Empty` is an isomorphism onto the localized `Empty`. -/
lemma isIso_leftComparison_empty :
    IsIso ((quillenDerivedAdjunctionData opOpAdj).leftComparison.app (op (op Empty))) := by
  have := quillenDerived_leftComparison_isIso opOpAdj opOp_hL
  infer_instance

/-- The comparison square at `Empty → Unit`: the derived image of the localized source map,
followed by the comparison, is the comparison followed by the localized target map. -/
lemma leftComparison_square :
    (quillenDerivedAdjunctionData opOpAdj).leftDerived.map localizedSourceMap ≫
        (quillenDerivedAdjunctionData opOpAdj).leftComparison.app (op (op Unit)) =
      (quillenDerivedAdjunctionData opOpAdj).leftComparison.app (op (op Empty)) ≫
        (weakEquivalences (Type)).Q.map emptyToUnit :=
  (quillenDerivedAdjunctionData opOpAdj).leftComparison.naturality emptyToUnit.op.op

/-- The forward functor of the derived equivalence sends the localized non-isomorphism to an
isomorphism, and agrees with the canonical total left derived functor. -/
example :
    IsIso ((homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).functor.map
      localizedSourceMap) ∧
    (homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).functor =
      (quillenDerivedAdjunctionData opOpAdj).leftDerived := by
  have : IsIso localizedSourceMap :=
    Localization.inverts _ (weakEquivalences (Type)ᵒᵖᵒᵖ) _ trivial
  exact ⟨Functor.map_isIso _ localizedSourceMap, homotopicalQuillenDerivedEquivalence_functor _ _ _⟩

/-- The remaining four provider statements at this concrete Quillen adjunction. -/
example :
    (homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).inverse =
        (quillenDerivedAdjunctionData opOpAdj).rightDerived ∧
      (homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).unitIso.hom =
        (quillenDerivedAdjunctionData opOpAdj).adjunction.unit ∧
      (homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).counitIso.hom =
        (quillenDerivedAdjunctionData opOpAdj).adjunction.counit ∧
      ∀ X Y f, (homotopicalQuillenDerivedEquivalence opOpAdj opOp_hL opOp_hR).toAdjunction.homEquiv
          X Y f = (quillenDerivedAdjunctionData opOpAdj).adjunction.homEquiv X Y f :=
  ⟨homotopicalQuillenDerivedEquivalence_inverse _ _ _,
    homotopicalQuillenDerivedEquivalence_unit_hom _ _ _,
    homotopicalQuillenDerivedEquivalence_counit_hom _ _ _,
    homotopicalQuillenDerivedEquivalence_homEquiv _ _ _⟩

end MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenLocalizationRegression
