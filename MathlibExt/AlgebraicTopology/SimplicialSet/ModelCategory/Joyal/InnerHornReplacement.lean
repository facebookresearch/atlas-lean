/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
import Mathlib.CategoryTheory.Groupoid
import MathlibExt.CategoryTheory.NatTrans.TerminalArrow
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Strict inner-horn replacement of original groupoidal simplicial sets

This file constructs one native functorial factorization at
the literal inner-horn family and the literal cardinal `Cardinal.aleph0.{u}`.
Every replacement map is the component of that same factorization at the
canonical terminal arrow. No quasicategory assumption on the original input is
used in the categorical or realization weakness of the unit, in its induced
equivalence of homotopy categories, or in the conditional groupoidal Kan result.

The later comparison of categorical and realization equivalences between
arbitrary original groupoidal inputs is a separate theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- One actual native factorization at the inner horns and `aleph0`. -/
def innerHornFactorization :
    FunctorialFactorizationData innerHornInclusions.{u}.rlp.llp
      innerHornInclusions.{u}.rlp :=
  SmallObject.functorialFactorizationData innerHornInclusions.{u} Cardinal.aleph0.{u}

/-- The intermediate objects in the factorization of the original terminal arrows. -/
def innerHornReplacement : SSet.{u} ⥤ SSet.{u} :=
  terminal.arrowFunctor SSet.{u} ⋙ innerHornFactorization.{u}.Z

/-- The actual native left-factor components form the replacement unit. -/
def innerHornReplacementUnit : 𝟭 SSet.{u} ⟶ innerHornReplacement.{u} where
  app X := innerHornFactorization.{u}.i.app
    ((terminal.arrowFunctor SSet.{u}).obj X)
  naturality X Y f := by
    simpa [innerHornReplacement] using innerHornFactorization.{u}.i.naturality
      ((terminal.arrowFunctor SSet.{u}).map f)

/-- The actual native right-factor components form the terminal projection. -/
def innerHornReplacementProjection :
    innerHornReplacement.{u} ⟶ (Functor.const SSet.{u}).obj (⊤_ SSet.{u}) where
  app X := innerHornFactorization.{u}.p.app
    ((terminal.arrowFunctor SSet.{u}).obj X)
  naturality X Y f := by
    simpa [innerHornReplacement] using innerHornFactorization.{u}.p.naturality
      ((terminal.arrowFunctor SSet.{u}).map f)

/-- The strict unit square for every original arrow. -/
@[reassoc]
theorem innerHornReplacementUnit_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    innerHornReplacementUnit.app X ≫ innerHornReplacement.map f =
      f ≫ innerHornReplacementUnit.app Y :=
  (innerHornReplacementUnit.naturality f).symm

/-- The strict projection square for every original arrow, with both components retained. -/
@[reassoc]
theorem innerHornReplacementProjection_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    innerHornReplacement.map f ≫ innerHornReplacementProjection.app Y =
      innerHornReplacementProjection.app X ≫ 𝟙 (⊤_ SSet.{u}) := by
  simpa only [Functor.const_obj_map] using innerHornReplacementProjection.naturality f

/-- The factorization is the literal original map to the chosen terminal object. -/
@[reassoc]
theorem innerHornReplacement_fac (X : SSet.{u}) :
    innerHornReplacementUnit.app X ≫ innerHornReplacementProjection.app X =
      terminal.from X :=
  innerHornFactorization.{u}.fac_app

/-- The native projection is exactly the chosen terminal map of the replacement. -/
theorem innerHornReplacementProjection_eq_terminal (X : SSet.{u}) :
    innerHornReplacementProjection.app X = terminal.from (innerHornReplacement.obj X) :=
  terminalIsTerminal.hom_ext _ _

/-- Every unit is inner anodyne, using the entire native left class. -/
theorem innerHornReplacementUnit_innerAnodyne (X : SSet.{u}) :
    innerAnodyneExtensions (innerHornReplacementUnit.app X) := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact innerHornFactorization.{u}.hi ((terminal.arrowFunctor SSet.{u}).obj X)

/-- Every projection has the right lifting property against all inner horns. -/
theorem innerHornReplacementProjection_rlp (X : SSet.{u}) :
    innerHornInclusions.rlp (innerHornReplacementProjection.app X) :=
  innerHornFactorization.{u}.hp ((terminal.arrowFunctor SSet.{u}).obj X)

/-- The actual replacement is a quasicategory for every original input. -/
theorem innerHornReplacement_quasicategory (X : SSet.{u}) :
    Quasicategory (innerHornReplacement.obj X) := by
  have hp : innerFibrations (innerHornReplacementProjection.app X) :=
    innerHornReplacementProjection_rlp X
  rw [innerHornReplacementProjection_eq_terminal X] at hp
  exact (quasicategory_iff_innerFibration _).2
    ((innerFibration_iff _).2 hp)

/-- Every unit is a trivial cofibration for the selected Kan--Quillen model. -/
theorem innerHornReplacementUnit_trivialCofibration (X : SSet.{u}) :
    trivialCofibrations SSet.{u} (innerHornReplacementUnit.app X) := by
  rw [← anodyneExtensions_eq_trivialCofibrations]
  exact innerAnodyneExtensions_le _ (innerHornReplacementUnit_innerAnodyne X)

/-- The original unit is a genuine realization weak equivalence, with no endpoint premise. -/
theorem innerHornReplacementUnit_realizationWeak (X : SSet.{u}) :
    realizationWeakEquivalences (innerHornReplacementUnit.app X) := by
  have hw : WeakEquivalence (innerHornReplacementUnit.app X) :=
    ((mem_trivialCofibrations_iff _).1
      (innerHornReplacementUnit_trivialCofibration X)).2
  exact (weakEquivalence_iff _).1 hw

/-- The original unit is a categorical equivalence, using saturated inner anodynes. -/
theorem innerHornReplacementUnit_categorical (X : SSet.{u}) :
    categoricalEquivalences (innerHornReplacementUnit.app X) :=
  innerAnodyneExtensions_le_categoricalEquivalences _
    (innerHornReplacementUnit_innerAnodyne X)

/-- The unit induces an equivalence of ordinary homotopy categories without original QC. -/
theorem innerHornReplacementUnit_mapHo_isEquivalence (X : SSet.{u}) :
    (mapHomotopyCategory (innerHornReplacementUnit.app X)).IsEquivalence :=
  (innerHornReplacementUnit_categorical X).isEquivalence_mapHomotopyCategory

/-- Original groupoidality transfers through the inverse of the actual unit Ho equivalence. -/
theorem innerHornReplacement_isGroupoid_of_isGroupoid (X : SSet.{u})
    [IsGroupoid X.HomotopyCategory] :
    IsGroupoid (innerHornReplacement.obj X).HomotopyCategory := by
  let _ : (mapHomotopyCategory (innerHornReplacementUnit.app X)).IsEquivalence :=
    innerHornReplacementUnit_mapHo_isEquivalence X
  let _ : IsGroupoid ((𝟭 SSet.{u}).obj X).HomotopyCategory := by
    simpa only [Functor.id_obj] using
      (inferInstance : IsGroupoid X.HomotopyCategory)
  let e := (mapHomotopyCategory (innerHornReplacementUnit.app X)).asEquivalence
  exact isGroupoid_of_reflects_iso e.inverse

/-- Every original edge of the replacement is an equivalence when original Ho is groupoidal. -/
theorem innerHornReplacement_core_eq_top_of_isGroupoid (X : SSet.{u})
    [IsGroupoid X.HomotopyCategory] :
    core (innerHornReplacement.obj X) = ⊤ := by
  let _ : IsGroupoid (innerHornReplacement.obj X).HomotopyCategory :=
    innerHornReplacement_isGroupoid_of_isGroupoid X
  refine le_antisymm le_top ?_
  apply (le_core_iff (⊤ : (innerHornReplacement.obj X).Subcomplex)).2
  intro s _hs
  exact (Edge.isEquivalence_iff (Edge.mk' s)).2 (by infer_instance)

/-- The same replacement is Kan, via its genuine QC core and the inverse core/top isomorphism. -/
theorem innerHornReplacement_kanComplex_of_isGroupoid (X : SSet.{u})
    [IsGroupoid X.HomotopyCategory] :
    KanComplex (innerHornReplacement.obj X) := by
  let _ : Quasicategory (innerHornReplacement.obj X) :=
    innerHornReplacement_quasicategory X
  let _ : KanComplex (core (innerHornReplacement.obj X) : SSet.{u}) :=
    kanComplex_core_of_quasicategory (innerHornReplacement.obj X)
  let e : (core (innerHornReplacement.obj X) : SSet.{u}) ≅
      innerHornReplacement.obj X :=
    Subcomplex.eqToIso (innerHornReplacement_core_eq_top_of_isGroupoid X) ≪≫
      Subcomplex.topIso (innerHornReplacement.obj X)
  exact isFibrant_of_fibration e.inv

/-- Every original map into a quasicategory extends with both native strict lift equations. -/
theorem exists_innerHornReplacement_extension {X Y : SSet.{u}} (f : X ⟶ Y)
    [Quasicategory Y] :
    ∃ g : innerHornReplacement.obj X ⟶ Y,
      innerHornReplacementUnit.app X ≫ g = f ∧
      g ≫ terminal.from Y = innerHornReplacementProjection.app X := by
  let _ : HasLiftingProperty (innerHornReplacementUnit.app X) (terminal.from Y) :=
    innerHornReplacementUnit_innerAnodyne X _ (mem_innerFibrations _)
  let sq : CommSq f (innerHornReplacementUnit.app X)
      (terminal.from Y) (innerHornReplacementProjection.app X) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SSet
