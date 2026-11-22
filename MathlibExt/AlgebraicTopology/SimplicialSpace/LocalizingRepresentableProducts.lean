/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCartesianModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.SpineInnerAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FilteredColimitsGeneral
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Representable products of complete-Segal localizing maps

Every Segal-spine localizing map and the full walking-isomorphism source-vertex map is a Rezk
weak equivalence after Cartesian product on either side by an outer simplex representable. Both
product orientations retain the given localizing map and representable factor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra MonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace

/-- The actual original underlying arrow; no source label is resized or replaced. -/
private def scalarGeneratorArrow (q : SSet.Rezk.LocalizingIndex) : Arrow SSet.{u} := by
  cases q with
  | inl n => exact Arrow.mk (SSet.Rezk.spineSubcomplex.{u} n.1).ι
  | inr _ => exact Arrow.mk (SSet.coherentIso.endpointInclusion.{u})

/-- Both original branches are categorical weak, including the full source-vertex map. -/
private theorem scalarGeneratorArrow_categorical (q : SSet.Rezk.LocalizingIndex) :
    SSet.categoricalEquivalences (scalarGeneratorArrow.{u} q).hom := by
  cases q with
  | inl n => exact (SSet.Rezk.monomorphisms_inf_categoricalEquivalences_spineSubcomplex_ι n.1 n.2).2
  | inr _ => exact SSet.coherentIso_endpointInclusion_mem.2

/-- Ordinary finite products are preserved by the same forget/constant/wrapping functors. -/
private instance comparisonLeft_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) comparisonLeft.{u} := by
  dsimp only [comparisonLeft, SSet.simplicialSpaceDiscrete]
  infer_instance

/-- The whole product Arrow comparison retains both original maps and both inverse legs. -/
private def comparisonLeftTensorArrowIso {A B : JoyalSSet.{u}}
    (K : JoyalSSet.{u}) (f : A ⟶ B) :
    Arrow.mk (comparisonLeft.map (K ◁ f)) ≅
      Arrow.mk (comparisonLeft.obj K ◁ comparisonLeft.map f) :=
  Arrow.isoMk' _ _
    (CartesianMonoidalCategory.prodComparisonIso comparisonLeft K A)
    (CartesianMonoidalCategory.prodComparisonIso comparisonLeft K B)
    ((CartesianMonoidalCategory.prodComparisonNatIso comparisonLeft K).hom.naturality f).symm

/-- The actual Joyal model supplies fixed-left tensor weakness by native Quillen/Brown. -/
private theorem tensorCategorical_left {A B : JoyalSSet.{u}}
    (K : JoyalSSet.{u}) (f : A ⟶ B)
    (hf : SSet.categoricalEquivalences (JoyalSSet.forget.map f)) :
    SSet.categoricalEquivalences (JoyalSSet.forget.map (K ◁ f)) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
    JoyalSSet.isClosedSymmetricMonoidalModelCategory
  let _ : IsCofibrant K := JoyalSSet.isCofibrant K
  let _ : IsCofibrant A := JoyalSSet.isCofibrant A
  let _ : IsCofibrant B := JoyalSSet.isCofibrant B
  let _ : Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  let _ : WeakEquivalence f := by
    constructor
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hf
  have hw : WeakEquivalence (K ◁ f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ihom.adjunction K) f
  have hp := (weakEquivalence_iff (K ◁ f)).mp hw
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences (K ◁ f) at hp
  rw [JoyalSSet.modelCategory_weakEquivalences] at hp
  exact hp

/-- The ordinary braid gives the whole opposite-orientation Arrow comparison. -/
private def tensorBraidArrowIso {A B : SimplicialSpace.{u}}
    (K : SimplicialSpace.{u}) (f : A ⟶ B) :
    Arrow.mk (K ◁ f) ≅ Arrow.mk (f ▷ K) :=
  Arrow.isoMk' _ _ (β_ K A) (β_ K B)
    (BraidedCategory.braiding_naturality_right K f).symm

/-- Every original scalar localizing generator is weak after product on the left by F(m). -/
theorem scalarLocalizingProduct_rezkWeak_left
    (q : SSet.Rezk.LocalizingIndex) (m : ℕ) :
    rezkWeakEquivalences (ofSimplicialObject.obj (SSet.Rezk.representable.{u} m) ◁
      ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} q).hom) := by
  let K := JoyalSSet.ofSSet.obj (SSet.stdSimplex.{u}.obj ⦋m⦌)
  let f := JoyalSSet.ofSSet.map (scalarGeneratorArrow.{u} q).hom
  have hf : SSet.categoricalEquivalences (JoyalSSet.forget.map f) :=
    scalarGeneratorArrow_categorical q
  have hw := comparisonLeft_rezkWeak_of_categoricalEquivalence
    (K ◁ f) (tensorCategorical_left K f hf)
  have h := (rezkWeakEquivalences.arrow_mk_iso_iff (comparisonLeftTensorArrowIso K f)).mp hw
  cases q with
  | inl n => exact h
  | inr _ => exact h

/-- Every original scalar localizing generator is weak after product on the right by F(m). -/
theorem scalarLocalizingProduct_rezkWeak
    (q : SSet.Rezk.LocalizingIndex) (m : ℕ) :
    rezkWeakEquivalences (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} q).hom ▷
      ofSimplicialObject.obj (SSet.Rezk.representable.{u} m)) := by
  exact (rezkWeakEquivalences.arrow_mk_iso_iff
    (tensorBraidArrowIso _ _)).mp (scalarLocalizingProduct_rezkWeak_left q m)

end SimplicialSpace
