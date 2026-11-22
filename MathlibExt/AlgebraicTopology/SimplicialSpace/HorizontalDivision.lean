/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
# Horizontal Reedy division and pullback-Hom calculus

This is Joyal--Tierney Proposition 7.33 for the literal horizontal box
action.  For an arbitrary left morphism class `A`, it identifies relative
matching maps in `A.rlp`, right row pullback-Homs in `A.rlp` along all
monomorphisms, and source left box pullback-Homs in the genuine simplicial
trivial-fibration class along maps in `A`.

The final theorems specialize this statement to the Joyal, Kan, and inner
anodyne weak factorization systems.  The Joyal specialization is also stated
as a characterization of fibrations in the named horizontal Reedy model.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace SimplicialSpace

/-- A map has relative matching maps in `P` in every horizontal degree. -/
def hasHorizontalRelativeMatchingMaps
    (P : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, P (HorizontalModel.horizontalRelativeMatchingMap f n)

/-- Every right row pullback-Hom along a monomorphism belongs to `P`. -/
def hasRowPullbackHoms
    (P : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ {K L : SSet.{u}} (u : K ⟶ L), monomorphisms SSet.{u} u →
    P (rowPullbackHom u f)

/-- Every source-left box pullback-Hom along a map in `A` belongs to `P`. -/
def hasBoxLeftPullbackHoms
    (A P : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) : Prop :=
  ∀ {K L : SSet.{u}} (v : K ⟶ L), A v → P (boxLeftPullbackHom v f)

private theorem horizontalRelativeMatching_to_boxLeftTrivial
    (A : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y)
    (h : hasHorizontalRelativeMatchingMaps A.rlp f) :
    hasBoxLeftPullbackHoms A SSet.modelCategoryQuillen.I.rlp f := by
  intro K L v hv P Q i hi
  change MorphismProperty.ofHoms
      (fun n : ℕ => (SSet.boundary.{u} n).ι) i at hi
  cases hi with
  | mk n =>
      have hrow : A.rlp (rowPullbackHom (SSet.boundary.{u} n).ι f) :=
        (A.rlp.arrow_iso_iff
          (rowRelativeMatchingArrowIso n (Arrow.mk f))).mpr (h n)
      exact (box_hasLiftingProperty_iff v (SSet.boundary.{u} n).ι f).mp
        (hrow v hv)

private theorem boxLeftTrivial_to_rowPullback
    (A : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y)
    (h : hasBoxLeftPullbackHoms A SSet.modelCategoryQuillen.I.rlp f) :
    hasRowPullbackHoms A.rlp f := by
  intro K L u hu P Q v hv
  apply (box_hasLiftingProperty_iff v u f).mpr
  have hmono : (monomorphisms SSet.{u}).rlp (boxLeftPullbackHom v f) := by
    rw [SSet.rlp_monomorphisms]
    exact h v hv
  exact hmono u hu

private theorem rowPullback_to_horizontalRelativeMatching
    (A : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (h : hasRowPullbackHoms A.rlp f) :
    hasHorizontalRelativeMatchingMaps A.rlp f := by
  intro n
  exact (A.rlp.arrow_iso_iff
    (rowRelativeMatchingArrowIso n (Arrow.mk f))).mp
      (h (SSet.boundary.{u} n).ι inferInstance)

/-- Joyal--Tierney Proposition 7.33 for the literal horizontal box action.
The three conditions retain the original relative matching maps, both
pullback-Hom arrows, and their canonical pullback objects. -/
theorem horizontalDivisionSM7
    (A : MorphismProperty SSet.{u}) {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    (hasHorizontalRelativeMatchingMaps A.rlp f ↔
      hasRowPullbackHoms A.rlp f) ∧
    (hasRowPullbackHoms A.rlp f ↔
      hasBoxLeftPullbackHoms A SSet.modelCategoryQuillen.I.rlp f) := by
  have h13 : hasHorizontalRelativeMatchingMaps A.rlp f →
      hasBoxLeftPullbackHoms A SSet.modelCategoryQuillen.I.rlp f :=
    horizontalRelativeMatching_to_boxLeftTrivial A f
  have h32 : hasBoxLeftPullbackHoms A SSet.modelCategoryQuillen.I.rlp f →
      hasRowPullbackHoms A.rlp f :=
    boxLeftTrivial_to_rowPullback A f
  have h21 : hasRowPullbackHoms A.rlp f →
      hasHorizontalRelativeMatchingMaps A.rlp f :=
    rowPullback_to_horizontalRelativeMatching A f
  exact ⟨⟨fun h => h32 (h13 h), h21⟩,
    ⟨fun h => h13 (h21 h), h32⟩⟩

end SimplicialSpace

namespace SimplicialSpace

/-- Proposition 7.33 for the genuine Joyal weak factorization system. -/
theorem horizontalJoyalDivisionSM7 {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    (hasHorizontalRelativeMatchingMaps SSet.categoricalFibrations f ↔
      hasCategoricalRowPullbackHom f) ∧
    (hasCategoricalRowPullbackHom f ↔
      hasBoxLeftPullbackHoms
        (monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences)
        SSet.modelCategoryQuillen.I.rlp f) := by
  simpa only [SSet.categoricalFibrations, hasCategoricalRowPullbackHom,
    hasRowPullbackHoms] using
      horizontalDivisionSM7
        (monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences) f

/-- Proposition 7.33 for the Kan weak factorization system. -/
theorem horizontalKanDivisionSM7 {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    (hasHorizontalRelativeMatchingMaps
        SSet.modelCategoryQuillen.J.rlp f ↔
      hasRowPullbackHoms SSet.modelCategoryQuillen.J.rlp f) ∧
    (hasRowPullbackHoms SSet.modelCategoryQuillen.J.rlp f ↔
      hasBoxLeftPullbackHoms SSet.anodyneExtensions
        SSet.modelCategoryQuillen.I.rlp f) := by
  simpa only [SSet.anodyneExtensions_eq_llp_rlp, rlp_llp_rlp] using
    horizontalDivisionSM7 SSet.anodyneExtensions f

/-- Proposition 7.33 for the inner-anodyne weak factorization system. -/
theorem horizontalInnerAnodyneDivisionSM7 {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    (hasHorizontalRelativeMatchingMaps SSet.innerFibrations f ↔
      hasRowPullbackHoms SSet.innerFibrations f) ∧
    (hasRowPullbackHoms SSet.innerFibrations f ↔
      hasBoxLeftPullbackHoms SSet.innerAnodyneExtensions
        SSet.modelCategoryQuillen.I.rlp f) := by
  simpa only [SSet.innerAnodyneExtensions,
    SSet.innerFibrations, rlp_llp_rlp] using
      horizontalDivisionSM7 SSet.innerAnodyneExtensions f

namespace HorizontalModel

/-- Horizontal Joyal--Reedy fibrations are exactly the maps whose right row
pullback-Hom along every monomorphism is a categorical fibration. -/
theorem fibration_iff_hasCategoricalRowPullbackHoms
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
      modelCategory
    HomotopicalAlgebra.Fibration f ↔ hasCategoricalRowPullbackHom f := by
  let _ : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
    modelCategory
  exact (fibration_iff f).trans (horizontalJoyalDivisionSM7 f).1

/-- Horizontal Joyal--Reedy fibrations are exactly the maps whose source-left
box pullback-Hom along every monic categorical equivalence is a genuine
trivial fibration. -/
theorem fibration_iff_hasTrivialBoxLeftPullbackHoms
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
      modelCategory
    HomotopicalAlgebra.Fibration f ↔
      hasBoxLeftPullbackHoms
        (monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences)
        SSet.modelCategoryQuillen.I.rlp f := by
  exact (fibration_iff_hasCategoricalRowPullbackHoms f).trans
    (horizontalJoyalDivisionSM7 f).2

end HorizontalModel

end SimplicialSpace
