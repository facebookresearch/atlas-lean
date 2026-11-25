/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition
public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer
public import MathlibExt.CategoryTheory.SmallObject.Image
public import Mathlib.Data.PNat.Basic

/-!
# The original degree-zero maps of positive free Day-module cells

The carrier is the existing internal module category of an arbitrary Day monoid.
The generator family retains the original free-at-cardinal maps. Its degree-zero
component is an isomorphism by the actual below-degree free-module comparison.
The small-object left maps and the retract characterization retain those maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.PositiveLevelModel

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) [MonObj R]

/-- The same original module evaluation at the empty finite alphabet. -/
abbrev zeroEvaluation : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C)
    R ⥤ C :=
  CategoryTheory.Mod.dayEvaluation R (card 0)

/-- The exact degree-zero isomorphism class on the original module maps. -/
def zeroIsomorphisms :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  (isomorphisms C).inverseImage (zeroEvaluation R)

/-- Every original free module map generated in strictly positive degree. -/
def positiveGenerators (K : MorphismProperty C) :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  adjointFamilyGenerators (fun n : ℕ+ => CategoryTheory.Mod.dayFreeAt R (card n)) K

/-- Every original ordinary free module map, including degree zero. -/
def ordinaryGenerators (K : MorphismProperty C) :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  adjointFamilyGenerators (fun n : ℕ => CategoryTheory.Mod.dayFreeAt R (card n)) K

/-- Positive degree tests retain the original evaluated component maps. -/
def positiveProperty (K : MorphismProperty C) :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  EvaluationTransfer.evaluationProperty (fun n : ℕ+ => CategoryTheory.Mod.dayEvaluation R (card n))
      K

/-- Ordinary tests retain every original finite cardinal, including the empty alphabet. -/
def ordinaryProperty (K : MorphismProperty C) :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  EvaluationTransfer.evaluationProperty (fun n : ℕ => CategoryTheory.Mod.dayEvaluation R (card n)) K

/-- Positive evaluation is exactly the unrestricted quantification at degrees n>0. -/
theorem positiveProperty_iff (K : MorphismProperty C)
    {X Y : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R}
        (f : X ⟶ Y) :
    positiveProperty R K f ↔ ∀ n : ℕ, 0 < n → K
        ((CategoryTheory.Mod.dayEvaluation R (card n)).map f) := by
  rw [positiveProperty, EvaluationTransfer.evaluationProperty_iff]
  exact ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n n.2⟩

/-- The actual positive free/evaluation adjunction computes the full positive right class. -/
theorem positiveGenerators_rlp (K : MorphismProperty C) :
    (positiveGenerators R K).rlp = positiveProperty R K.rlp :=
  EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun n : ℕ+ => CategoryTheory.Mod.dayFreeAt R (card n))
    (fun n : ℕ+ => CategoryTheory.Mod.dayEvaluation R (card n))
    (fun n => CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (card n)) K

/-- The ordinary original free/evaluation adjunction computes its full right class. -/
theorem ordinaryGenerators_rlp (K : MorphismProperty C) :
    (ordinaryGenerators R K).rlp = ordinaryProperty R K.rlp :=
  EvaluationTransfer.evaluatedGenerators_rlp_eq
    (fun n : ℕ => CategoryTheory.Mod.dayFreeAt R (card n))
    (fun n : ℕ => CategoryTheory.Mod.dayEvaluation R (card n))
    (fun n => CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (card n)) K

/-- Positive generators are the same original ordinary generators with only the index restricted. -/
theorem positiveGenerators_le_ordinary (K : MorphismProperty C) :
    positiveGenerators R K ≤ ordinaryGenerators R K := by
  intro X Y f hf
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  exact (adjointFamilyGenerators_iff _ _ f).mpr ⟨⟨q.1, q.2⟩, hq⟩

/-- The actual positive free generator has an isomorphism as its original degree-zero map. -/
theorem positiveFreeAt_zero_isIso (n : ℕ+) {X Y : C} (f : X ⟶ Y) :
    IsIso ((zeroEvaluation R).map ((CategoryTheory.Mod.dayFreeAt R (card n)).map f)) := by
  let e := CategoryTheory.Mod.dayFreeAtCardBelowIso R n.2
  let χ : Arrow.mk ((zeroEvaluation R).map ((CategoryTheory.Mod.dayFreeAt R (card n)).map f)) ≅
      Arrow.mk (𝟙 (⊥_ C)) :=
    Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
  exact ((isomorphisms C).arrow_iso_iff χ).mpr (inferInstance : IsIso (𝟙 (⊥_ C)))

/-- Every actual positive generator lies in the exact degree-zero isomorphism class. -/
theorem positiveGenerators_le_zeroIsomorphisms (K : MorphismProperty C) :
    positiveGenerators R K ≤ zeroIsomorphisms R := by
  intro X Y f hf
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  change IsIso ((zeroEvaluation R).map f)
  have h := positiveFreeAt_zero_isIso R q.1 q.2.1.hom
  have e : Arrow.mk f ≅ Arrow.mk ((CategoryTheory.Mod.dayFreeAt R (card q.1)).map q.2.1.hom) :=
    eqToIso hq
  exact ((isomorphisms C).arrow_iso_iff ((zeroEvaluation R).mapArrow.mapIso e)).mpr h

/-- The actual positive right factor becomes an ordinary right factor when its zero component is an
isomorphism. -/
theorem positiveRight_zeroIsomorphisms_le_ordinaryRight (K : MorphismProperty C) :
    (positiveGenerators R K).rlp ⊓ zeroIsomorphisms R ≤ (ordinaryGenerators R K).rlp := by
  intro X Y f hf
  rw [positiveGenerators_rlp] at hf
  rw [ordinaryGenerators_rlp, ordinaryProperty, EvaluationTransfer.evaluationProperty_iff]
  intro n
  by_cases hn : 0 < n
  · exact (positiveProperty_iff R K.rlp f).mp hf.1 n hn
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    let _ : IsIso ((zeroEvaluation R).map f) := hf.2
    exact K.rlp_of_isIso _

section ActualPositiveSmallObject

variable (K : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [(positiveGenerators R K).IsCardinalForSmallObjectArgument κ]
  [PreservesColimitsOfSize.{w, w} (zeroEvaluation R)]
  [PreservesColimitsOfShape κ.ord.ToType (zeroEvaluation R)]
  [PreservesWellOrderContinuousOfShape κ.ord.ToType (zeroEvaluation R)]

include κ in
/-- The full positive left class inherits degree-zero isomorphisms from its actual cell/retract
history. -/
theorem positiveGeneratedLeft_le_zeroIsomorphisms :
    (positiveGenerators R K).rlp.llp ≤ zeroIsomorphisms R := by
  let _ : (isomorphisms C).IsStableUnderCoproducts.{w} := {}
  exact rlp_llp_le_inverseImage_of_cardinal_closure (positiveGenerators R K) (isomorphisms C)
    (zeroEvaluation R) κ (positiveGenerators_le_zeroIsomorphisms R K)

/-- The actual positive small-object left map is an isomorphism in degree zero. -/
theorem positiveSmallObject_left_zero_isIso
    {X Y : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R}
        (f : X ⟶ Y) :
    IsIso ((zeroEvaluation R).map (SmallObject.ιObj (positiveGenerators R K) κ f)) :=
  positiveGeneratedLeft_le_zeroIsomorphisms R K κ _
      (SmallObject.llp_rlp_ιObj (positiveGenerators R K) κ f)

omit [PreservesColimitsOfSize.{w, w} (zeroEvaluation R)]
  [PreservesColimitsOfShape κ.ord.ToType (zeroEvaluation R)]
  [PreservesWellOrderContinuousOfShape κ.ord.ToType (zeroEvaluation R)] in
/-- The original positive factor maps recover the caller's exact degree-zero map. -/
theorem positiveSmallObject_degreeZero_fac
    {X Y : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R}
        (f : X ⟶ Y) :
    (zeroEvaluation R).map (SmallObject.ιObj (positiveGenerators R K) κ f) ≫
      (zeroEvaluation R).map (SmallObject.πObj (positiveGenerators R K) κ f) =
        (zeroEvaluation R).map f := by
  rw [← Functor.map_comp, SmallObject.ιObj_πObj]

include κ in
/-- The full positive cofibrations are exactly the original ordinary cofibrations with isomorphic
degree zero. -/
theorem positiveGeneratedLeft_eq_ordinary_inf_zero :
    (positiveGenerators R K).rlp.llp = (ordinaryGenerators R K).rlp.llp ⊓ zeroIsomorphisms R := by
  apply le_antisymm
  · exact le_inf (antitone_llp (antitone_rlp (positiveGenerators_le_ordinary R K)))
      (positiveGeneratedLeft_le_zeroIsomorphisms R K κ)
  · intro X Y f hf
    let i := SmallObject.ιObj (positiveGenerators R K) κ f
    let q := SmallObject.πObj (positiveGenerators R K) κ f
    let _ : IsIso ((zeroEvaluation R).map i) := positiveSmallObject_left_zero_isIso R K κ f
    let _ : IsIso ((zeroEvaluation R).map f) := hf.2
    let _ : IsIso ((zeroEvaluation R).map q) :=
      IsIso.of_isIso_fac_left (positiveSmallObject_degreeZero_fac R K κ f)
    have hq : (ordinaryGenerators R K).rlp q :=
      positiveRight_zeroIsomorphisms_le_ordinaryRight R K q
        ⟨SmallObject.rlp_πObj (positiveGenerators R K) κ f,
          (show IsIso ((zeroEvaluation R).map q) from inferInstance)⟩
    let _ : HasLiftingProperty f q := hf.1 q hq
    exact (positiveGenerators R K).rlp.llp.of_retract
      (RetractArrow.ofLeftLiftingProperty (SmallObject.ιObj_πObj (positiveGenerators R K) κ f))
      (SmallObject.llp_rlp_ιObj (positiveGenerators R K) κ f)

end ActualPositiveSmallObject

end HomotopicalAlgebra.PositiveLevelModel
