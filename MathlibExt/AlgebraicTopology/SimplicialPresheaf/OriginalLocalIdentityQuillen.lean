/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalDerivedMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWhitehead
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# The actual base-to-localization identity Quillen adjunction

Both models are the internally constructed models on the original presheaf
category. Their comparison retains global lifting classes. The final detector
uses the chosen Smith fibrant replacement, and compares its actual map with
the original all-local-target weak class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra
open SimplicialPresheaf.OriginalLocalDerived
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

omit [Small.{u} I] in
private theorem baseWeak_le_localWeak (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SimplicialPresheaf.objectwiseKanWeakEquivalences D ≤ originalLocalEquivalences S := by
  intro X Y f hf
  have hbase : weakEquivalences (SimplicialPresheaf.{u} D) f := by
    change (data D).model.categoryWithWeakEquivalences.weakEquivalences f
    rw [(data D).weakEquivalences_eq]
    exact hf
  exact weakEquivalences_le_originalLocalEquivalences S f hbase

/-- The original injective model maps to its constructed localization by the
literal identity Quillen adjunction. No model is supplied as a premise. -/
theorem originalLocalization_identity_isQuillenAdjunction
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    @CategoryTheory.Adjunction.IsQuillenAdjunction
      (SimplicialPresheaf.{u} D) inferInstance
      (SimplicialPresheaf.{u} D) inferInstance
      (data D).model (originalLocalSmithModel S)
      (Functor.id (SimplicialPresheaf.{u} D))
      (Functor.id (SimplicialPresheaf.{u} D))
      (Adjunction.id (C := SimplicialPresheaf.{u} D)) := by
  let b := data D
  let l := originalLocalSmithData S
  change @CategoryTheory.Adjunction.IsQuillenAdjunction
    (SimplicialPresheaf.{u} D) inferInstance
    (SimplicialPresheaf.{u} D) inferInstance
    b.model l.model (Functor.id _) (Functor.id _)
    (Adjunction.id (C := SimplicialPresheaf.{u} D))
  refine @CategoryTheory.Adjunction.IsQuillenAdjunction.mk
    (SimplicialPresheaf.{u} D) inferInstance
    (SimplicialPresheaf.{u} D) inferInstance
    b.model l.model (Functor.id _) (Functor.id _)
    (Adjunction.id (C := SimplicialPresheaf.{u} D)) ?_ ?_
  · intro X Y f hf
    change b.model.categoryWithCofibrations.cofibrations f at hf
    change l.model.categoryWithCofibrations.cofibrations f
    rw [l.cofibrations_eq]
    rw [b.cofibrations_eq] at hf
    exact hf
  · intro X Y f hf
    change b.model.categoryWithCofibrations.cofibrations f ∧
      b.model.categoryWithWeakEquivalences.weakEquivalences f at hf
    change l.model.categoryWithCofibrations.cofibrations f ∧
      l.model.categoryWithWeakEquivalences.weakEquivalences f
    rw [b.cofibrations_eq,b.weakEquivalences_eq] at hf
    rw [l.cofibrations_eq,l.weakEquivalences_eq]
    exact ⟨hf.1,baseWeak_le_localWeak S f hf.2⟩

/-- Localized fibrations have the GLOBAL injective base right lifting property
on the same original arrow, rather than only objectwise fibrancy. -/
theorem originalLocalFibrations_le_injectiveFibrations
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (originalLocalSmithModel S).categoryWithFibrations.fibrations ≤
      injectiveFibrations D := by
  change (originalLocalSmithData S).model.categoryWithFibrations.fibrations ≤ _
  rw [(originalLocalSmithData S).fibrations_eq]
  intro X Y p hp
  change (trivialMonomorphisms D).rlp p
  intro A B f hf
  exact hp f ⟨hf.1,baseWeak_le_localWeak S f hf.2⟩

/-- The full global trivial-fibration class is unchanged by localization. -/
theorem originalLocalTrivialFibrations_eq_injectiveTrivialFibrations
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    ((originalLocalSmithModel S).categoryWithFibrations.fibrations ⊓
      (originalLocalSmithModel S).categoryWithWeakEquivalences.weakEquivalences) =
    ((data D).model.categoryWithFibrations.fibrations ⊓
      (data D).model.categoryWithWeakEquivalences.weakEquivalences) := by
  calc
    _ = (monomorphisms (SimplicialPresheaf.{u} D)).rlp :=
      (originalLocalSmithData S).trivialFibrations_eq
    _ = _ := (data D).trivialFibrations_eq.symm

/-- The actual Smith replacement reflects as well as preserves the original
local weak class. Both original unit components enter the naturality square. -/
theorem originalLocalEquivalence_iff_localR_map
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    originalLocalEquivalences S f ↔
      originalLocalEquivalences S ((localR S).map f) := by
  let W := originalLocalEquivalences S
  let _ : W.HasTwoOutOfThreeProperty := originalLocalEquivalences_hasTwoOutOfThreeProperty S
  constructor
  · exact localR_map_localWeak S f
  · intro hf
    have hX : W ((localRUnit S).app X) := (localRUnit_localTrivialCofibration S X).2
    have hY : W ((localRUnit S).app Y) := (localRUnit_localTrivialCofibration S Y).2
    have hcomp : W ((localRUnit S).app X ≫ (localR S).map f) :=
      W.comp_mem _ _ hX hf
    have hn : f ≫ (localRUnit S).app Y = (localRUnit S).app X ≫ (localR S).map f :=
      (localRUnit S).naturality f
    rw [← hn] at hcomp
    exact (W.postcomp_iff f ((localRUnit S).app Y) hY).mp hcomp

/-- On every original arrow, local weakness is exactly objectwise Kan–Quillen
weakness of its internally chosen Smith fibrant-replacement map. -/
theorem originalLocalEquivalence_iff_objectwiseKanWeak_localR
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    originalLocalEquivalences S f ↔
      SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ ((localR S).map f) := by
  refine (originalLocalEquivalence_iff_localR_map S f).trans ?_
  exact originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S ((localR S).map f)
    (localR_isOriginalLocalFibrant S X) (localR_isOriginalLocalFibrant S Y)

end SimplicialPresheaf.InjectiveKan
