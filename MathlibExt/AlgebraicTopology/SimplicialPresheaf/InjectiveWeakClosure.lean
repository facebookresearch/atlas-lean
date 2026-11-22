/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Pre-recognition closure of objectwise Kan weak equivalences

The weak class uses every original component of a simplicial-presheaf map.
Its trivial monomorphisms are exactly the objectwise scalar trivial
cofibrations. Existing transfinite witnesses are evaluated through the
cofree evaluation adjunction at any ordinal size. The free evaluation
adjunction sends global mono-RLP maps to scalar trivial fibrations.

Only the actual scalar Kan model is selected. No diagram model, generating
family or recognition/accessibility outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf

variable (D : Type w) [Category.{v} D]

/-- The original objectwise realization weak class on simplicial presheaves. -/
def objectwiseKanWeakEquivalences : MorphismProperty (SimplicialPresheaf.{u} D) :=
  SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ

/-- Membership tests the original component at every original site object. -/
theorem objectwiseKanWeakEquivalences_iff {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    objectwiseKanWeakEquivalences D f ↔
      ∀ d : D, SSet.realizationWeakEquivalences (f.app (op d)) :=
  ⟨fun hf d => hf (op d), fun hf d => hf d.unop⟩

instance objectwiseKanWeakEquivalences_hasTwoOutOfThree :
    (objectwiseKanWeakEquivalences.{u} D).HasTwoOutOfThreeProperty := by
  unfold objectwiseKanWeakEquivalences
  infer_instance

instance objectwiseKanWeakEquivalences_isStableUnderRetracts :
    (objectwiseKanWeakEquivalences.{u} D).IsStableUnderRetracts := by
  unfold objectwiseKanWeakEquivalences
  infer_instance

/-- The canonical original weak class is invariant under whole diagram isomorphisms. -/
instance objectwiseKanWeakEquivalences_respectsIso :
    (objectwiseKanWeakEquivalences.{u} D).RespectsIso := by
  unfold objectwiseKanWeakEquivalences
  infer_instance

/-- Global trivial monomorphisms are the actual objectwise scalar trivial cofibrations. -/
theorem monomorphisms_inf_objectwiseKanWeakEquivalences_eq :
    monomorphisms (SimplicialPresheaf.{u} D) ⊓ objectwiseKanWeakEquivalences D =
      (trivialCofibrations SSet.{u}).functorCategory Dᵒᵖ := by
  ext X Y f
  change (Mono f ∧ ∀ d, SSet.realizationWeakEquivalences (f.app d)) ↔
    ∀ d, Mono (f.app d) ∧ SSet.realizationWeakEquivalences (f.app d)
  constructor
  · rintro ⟨hf, hw⟩ d
    exact ⟨(NatTrans.mono_iff_mono_app f).mp hf d, hw d⟩
  · intro hf
    exact ⟨(NatTrans.mono_iff_mono_app f).mpr (fun d => (hf d).1), fun d => (hf d).2⟩

instance monomorphisms_inf_objectwiseKanWeakEquivalences_isStableUnderCobaseChange :
    (monomorphisms (SimplicialPresheaf.{u} D) ⊓
      objectwiseKanWeakEquivalences D).IsStableUnderCobaseChange := by
  rw [monomorphisms_inf_objectwiseKanWeakEquivalences_eq]
  infer_instance

section LocallySmallEvaluation

variable [LocallySmall.{u} D]

private instance evaluationHomCoproducts :
    ∀ a b : Dᵒᵖ, HasCoproductsOfShape (a ⟶ b) SSet.{u} :=
  fun a b => hasCoproductsOfShape_of_small SSet.{u} (a ⟶ b)

private instance evaluationHomProducts :
    ∀ a b : Dᵒᵖ, HasProductsOfShape (a ⟶ b) SSet.{u} :=
  fun a b => hasProductsOfShape_of_small SSet.{u} (a ⟶ b)

/-- Evaluate the entire original transfinite witness, at any existing ordinal size.
The original functor, colimit cocone, bottom isomorphism and maps are retained. -/
def evalKanTrivialMonoTransfiniteComposition
    {K : Type z} [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    {X Y : SimplicialPresheaf.{u} D} {f : X ⟶ Y}
    (h : (monomorphisms (SimplicialPresheaf.{u} D) ⊓
      objectwiseKanWeakEquivalences D).TransfiniteCompositionOfShape K f) (d : Dᵒᵖ) :
    (trivialCofibrations SSet.{u}).TransfiniteCompositionOfShape K (f.app d) := by
  let : ((evaluation Dᵒᵖ SSet.{u}).obj d).IsLeftAdjoint :=
    ⟨_, ⟨evaluationAdjunctionLeft SSet.{u} d⟩⟩
  let : PreservesWellOrderContinuousOfShape K ((evaluation Dᵒᵖ SSet.{u}).obj d) :=
    ⟨fun _ _ => inferInstance⟩
  have hLE : monomorphisms (SimplicialPresheaf.{u} D) ⊓
      objectwiseKanWeakEquivalences D ≤
      (trivialCofibrations SSet.{u}).inverseImage ((evaluation Dᵒᵖ SSet.{u}).obj d) := by
    rw [monomorphisms_inf_objectwiseKanWeakEquivalences_eq]
    intro A B g hg
    exact hg d
  exact (h.ofLE hLE).map

private theorem scalarTrivialCofibrations_isStableUnderTransfiniteComposition :
    (trivialCofibrations SSet.{u}).IsStableUnderTransfiniteComposition.{z} := by
  rw [← fibrations_llp]
  infer_instance

instance monomorphisms_inf_objectwiseKanWeakEquivalences_isStableUnderTransfiniteComposition :
    (monomorphisms (SimplicialPresheaf.{u} D) ⊓
      objectwiseKanWeakEquivalences D).IsStableUnderTransfiniteComposition.{z} where
  isStableUnderTransfiniteCompositionOfShape K _ _ _ _ := by
    constructor
    rintro X Y f ⟨h⟩
    rw [monomorphisms_inf_objectwiseKanWeakEquivalences_eq]
    intro d
    let : (trivialCofibrations SSet.{u}).IsStableUnderTransfiniteComposition.{z} :=
      scalarTrivialCofibrations_isStableUnderTransfiniteComposition
    exact (trivialCofibrations SSet.{u}).transfiniteCompositionsOfShape_le K _
      ⟨evalKanTrivialMonoTransfiniteComposition D h d⟩

private theorem mono_evaluationLeftAdjoint_map (d : Dᵒᵖ)
    {A B : SSet.{u}} (a : A ⟶ B) [Mono a] :
    Mono ((evaluationLeftAdjoint SSet.{u} d).map a) := by
  let : Cofibration a := (cofibration_iff a).mpr (by
    simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using
      (show Mono a from inferInstance))
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro e
  change Mono (Limits.Sigma.map (fun _ : d ⟶ e => a))
  have hc : Cofibration (Limits.Sigma.map (fun _ : d ⟶ e => a)) := inferInstance
  simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using
    (cofibration_iff _).mp hc

/-- Global mono-RLP gives actual scalar trivial fibrations at every original component.
This is only the global-to-objectwise implication. -/
theorem globalMonos_rlp_le_objectwiseTrivialFibrations :
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp ≤
      (trivialFibrations SSet.{u}).functorCategory Dᵒᵖ := by
  intro X Y p hp d
  rw [← cofibrations_rlp]
  intro A B a ha
  have hm : Mono a := by
    simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using ha
  let : Mono a := hm
  have hFreeMono : monomorphisms (SimplicialPresheaf.{u} D)
      ((evaluationLeftAdjoint SSet.{u} d).map a) :=
    mono_evaluationLeftAdjoint_map D d a
  exact ((evaluationAdjunctionRight SSet.{u} d).hasLiftingProperty_iff a p).mp
    (hp _ hFreeMono)

/-- The original global mono-RLP class lies in the original objectwise weak class. -/
theorem globalMonos_rlp_le_objectwiseKanWeakEquivalences :
    (monomorphisms (SimplicialPresheaf.{u} D)).rlp ≤ objectwiseKanWeakEquivalences D := by
  intro X Y p hp d
  exact (globalMonos_rlp_le_objectwiseTrivialFibrations D p hp d).2

end LocallySmallEvaluation

end SimplicialPresheaf
