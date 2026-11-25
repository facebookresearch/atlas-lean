/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedProjective
public import MathlibExt.CategoryTheory.Enriched.EndOrdinaryEnrichment
public import MathlibExt.CategoryTheory.Enriched.ScalarParametrizedAdjunctions
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# SM7 for the same original enriched projective model

Only genuine pairs of original scalar/diagram generators are tested in the
source PP hypotheses. The two actual parametrized lifting adjunctions extend
them to the full original left classes. SM7 is an output for every supplied
mapping-end pullback corner, with its original point and projections.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe w uA uV vV u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite

namespace HomotopicalAlgebra.OriginalEnrichedDiagramSM7

section RectangularClosure

variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  [HasPullbacks C₁] [HasPullbacks C₂] [HasPushouts C₃]

/-- Two actual parametrized adjunctions extend the original rectangular generator PP tests. -/
private theorem mixed_left_closure
    (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) (H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁)
    (adj : F ⊣₂ G) (adj' : F.flip ⊣₂ H)
    (P : MorphismProperty C₁) (Q : MorphismProperty C₂) (R : MorphismProperty C₃)
    (h : ∀ {A B : C₁} {K L : C₂} (i : A ⟶ B) (j : K ⟶ L), P i → Q j →
      ∀ (sq : F.PushoutObjObj i j), R.rlp.llp sq.ι)
    {A B : C₁} {K L : C₂} (i : A ⟶ B) (j : K ⟶ L)
    (hi : P.rlp.llp i) (hj : Q.rlp.llp j) (sq : F.PushoutObjObj i j) :
    R.rlp.llp sq.ι := by
  intro X Y p hp
  let c := Functor.PullbackObjObj.ofHasPullback G i p
  apply (adj.hasLiftingProperty_iff sq c).mpr
  apply hj
  intro K' L' j' hj'
  let sq' := Functor.PushoutObjObj.ofHasPushout F i j'
  apply (adj.hasLiftingProperty_iff sq' c).mp
  let c' := Functor.PullbackObjObj.ofHasPullback H j' p
  apply (adj'.hasLiftingProperty_iff sq'.flip c').mpr
  apply hi
  intro A' B' i' hi'
  let sq'' := Functor.PushoutObjObj.ofHasPushout F i' j'
  apply (adj'.hasLiftingProperty_iff sq''.flip c').mp
  exact h i' j' hi' hj' sq'' p hp

end RectangularClosure

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  [HasProducts.{uA} V] [HasEqualizers V]
  (d : CofibrantGenerationData V κ)
  (s : OriginalEnrichedProjective.SourceConditions (A := A) d)

open EnrichedFunctorCat
open EnrichedFunctorCat.ScalarParametrizedAdjunctions

/-- The actual mixed source pushout-product, with the complete original scalar maps. -/
abbrev ScalarPushout {F G : EnrichedFunctorCat V A} {K L : V} (i : F ⟶ G) (j : K ⟶ L) :=
  (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip.PushoutObjObj i j

/-- The full original mapping-end pullback corner with its supplied universal maps. -/
abbrev MappingCorner {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y) :=
  (WeightedEndVariance.bifunctor (V := V) (I := A)).PullbackObjObj i p

/-- Only the literal original I/J generator pairs and their source PP maps are required. -/
structure GeneratorConditions : Prop where
  II : ∀ {F G : EnrichedFunctorCat V A} {K L : V} (i : F ⟶ G) (j : K ⟶ L),
    EnrichedProjective.generators (A := A) d.I i → d.I j →
      ∀ (sq : ScalarPushout i j), (EnrichedProjective.generators (A := A) d.I).rlp.llp sq.ι
  JI : ∀ {F G : EnrichedFunctorCat V A} {K L : V} (i : F ⟶ G) (j : K ⟶ L),
    EnrichedProjective.generators (A := A) d.J i → d.I j →
      ∀ (sq : ScalarPushout i j), (EnrichedProjective.generators (A := A) d.J).rlp.llp sq.ι
  IJ : ∀ {F G : EnrichedFunctorCat V A} {K L : V} (i : F ⟶ G) (j : K ⟶ L),
    EnrichedProjective.generators (A := A) d.I i → d.J j →
      ∀ (sq : ScalarPushout i j), (EnrichedProjective.generators (A := A) d.J).rlp.llp sq.ι

/-- All three SM7 conclusions use the original model and every actual supplied end corner. -/
theorem sm7 (h : GeneratorConditions (A := A) d) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    (∀ {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y),
      cofibrations (EnrichedFunctorCat V A) i → fibrations (EnrichedFunctorCat V A) p →
        ∀ (c : MappingCorner i p), fibrations V c.π) ∧
    (∀ {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y),
      trivialCofibrations (EnrichedFunctorCat V A) i → fibrations (EnrichedFunctorCat V A) p →
        ∀ (c : MappingCorner i p), trivialFibrations V c.π) ∧
    (∀ {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y),
      cofibrations (EnrichedFunctorCat V A) i → trivialFibrations (EnrichedFunctorCat V A) p →
        ∀ (c : MappingCorner i p), trivialFibrations V c.π) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
  let E := OriginalEnrichedProjective.generationData d s
  have hI : E.I.rlp.llp = cofibrations (EnrichedFunctorCat V A) := by
    rw [E.I_rlp, trivialFibrations_llp]
  have hJ : E.J.rlp.llp = trivialCofibrations (EnrichedFunctorCat V A) := by
    rw [E.J_rlp, fibrations_llp]
  have extend := mixed_left_closure
    (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip
    (WeightedEndVariance.bifunctor (V := V) (I := A))
    (cotensorBifunctor (V := V) (A := A))
    (tensorEndParametrized (V := V) (A := A))
    (tensorCotensorParametrized (V := V) (A := A))
  refine ⟨?_, ?_, ?_⟩
  · intro F G X Y i p hi hp c
    rw [← d.J_rlp]
    intro K L j hj
    let sq := Functor.PushoutObjObj.ofHasPushout
      (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip i j
    apply (tensorEndParametrized.hasLiftingProperty_iff sq c).mp
    have hi' : E.I.rlp.llp i := by rw [hI]; exact hi
    have hPP : E.J.rlp.llp sq.ι :=
      extend E.I d.J E.J h.IJ i j hi' (d.J.le_llp_rlp j hj) sq
    exact hPP p (by rw [E.J_rlp]; exact hp)
  · intro F G X Y i p hi hp c
    rw [← d.I_rlp]
    intro K L j hj
    let sq := Functor.PushoutObjObj.ofHasPushout
      (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip i j
    apply (tensorEndParametrized.hasLiftingProperty_iff sq c).mp
    have hi' : E.J.rlp.llp i := by rw [hJ]; exact hi
    have hPP : E.J.rlp.llp sq.ι :=
      extend E.J d.I E.J h.JI i j hi' (d.I.le_llp_rlp j hj) sq
    exact hPP p (by rw [E.J_rlp]; exact hp)
  · intro F G X Y i p hi hp c
    rw [← d.I_rlp]
    intro K L j hj
    let sq := Functor.PushoutObjObj.ofHasPushout
      (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip i j
    apply (tensorEndParametrized.hasLiftingProperty_iff sq c).mp
    have hi' : E.I.rlp.llp i := by rw [hI]; exact hi
    have hPP : E.I.rlp.llp sq.ι :=
      extend E.I d.I E.I h.II i j hi' (d.I.le_llp_rlp j hj) sq
    exact hPP p (by rw [E.I_rlp]; exact hp)

end HomotopicalAlgebra.OriginalEnrichedDiagramSM7
