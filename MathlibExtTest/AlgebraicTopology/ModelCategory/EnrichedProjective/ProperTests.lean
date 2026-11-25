/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.Proper
import MathlibExt.CategoryTheory.Enriched.PointwiseColimitReflection

/-!
# Entire given-model enriched properness contracts

Fixed expected clients use the original square, same model and generation
record, and actual Hom-tensor conditions. Original factor maps are retained.
-/

set_option autoImplicit false
noncomputable section

universe w uA uV vV
open CategoryTheory Limits MorphismProperty MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective

namespace GivenEnrichedPropernessTests

section OriginalTensorPredicate

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  [ModelCategory (EnrichedFunctorCat V A)]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
  (P Q : MorphismProperty V) (hI : d.I = generators (A := A) P)
  [Q.RespectsIso] [Q.IsStableUnderRetracts]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
  (hW : weakEquivalences (EnrichedFunctorCat V A) =
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V))
  (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    P f → Q (f ▷ (a ⟶[V] b)))
  (hBase : (weakEquivalences V).IsStableUnderCobaseChangeAgainst Q)

include d hI hW hTensor hBase in
/-- The expected result is properness of the same given enriched model. -/
theorem whole_given_model_contract : IsLeftProper (EnrichedFunctorCat V A) :=
  isLeftProper_of_generatorTensor d P Q hI hW hTensor hBase

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_generatorTensor d P Q hI hW hTensor hBase
  exact IsLeftProper.weakEquivalence_of_isPushout sq

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] (a : A) :
    weakEquivalences V ((EnrichedFunctorCat.evaluation a).map f') := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_generatorTensor d P Q hI hW hTensor hBase
  have h : weakEquivalences (EnrichedFunctorCat V A) f' :=
    (weakEquivalence_iff f').1 (IsLeftProper.weakEquivalence_of_isPushout sq)
  rw [hW] at h
  exact (EvaluationTransfer.evaluationProperty_iff _ _ f').1 h a

example {X Y : EnrichedFunctorCat V A} (i : X ⟶ Y) [Cofibration i] (a : A) :
    Q ((EnrichedFunctorCat.evaluation a).map i) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q i).1
    (cofibrations_le_evaluationProperty d P Q hI hTensor i (mem_cofibrations i)) a

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] (a : A) :
    IsPushout ((EnrichedFunctorCat.evaluation a).map i)
      ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map f')
      ((EnrichedFunctorCat.evaluation a).map j) :=
  sq.map (EnrichedFunctorCat.evaluation a)

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (hcomm : i ≫ f' = f ≫ j)
    (hsq : ∀ a : A, IsPushout ((EnrichedFunctorCat.evaluation a).map i)
      ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map f')
      ((EnrichedFunctorCat.evaluation a).map j))
    [Cofibration i] [WeakEquivalence f] : WeakEquivalence f' := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_generatorTensor d P Q hI hW hTensor hBase
  exact IsLeftProper.weakEquivalence_of_isPushout
    ((EnrichedFunctorCat.isPushout_iff_evaluation hcomm).2 hsq)

example {X Y : EnrichedFunctorCat V A} (i : X ⟶ Y) [Cofibration i] :
    WeakEquivalence (𝟙 Y) := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_generatorTensor d P Q hI hW hTensor hBase
  exact IsLeftProper.weakEquivalence_of_isPushout (IsPushout.of_id_snd (f := i))

example
    (F : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)))
    (g : Arrow (EnrichedFunctorCat V A)) (a : A) :
    Q ((EnrichedFunctorCat.evaluation a).map (F.i.app g)) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q (F.i.app g)).1
    (cofibrations_le_evaluationProperty d P Q hI hTensor (F.i.app g) (F.hi g)) a

example
    (F : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)))
    (g : Arrow (EnrichedFunctorCat V A)) :
    F.i.app g ≫ F.p.app g = g.hom :=
  F.fac_app

end OriginalTensorPredicate

section CofibrantOriginalHoms

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  [IsClosedSymmetricMonoidalModelCategory V] [IsLeftProper V]
  {A : Type uA} [EnrichedCategory V A]
  [ModelCategory (EnrichedFunctorCat V A)]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
  (P : MorphismProperty V) (hI : d.I = generators (A := A) P)
  (hP : P ≤ cofibrations V)
  (hW : weakEquivalences (EnrichedFunctorCat V A) =
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V))
  (hHom : ∀ a b : A, IsCofibrant (a ⟶[V] b))

example : IsLeftProper (EnrichedFunctorCat V A) :=
  isLeftProper_of_isCofibrant_homs d P hI hP hW hHom

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_isCofibrant_homs d P hI hP hW hHom
  exact IsLeftProper.weakEquivalence_of_isPushout sq

example {X Y Z W : EnrichedFunctorCat V A}
    {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] (a : A) :
    weakEquivalences V ((EnrichedFunctorCat.evaluation a).map f') := by
  let _ : IsLeftProper (EnrichedFunctorCat V A) :=
    isLeftProper_of_isCofibrant_homs d P hI hP hW hHom
  have h : weakEquivalences (EnrichedFunctorCat V A) f' :=
    (weakEquivalence_iff f').1 (IsLeftProper.weakEquivalence_of_isPushout sq)
  rw [hW] at h
  exact (EvaluationTransfer.evaluationProperty_iff _ _ f').1 h a

example {X Y : V} (f : X ⟶ Y) (hf : P f) (a b : A) :
    cofibrations V ((a ⟶[V] b) ◁ f) := by
  let _ : IsCofibrant (a ⟶[V] b) := hHom a b
  exact (ihomAdjunction_isQuillenAdjunction_of_isCofibrant
    (a ⟶[V] b)).preservesCofibrations f (hP f hf)

end CofibrantOriginalHoms

end GivenEnrichedPropernessTests
