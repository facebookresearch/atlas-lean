/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer.Proper
import Mathlib.CategoryTheory.Types.Basic

/-!
# Full original evaluation-family properness contracts

The original square orientation and the weakest category-class parents are
fixed. A constant evaluation gives a concrete failure of weak detection;
that essential hypothesis cannot be replaced by preservation alone.
-/

set_option autoImplicit false
noncomputable section
universe s uC vC uM vM u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EvaluationTransfer

namespace EvaluationPropernessTests

section Primitive

variable {C : Type uC} [Category.{vC} C]
  {M : Type uM} [Category.{vM} M] {S : Type s}
  (R : S → C ⥤ M) (W P : MorphismProperty C) (WM Q : MorphismProperty M)
  (hW : W = evaluationProperty R WM)
  (hP : P ≤ evaluationProperty R Q)
  (hBase : WM.IsStableUnderCobaseChangeAgainst Q)
  (hPush : ∀ (s : S) {A B X : C} (i : A ⟶ B) (f : A ⟶ X),
    P i → W f → PreservesColimit (span i f) (R s))

include hW hP hBase hPush in
/-- The full primitive contract keeps the given classes and actual square family. -/
theorem whole_primitive_contract : W.IsStableUnderCobaseChangeAgainst P :=
  cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) (hi : P i) (hf : W f) : W f' :=
  (cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush).of_isPushout
    sq hi hf

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) (hi : P i) (hf : W f) (s : S) :
    WM ((R s).map f') := by
  have h := (cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush).of_isPushout
    sq hi hf
  rw [hW] at h
  exact (evaluationProperty_iff R WM f').1 h s

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (_sq : IsPushout i f f' j) (_hi : P i) (_hf : W f) : True := by
  fail_if_success
    have _ : W f' :=
      IsStableUnderCobaseChangeAgainst.of_isPushout
        (cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush) _sq _hf _hi
  trivial

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) (hi : P i) (hf : W f) (s : S) :
    IsPushout ((R s).map i) ((R s).map f) ((R s).map f') ((R s).map j) := by
  let _ : PreservesColimit (span i f) (R s) := hPush s i f hi hf
  exact sq.map (R s)

example {A B : C} (i : A ⟶ B) (hi : P i) (hId : W (𝟙 A)) :
    W (𝟙 B) :=
  (cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush).of_isPushout
    (IsPushout.of_id_snd (f := i)) hi hId

example {A X : C} (f : A ⟶ X) (hId : P (𝟙 A)) (hf : W f) :
    W f :=
  (cobaseChangeAgainst_of_evaluations R W P WM Q hW hP hBase hPush).of_isPushout
    (IsPushout.of_id_fst (f := f)) hId hf

end Primitive

section GivenCategoryClasses

variable {C : Type uC} [Category.{vC} C]
  [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  {M : Type uM} [Category.{vM} M] [CategoryWithWeakEquivalences M]
  {S : Type s} (R : S → C ⥤ M) (Q : MorphismProperty M)
  (hW : weakEquivalences C = evaluationProperty R (weakEquivalences M))
  (hCof : cofibrations C ≤ evaluationProperty R Q)
  (hBase : (weakEquivalences M).IsStableUnderCobaseChangeAgainst Q)
  (hPush : ∀ (s : S) {A B X : C} (i : A ⟶ B) (f : A ⟶ X),
    cofibrations C i → weakEquivalences C f →
      PreservesColimit (span i f) (R s))

example : IsLeftProper C :=
  isLeftProper_of_evaluations R Q hW hCof hBase hPush

example :
    (isLeftProper_of_evaluations R Q hW hCof hBase hPush).weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations =
    cobaseChangeAgainst_of_evaluations R (weakEquivalences C)
      (cofibrations C) (weakEquivalences M) Q hW hCof hBase hPush := rfl

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' := by
  let _ : IsLeftProper C :=
    isLeftProper_of_evaluations R Q hW hCof hBase hPush
  exact IsLeftProper.weakEquivalence_of_isPushout sq

example : True := by
  fail_if_success let _ : IsLeftProper C := inferInstance
  trivial

end GivenCategoryClasses

section StandardBaseCofibrations

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {M : Type uM} [Category.{vM} M] [ModelCategory M] [IsLeftProper M]
  {S : Type s} (R : S → C ⥤ M)
  (hW : weakEquivalences C = evaluationProperty R (weakEquivalences M))
  (hCof : cofibrations C ≤ evaluationProperty R (cofibrations M))
  (hPush : ∀ (s : S) {A B X : C} (i : A ⟶ B) (f : A ⟶ X),
    cofibrations C i → weakEquivalences C f →
      PreservesColimit (span i f) (R s))

example : IsLeftProper C :=
  isLeftProper_of_evaluations R (cofibrations M) hW hCof inferInstance hPush

example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' := by
  let _ : IsLeftProper C :=
    isLeftProper_of_evaluations R (cofibrations M) hW hCof inferInstance hPush
  exact IsLeftProper.weakEquivalence_of_isPushout sq

end StandardBaseCofibrations

section IndependentUniverseClients

variable {C₂ : Type 2} [Category.{0} C₂]
  [CategoryWithWeakEquivalences C₂] [CategoryWithCofibrations C₂]
  {M₁ : Type 1} [Category.{1} M₁] [CategoryWithWeakEquivalences M₁]
  (R : ULift.{3} ℕ → C₂ ⥤ M₁) (Q : MorphismProperty M₁)
  (hW : weakEquivalences C₂ = evaluationProperty R (weakEquivalences M₁))
  (hCof : cofibrations C₂ ≤ evaluationProperty R Q)
  (hBase : (weakEquivalences M₁).IsStableUnderCobaseChangeAgainst Q)
  (hPush : ∀ (s : ULift.{3} ℕ) {A B X : C₂} (i : A ⟶ B) (f : A ⟶ X),
    cofibrations C₂ i → weakEquivalences C₂ f →
      PreservesColimit (span i f) (R s))

example : IsLeftProper C₂ :=
  isLeftProper_of_evaluations R Q hW hCof hBase hPush

end IndependentUniverseClients

section EmptyDetection

variable {C : Type uC} [Category.{vC} C]
  {M : Type uM} [Category.{vM} M]
  (R : PEmpty.{s + 1} → C ⥤ M)
  (W P : MorphismProperty C) (WM Q : MorphismProperty M)
  (hW : W = evaluationProperty R WM)
  (hBase : WM.IsStableUnderCobaseChangeAgainst Q)

/-- Empty detection necessarily makes the original detected class universal. -/
example : W = ⊤ := by
  ext X Y f
  rw [hW, evaluationProperty_iff]
  constructor
  · intro _
    trivial
  · intro _ s
    exact nomatch s

example : W.IsStableUnderCobaseChangeAgainst P :=
  cobaseChangeAgainst_of_evaluations R W P WM Q hW
    (by
      intro X Y f hf
      apply (evaluationProperty_iff R Q f).2
      intro s
      exact nomatch s)
    hBase
    (by intro s; exact nomatch s)

example {A B X Y : C} {i : A ⟶ B} {f : A ⟶ X}
    {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) (hi : P i) (hf : W f) : W f' := by
  have h : W.IsStableUnderCobaseChangeAgainst P :=
    cobaseChangeAgainst_of_evaluations R W P WM Q hW
      (by
        intro X Y f hf
        apply (evaluationProperty_iff R Q f).2
        intro s
        exact nomatch s)
      hBase
      (by intro s; exact nomatch s)
  exact h.of_isPushout sq hi hf

end EmptyDetection

section FailureOfDetection

/-- An original map with no inverse in the nonthin category of Types. -/
private def emptyToUnit : PEmpty.{u + 1} ⟶ PUnit.{u + 1} := ↾fun x => nomatch x

/-- A constant functor sends every original map to an isomorphism. -/
private def constantEvaluation : Unit → Type u ⥤ Type u :=
  fun _ => (Functor.const (Type u)).obj PUnit.{u + 1}

example :
    evaluationProperty constantEvaluation (isomorphisms (Type u)) emptyToUnit := by
  apply (evaluationProperty_iff constantEvaluation (isomorphisms (Type u)) emptyToUnit).2
  intro s
  change IsIso (𝟙 PUnit.{u + 1})
  infer_instance

example : ¬ IsIso emptyToUnit.{u} := by
  intro h
  let _ : IsIso emptyToUnit.{u} := h
  exact PEmpty.elim ((inv emptyToUnit.{u}) PUnit.unit)

example :
    isomorphisms (Type u) ≠ evaluationProperty constantEvaluation (isomorphisms (Type u)) := by
  intro h
  have hImage : evaluationProperty constantEvaluation (isomorphisms (Type u)) emptyToUnit := by
    apply (evaluationProperty_iff constantEvaluation (isomorphisms (Type u)) emptyToUnit).2
    intro s
    change IsIso (𝟙 PUnit.{u + 1})
    infer_instance
  have hIso : IsIso emptyToUnit.{u} := by
    change isomorphisms (Type u) emptyToUnit
    rw [h]
    exact hImage
  let _ : IsIso emptyToUnit.{u} := hIso
  exact PEmpty.elim ((inv emptyToUnit.{u}) PUnit.unit)

end FailureOfDetection

#check @HomotopicalAlgebra.EvaluationTransfer.cobaseChangeAgainst_of_evaluations
#check @HomotopicalAlgebra.EvaluationTransfer.isLeftProper_of_evaluations

end EvaluationPropernessTests
