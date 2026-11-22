/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacement
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWhitehead

/-!
# Original terminal lifting and local Whitehead

The original local-trivial monomorphisms lift into exactly the original
local-fibrant objects. The proof uses the actual local-cell unit and a
base-trivial composite between local objects. Local Whitehead is then
reconciled with the same original objectwise scalar weak class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- A genuinely local target lifts every original local-trivial mono by a base-trivial composite
retraction. -/
private theorem localFibrant_terminalRlp (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) (hZ : isOriginalLocalFibrant S Z) :
    (localTrivialMonomorphisms S).rlp (terminal.from Z) := by
  let _ : (localTrivialMonomorphisms S).IsStableUnderCobaseChange :=
    localTrivialMonomorphisms_isStableUnderCobaseChange S
  let _ : (localTrivialMonomorphisms S).IsMultiplicative :=
    localTrivialMonomorphisms_isMultiplicative S
  let _ : IsFibrant Z := hZ.1
  intro A B f hf
  refine ⟨fun {top bottom} sq => ?_⟩
  let P := pushout f top
  let j : Z ⟶ P := pushout.inr f top
  let η : P ⟶ (originalLocalCellReplacement S).obj P := (originalLocalCellUnit S).app P
  let k : Z ⟶ (originalLocalCellReplacement S).obj P := j ≫ η
  have hj : localTrivialMonomorphisms S j :=
    (localTrivialMonomorphisms S).of_isPushout (IsPushout.of_hasPushout f top).flip hf
  have hη : localTrivialMonomorphisms S η := originalLocalCellUnit_mono_weak S P
  have hk : localTrivialMonomorphisms S k :=
    (localTrivialMonomorphisms S).comp_mem j η hj hη
  have hRP : isOriginalLocalFibrant S ((originalLocalCellReplacement S).obj P) :=
    originalLocalCellReplacement_localFibrant S P
  have hkw : weakEquivalences (SimplicialPresheaf.{u} D) k :=
    (originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S k hZ hRP).mp hk.2
  have hkc : cofibrations (SimplicialPresheaf.{u} D) k := by
    change (data D).model.categoryWithCofibrations.cofibrations k
    rw [(data D).cofibrations_eq]
    exact hk.1
  let _ : Cofibration k := (cofibration_iff k).mpr hkc
  let _ : WeakEquivalence k := (weakEquivalence_iff k).mpr hkw
  have liftSq : CommSq (𝟙 Z) k (terminal.from Z)
      (terminal.from ((originalLocalCellReplacement S).obj P)) :=
    ⟨terminal.hom_ext _ _⟩
  let _ : liftSq.HasLift :=
    (ModelCategory.cm4a k (terminal.from Z)).sq_hasLift liftSq
  let r := liftSq.lift
  have hret : k ≫ r = 𝟙 Z := liftSq.fac_left
  let l : B ⟶ Z := pushout.inl f top ≫ η ≫ r
  have hl : f ≫ l = top := by
    calc
      f ≫ l = (f ≫ pushout.inl f top) ≫ η ≫ r := by
        simp only [l, Category.assoc]
      _ = (top ≫ j) ≫ η ≫ r := by rw [pushout.condition]
      _ = top ≫ (k ≫ r) := by simp only [k, Category.assoc]
      _ = top := by rw [hret, Category.comp_id]
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := terminal.hom_ext _ _ }⟩⟩

/-- The actual constructed generator system gives the reverse terminal implication on the same
original target. -/
private theorem terminalRlp_localFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D)
    (h : (localTrivialMonomorphisms S).rlp (terminal.from Z)) :
    isOriginalLocalFibrant S Z := by
  let d := originalLocalCellData S
  let _ : Fact d.κ.IsRegular := d.regular
  let _ : OrderBot d.κ.ord.ToType := d.orderBot
  rcases d.properties with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRaw, _⟩
  have hJ : (originalLocalGenerators d.T).rlp (terminal.from Z) := by
    intro A B f hf
    exact h f (d.generatorWeak f hf)
  exact (hRaw Z).mp hJ

/-- The entire original terminal criterion follows without a localized model or HFC outcome. -/
theorem localTrivialMonomorphisms_terminal_iff (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) :
    (localTrivialMonomorphisms S).rlp (terminal.from Z) ↔ isOriginalLocalFibrant S Z :=
  ⟨terminalRlp_localFibrant S Z, localFibrant_terminalRlp S Z⟩

omit [Small.{u} I] in
/-- Between actual original local-fibrant endpoints, local weakness is the same objectwise scalar
class at every original site. -/
theorem originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hA : isOriginalLocalFibrant S A) (hB : isOriginalLocalFibrant S B) :
    originalLocalEquivalences S f ↔
      (SSet.realizationWeakEquivalences.{u}).functorCategory Dᵒᵖ f := by
  have h := originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S f hA hB
  change (originalLocalEquivalences S f ↔
    (data D).model.categoryWithWeakEquivalences.weakEquivalences f) at h
  rw [(data D).weakEquivalences_eq] at h
  exact h

end SimplicialPresheaf.InjectiveKan
