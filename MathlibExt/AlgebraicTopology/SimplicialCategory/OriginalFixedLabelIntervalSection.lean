/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedLabelIntervalFactor

/-!
# Genuine fixed-label sections from an actual original weak interval factor

An actual original fixed-label fibration with cofibrant weak-unit target
has a section once its source has the supplied original equivalence.
The constructed SAME original weak interval maps to that source; its
composite to the target is genuinely weak. Its native horn factorization
supplies the full lift and original cofibrancy supplies the section. All
original object labels and full Hom maps remain unchanged.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalSection
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {P H : FixedObjects walking.{u}} (p : P ⟶ H)
variable (hp : FixedObjectModel.fibrations walking p)
variable (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H))
variable (e : (hom P (BergnerTwoObject.source (𝟙_ SSet.{u}))
  (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf P.val e))
attribute [local instance] FixedObjectModel.modelCategory

include hH in
/-- The actual same-label weak interval composite is genuinely weak by its original terminal-map triangle. -/
theorem composite_weak : FixedObjectModel.weakEquivalences walking
    (OriginalFixedLabelIntervalFactor.map P e he ≫ p) := by
  have hK := OriginalEquivalenceCountableInterval.terminal_weak (vertex P) e he
  have hfac : (OriginalFixedLabelIntervalFactor.map P e he ≫ p) ≫ CodiscreteTerminal.toTerminal H =
      CodiscreteTerminal.toTerminal (OriginalFixedLabelIntervalFactor.object P e he) :=
    CodiscreteTerminal.toTerminal_naturality _
  exact (FixedObjectModel.weakEquivalences walking).of_postcomp _ _ hH
    ((congrArg (fun f => FixedObjectModel.weakEquivalences walking f) hfac).mpr hK)

include hp hH e he in
/-- The original target cofibrancy and SAME native horn factorization construct an actual full fixed-label section. -/
theorem exists_section [IsCofibrant H] : ∃ s : H ⟶ P, s ≫ p = 𝟙 H := by
  let K := OriginalFixedLabelIntervalFactor.object P e he
  let m := OriginalFixedLabelIntervalFactor.map P e he
  let F := FreeFactorization.horn (m ≫ p)
  have hi : FixedObjectModel.weakEquivalences walking F.i :=
    FixedObjectModel.trivialCofibrations_le_weakEquivalences _ F.hi
  have hright : FixedObjectModel.weakEquivalences walking F.p :=
    (FixedObjectModel.weakEquivalences walking).of_precomp _ _ hi
      ((congrArg (fun f => FixedObjectModel.weakEquivalences walking f) F.fac).mpr
        (composite_weak p hH e he))
  have hrt : FixedObjectModel.trivialFibrations walking F.p := by
    rw [FixedObjectModel.trivialFibrations_eq]
    exact ⟨F.hp, hright⟩
  have hsquare : CommSq m F.i p F.p := ⟨F.fac.symm⟩
  let hLift : HasLiftingProperty F.i p := F.hi _ hp
  let _ : hsquare.HasLift := hLift.sq_hasLift hsquare
  have hinitial : FixedObjectModel.cofibrations walking (initial.to H) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (initial.to H)).mp
      (inferInstance : Cofibration (initial.to H))
  have tsquare : CommSq (initial.to F.Z) (initial.to H) F.p (𝟙 H) :=
    ⟨initialIsInitial.hom_ext _ _⟩
  let htLift : HasLiftingProperty (initial.to H) F.p := hinitial _ hrt
  let _ : tsquare.HasLift := htLift.sq_hasLift tsquare
  refine ⟨tsquare.lift ≫ hsquare.lift, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => tsquare.lift ≫ f) hsquare.fac_right).trans tsquare.fac_right)

end CategoryTheory.SimplicialEnrichment.OriginalFixedLabelIntervalSection
