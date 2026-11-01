/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQCentralDifference

/-! Full genuine Q equality compares complete source Griess actions up to the local center.
The reused fiber lemma is polymorphic and has no axis or source-word parameters.
These symbolic proof drafts are uncompiled; no source spin orientation is selected. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- Equal full Q actions give one global central alternative for the complete Griess maps. -/
theorem generatedTenth_source_fibers_griess_central_difference
    (f g : localFiberSubgroup)
    (hQ : spinConjugation f.val.1 = spinConjugation g.val.1) :
    localGriessRepresentation f = localGriessRepresentation g ∨
      localGriessRepresentation f = localCentralGriess * localGriessRepresentation g := by
  have hf : rhoLocal (localFiberIntoH f) = localGriessRepresentation f := rfl
  have hg : rhoLocal (localFiberIntoH g) = localGriessRepresentation g := rfl
  rcases generatedTwelfth_full_Q_fiber_central_difference f g hQ with hh | hh
  · left
    exact hf.symm.trans ((congrArg rhoLocal hh).trans hg)
  · right
    calc
      localGriessRepresentation f = rhoLocal (localFiberIntoH f) := hf.symm
      _ = rhoLocal (inclQ qCentralInvolution * localFiberIntoH g) := congrArg rhoLocal hh
      _ = rhoLocal (inclQ qCentralInvolution) * rhoLocal (localFiberIntoH g) :=
        rhoLocal.map_mul _ _
      _ = localCentralGriess * localGriessRepresentation g := by
        rw [hg]
        rfl

/-- Constructor Q and quotient bindings compare every full image with the genuine central image.
For genuine fibers the full Q hypothesis already forces the projection relation, so the
explicit quotient binding is retained as constructor input rather than a sign choice. -/
theorem generatedTenth_source_fibers_griess_image_central_difference
    (f g : localFiberSubgroup)
    (hQ : spinConjugation f.val.1 = spinConjugation g.val.1)
    (_hspatial : QuotientGroup.mk' signsSubgroup f.val.2 =
      QuotientGroup.mk' signsSubgroup g.val.2) (x : GriessSpace) :
    localGriessRepresentation f x = localGriessRepresentation g x ∨
      localGriessRepresentation f x = localCentralGriess (localGriessRepresentation g x) := by
  rcases generatedTenth_source_fibers_griess_central_difference f g hQ with hh | hh
  · left
    exact LinearEquiv.congr_fun hh x
  · right
    simpa only [LinearEquiv.mul_apply] using LinearEquiv.congr_fun hh x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
