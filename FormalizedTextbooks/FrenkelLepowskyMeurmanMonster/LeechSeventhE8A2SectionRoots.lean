/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RealRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitGenerators

/-! The full actual section stabilizer permutes the genuine finite E8 root lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full Co0 stabilizer of the selected original coordinate E8 section. -/
abbrev leechSeventhE8SectionGroup :=
  generatedAxisE8SectionStabilizer (golayOctadWord generatedFifthFlagOctad)

/-- Every actual section isometry induces an original finite short-line address. -/
def leechSeventhE8SectionRootIndex (g : leechSeventhE8SectionGroup) (r : Fin 120) : Fin 120 :=
  leechSeventhE8RootLabelEquiv.symm ⟨griessShortPermutation g.val (leechSeventhE8RootLabel r), by
    have hs := (generatedAxisE8SectionStabilizer_mem _ g.val).mp g.property
    change (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)).map
      (leechIntegralAction g.val).toLinearMap =
        generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad) at hs
    rw [← hs]
    exact (generatedAxisE8ShortLines_image_mem g.val _ _).mpr
      (leechSeventhE8Root_label_supported r)⟩

/-- The full section action has exactly the original short-catalogue label at the finite address. -/
theorem leechSeventhE8SectionRootIndex_label (g : leechSeventhE8SectionGroup) (r : Fin 120) :
    leechSeventhE8RootLabel (leechSeventhE8SectionRootIndex g r) =
      griessShortPermutation g.val (leechSeventhE8RootLabel r) := by
  unfold leechSeventhE8SectionRootIndex
  exact congrArg Subtype.val (leechSeventhE8RootLabelEquiv.apply_symm_apply _)

/-- Every actual full section root image has its genuine lattice orientation retained. -/
theorem leechSeventhE8SectionRoot_integral_sign (g : leechSeventhE8SectionGroup) (r : Fin 120) :
    leechIntegralAction g.val (leechSeventhE8Root r) =
        leechSeventhE8Root (leechSeventhE8SectionRootIndex g r) ∨
      leechIntegralAction g.val (leechSeventhE8Root r) =
        -leechSeventhE8Root (leechSeventhE8SectionRootIndex g r) := by
  apply leechShort_same_class _ _
    (by rw [leechIntegralAction_squareSum]; exact leechSeventhE8Root_norm r)
    (leechSeventhE8Root_norm _)
  change leechModTwoAction g.val (leechReduction (leechSeventhE8Root r)) = _
  rw [← leechSeventhE8Root_label_class, ← leechSeventhE8Root_label_class,
    ← griessShortPermutation_class, leechSeventhE8SectionRootIndex_label]

/-- Every actual full section root image has the same genuine sign in physical coordinates. -/
theorem leechSeventhE8SectionRoot_real_sign (g : leechSeventhE8SectionGroup) (r : Fin 120) :
    g.val.val (leechSeventhE8RealRoot r) =
        leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g r) ∨
      g.val.val (leechSeventhE8RealRoot r) =
        -leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g r) := by
  rcases leechSeventhE8SectionRoot_integral_sign g r with h | h
  · left
    rw [leechSeventhE8RealRoot, ← leechIntegralAction_embedding, h]
    rfl
  · right
    rw [leechSeventhE8RealRoot, ← leechIntegralAction_embedding, h]
    rw [Submodule.coe_neg, map_neg]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
