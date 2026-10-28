/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SectionRoots

/-! The full genuine section group preserves the intrinsic A2 root-pair predicate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every full actual section isometry preserves the absolute original integral root pairing. -/
theorem leechSeventhE8SectionRoot_pairing_abs (g : leechSeventhE8SectionGroup)
    (r s : Fin 120) :
    |∑ i, leechSeventhE8RootLocal (leechSeventhE8SectionRootIndex g r) i *
      leechSeventhE8RootLocal (leechSeventhE8SectionRootIndex g s) i| =
        |∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i| := by
  have hp := g.val.property.1 (leechSeventhE8RealRoot r) (leechSeventhE8RealRoot s)
  change (g.val.val (leechSeventhE8RealRoot r)) ⬝ᵥ
    (g.val.val (leechSeventhE8RealRoot s)) =
      leechSeventhE8RealRoot r ⬝ᵥ leechSeventhE8RealRoot s at hp
  have hr : |leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g r) ⬝ᵥ
      leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g s)| =
        |leechSeventhE8RealRoot r ⬝ᵥ leechSeventhE8RealRoot s| := by
    rcases leechSeventhE8SectionRoot_real_sign g r with hru | hru <;>
      rcases leechSeventhE8SectionRoot_real_sign g s with hsu | hsu <;>
      rw [hru, hsu] at hp <;>
      simpa only [dotProduct_neg, neg_dotProduct, neg_neg, abs_neg] using congrArg abs hp
  change |stdPairingFun _ _| = |stdPairingFun _ _| at hr
  rw [leechSeventhE8RealRoot_pairing, leechSeventhE8RealRoot_pairing] at hr
  simp only [abs_div, show |(8 : ℝ)| = 8 by norm_num] at hr
  have he := (div_left_inj' (by norm_num : (8 : ℝ) ≠ 0)).mp hr
  exact_mod_cast he

/-- The intrinsic nonorthogonal two-root condition is invariant under the full actual section. -/
theorem leechSeventhE8SectionRoot_nonorthogonal (g : leechSeventhE8SectionGroup)
    (r s : Fin 120)
    (hrs : |∑ i, leechSeventhE8RootLocal r i * leechSeventhE8RootLocal s i| = 16) :
    |∑ i, leechSeventhE8RootLocal (leechSeventhE8SectionRootIndex g r) i *
      leechSeventhE8RootLocal (leechSeventhE8SectionRootIndex g s) i| = 16 := by
  rw [leechSeventhE8SectionRoot_pairing_abs, hrs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
