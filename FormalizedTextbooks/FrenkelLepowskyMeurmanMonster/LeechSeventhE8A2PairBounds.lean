/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RealRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortGeometry

/-! The actual Leech minimum bounds the physical pairing of distinct section root lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Distinct genuine section root lines have squared physical pairing at most four. -/
theorem leechSeventhE8RealRoot_pairing_square_bound (r s : Fin 120) (hrs : r ≠ s) :
    (stdPairingFun (leechSeventhE8RealRoot r) (leechSeventhE8RealRoot s)) ^ 2 ≤ 4 := by
  have hn : leechSeventhE8RootLabel r ≠ leechSeventhE8RootLabel s := by
    intro h
    exact hrs (leechSeventhE8RootLabel_injective h)
  have hp := griessShort_pairing_bounds _ _ hn
  have hm := mul_nonneg (sub_nonneg.mpr hp.2)
    (show 0 ≤ (2 : ℝ) + stdPairingFun (griessShortVector (leechSeventhE8RootLabel r))
      (griessShortVector (leechSeventhE8RootLabel s)) by linarith only [hp.1])
  have hsq : (stdPairingFun (griessShortVector (leechSeventhE8RootLabel r))
      (griessShortVector (leechSeventhE8RootLabel s))) ^ 2 ≤ 4 := by
    nlinarith only [hm]
  change (griessShortVector (leechSeventhE8RootLabel r) ⬝ᵥ
    griessShortVector (leechSeventhE8RootLabel s)) ^ 2 ≤ 4 at hsq
  rcases leechSeventhE8RealRoot_label_sign r with hr | hr <;>
    rcases leechSeventhE8RealRoot_label_sign s with hs | hs <;>
    rw [hr, hs] <;> change (_ ⬝ᵥ _) ^ 2 ≤ 4 <;>
    simpa only [dotProduct_neg, neg_dotProduct, neg_neg, neg_sq] using hsq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
