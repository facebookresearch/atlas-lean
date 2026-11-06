/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQCentralDifference

/-! Full extraspecial conjugation determines both complete matrix and signed-short source blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equal complete Q conjugation retains the entire actual incoming matrix
and signed-short blocks. -/
theorem generatedTwelfth_full_Q_matrix_short_blocks (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).1 =
      (griessConwayEncode (rhoLocal (localFiberIntoH g) x)).1 ∧
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).2.1 =
      (griessConwayEncode (rhoLocal (localFiberIntoH g) x)).2.1 := by
  rcases generatedTwelfth_full_Q_fiber_central_difference f g he with hh | hh
  · rw [hh]
    exact ⟨rfl, rfl⟩
  · rw [hh, map_mul, LinearEquiv.mul_apply]
    change (griessConwayEncode
      (localCentralGriess (rhoLocal (localFiberIntoH g) x))).1 = _ ∧
      (griessConwayEncode
        (localCentralGriess (rhoLocal (localFiberIntoH g) x))).2.1 = _
    rw [localCentralGriess_encode]
    exact ⟨rfl, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
