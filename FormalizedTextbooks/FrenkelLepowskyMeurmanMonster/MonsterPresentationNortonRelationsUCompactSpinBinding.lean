/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binding of the compact operator once the actual fixed-vector certificate is available. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinPhaseData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual fixedness of the explicit vector determines the full compact spin operator exactly. -/
theorem monsterNortonUCompactPositiveSpin_eq_of_fixed
    (hf : monsterNortonUFiber.val.1.val (nortonUIntegerEmbed (monsterNortonFixedState 0)) =
      nortonUIntegerEmbed (monsterNortonFixedState 0)) :
    monsterNortonUFiber.val.1 = monsterNortonUCompactPositiveSpin := by
  obtain ⟨c, hc, hs⟩ := monsterNortonUCompactSpin_scalar
  have hcneg : c = -1 := by
    rcases hc with hc | hc
    · have h := congrFun (hs (nortonUIntegerEmbed (monsterNortonFixedState 0))) 0
      rw [hf] at h
      simp only [Pi.smul_apply, smul_eq_mul, hc, one_mul,
        monsterNortonUCompactSpin_fixed_zero] at h
      have hz : nortonUIntegerLabel (0 : SpinIndex) = 0 := by decide +kernel
      simp only [nortonUIntegerEmbed, hz, monsterNortonFixedState_zero_zero] at h
      norm_num at h
    · exact hc
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [monsterNortonUCompactPositiveSpin_apply]
  simpa only [hcneg, neg_one_smul] using hs x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
