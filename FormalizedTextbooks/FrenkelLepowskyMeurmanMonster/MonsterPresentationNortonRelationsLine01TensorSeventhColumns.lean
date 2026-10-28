/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A complete sixteen-column expansion of the seventh actual first-line tensor state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PhysicalSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem first16_columns (T : SpinIndex → Fin 24 → ℝ) (v : Fin 16 → SpinSpace)
    (c : ℝ) (hc : ∀ i t, T t (Fin.castLE (by omega) i) = c * v i t)
    (hz : ∀ t j, 16 ≤ j.val → T t j = 0) :
    T = c • ∑ i : Fin 16, conwaySpinColumn (v i) (Fin.castLE (by omega) i) := by
  ext t j
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, conwaySpinColumn]
  by_cases hj : j.val < 16
  · let k : Fin 16 := ⟨j.val, hj⟩
    have he : (Fin.castLE (by omega) k : Fin 24) = j := Fin.ext rfl
    rw [Finset.sum_eq_single k]
    · rw [← he, ite_eq_left rfl]
      exact hc k t
    · intro i _ hi
      have hn : j ≠ Fin.castLE (by omega) i := by
        intro h
        apply hi
        apply Fin.ext
        exact (congrArg Fin.val h).symm
      exact ite_eq_right hn
    · simp
  · rw [hz t j (by omega)]
    apply Eq.symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    change j.val = i.val at hv
    omega

/-- The entire actual seventh tensor is the finite sum of its sixteen verified spin packets. -/
theorem monsterNortonLine01TensorSeventh_columns :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2 =
      (1 / (4096 * Real.sqrt 2) : ℝ) • ∑ i : Fin 16,
        conwaySpinColumn (nortonUIntegerEmbed (monsterNortonLine01TensorSeventhPacket i))
          (Fin.castLE (by omega) i) := by
  apply first16_columns
  · intro i t
    have h := monsterNortonLine01TensorSeventhInteger_actual (nortonUIntegerLabel t)
      (Fin.castLE (by omega) i)
    rw [nortonUIntegerLabel_inverse, monsterNortonLine01TensorSeventhPacket_actual] at h
    exact h
  · exact monsterNortonLine01TensorSeventh_physical_zero

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
