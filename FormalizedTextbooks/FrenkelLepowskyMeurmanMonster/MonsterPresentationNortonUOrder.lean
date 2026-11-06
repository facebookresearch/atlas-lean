/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete literal Norton u word has thirteenth power one in the actual generated group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderNontrivial

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem spin_power_fixed (s : SpinHolomorph) (v : SpinSpace)
    (h : s.val v = v) (n : ℕ) : (s ^ n).val v = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change (s ^ n).val (s.val v) = v
    rw [h, ih]

/-- The positive central sign makes the full actual spin word have thirteenth power one. -/
theorem monsterNortonUFiber_spin_thirteen : monsterNortonUFiber.val.1 ^ 13 = 1 := by
  obtain ⟨c, hc⟩ := monsterNortonUFiber_spin_thirteen_central
  have hf := spin_power_fixed _ _ monsterNortonUFiber_spin_fixed 13
  rw [hc] at hf
  change spinRepresentation (qCentral c) (nortonUIntegerEmbed (monsterNortonFixedState 0)) =
    nortonUIntegerEmbed (monsterNortonFixedState 0) at hf
  rw [spinRepresentation_central] at hf
  have h := congrFun hf (0 : SpinIndex)
  change qSign c * nortonUIntegerEmbed (monsterNortonFixedState 0) 0 =
    nortonUIntegerEmbed (monsterNortonFixedState 0) 0 at h
  rw [monsterNortonFixedEmbed_zero] at h
  have hc0 : c = 0 := by
    by_cases he : c = 0
    · exact he
    · norm_num [qSign, he] at h
  rw [hc, hc0, show qCentral 0 = 1 from rfl, map_one]

private theorem fiber_power_one (f : localFiberSubgroup) (n : ℕ)
    (hs : f.val.1 ^ n = 1) (hl : f.val.2 ^ n = 1) : f ^ n = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · change f.val.1 ^ n = 1
    exact hs
  · change f.val.2 ^ n = 1
    exact hl

/-- Both genuine local fiber components have thirteenth power one. -/
theorem monsterNortonUFiber_thirteen : monsterNortonUFiber ^ 13 = 1 :=
  fiber_power_one _ _ monsterNortonUFiber_spin_thirteen monsterNortonUFiber_leech_thirteen

/-- The complete source word has thirteenth power one in the actual simultaneous-sign quotient H. -/
theorem monsterNortonULocal_thirteen : monsterNortonULocal ^ 13 = 1 := by
  have h := congrArg (QuotientGroup.mk' localDiagonalSubgroup) monsterNortonUFiber_thirteen
  rw [map_pow, map_one] at h
  exact h

/-- The literal Norton source word satisfies its thirteenth-power relation in the named group G. -/
theorem y555NortonActualU_thirteen : y555NortonActualU ^ 13 = 1 := by
  rw [← monsterNortonULocal_generated, ← map_pow, monsterNortonULocal_thirteen, map_one]

/-- The actual literal Norton word has exact order thirteen in the generated group. -/
theorem y555NortonActualU_orderOf : orderOf y555NortonActualU = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime y555NortonActualU_thirteen y555NortonActualU_ne_one

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
