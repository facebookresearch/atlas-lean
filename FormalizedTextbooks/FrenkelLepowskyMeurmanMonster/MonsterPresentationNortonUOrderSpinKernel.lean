/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Norton thirteenth spin power is central, from its actual binary action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem power_conjugate {E : Type*} [Group E] (s : E) (n : ℕ) :
    s * s ^ n * s⁻¹ = s ^ n := by
  rw [← pow_succ', pow_succ, mul_assoc, mul_inv_cancel, mul_one]

private theorem fiber_power_Q (f : localFiberSubgroup) (n : ℕ)
    (hLeech : f.val.2 ^ n = 1) : ∃ q : Q, spinHolomorphIncl q = f.val.1 ^ n := by
  apply spinBinaryAction_kernel_image
  rw [map_pow, f.property, ← map_pow, hLeech, map_one]

/-- The literal Norton's thirteenth spin power is in the actual extraspecial image. -/
theorem monsterNortonUFiber_spin_thirteen_Q :
    ∃ q : Q, spinHolomorphIncl q = monsterNortonUFiber.val.1 ^ 13 :=
  fiber_power_Q monsterNortonUFiber 13 monsterNortonUFiber_leech_thirteen

/-- The only possible thirteenth spin powers are the actual two central signs. -/
theorem monsterNortonUFiber_spin_thirteen_central :
    ∃ c : ZMod 2, monsterNortonUFiber.val.1 ^ 13 = spinHolomorphIncl (qCentral c) := by
  obtain ⟨q, hq⟩ := monsterNortonUFiber_spin_thirteen_Q
  have hf : spinConjugation monsterNortonUFiber.val.1 q = q := by
    apply spinRepresentation_injective
    rw [spinConjugation_representation]
    have h : monsterNortonUFiber.val.1 * spinHolomorphIncl q *
        monsterNortonUFiber.val.1⁻¹ = spinHolomorphIncl q := by
      rw [hq]
      exact power_conjugate _ 13
    exact congrArg Subtype.val h
  have hb : toAdd (qQuotHom q) = 0 := by
    apply monsterNortonUFiber_leech_binary_fixed
    rw [← monsterNortonUFiber.property]
    change qBinaryAction (spinConjugation monsterNortonUFiber.val.1)
      (toAdd (qQuotHom q)) = _
    rw [qBinaryAction_apply, hf]
  have hbase : q.base = 1 := by
    change toAdd q.base = 0 at hb
    exact toAdd.injective hb
  refine ⟨toAdd q.coeff, ?_⟩
  rw [← hq]
  apply congrArg spinHolomorphIncl
  apply NormalizedCocycleExtension.Extension.ext
  · exact hbase
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
