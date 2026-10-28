/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransitions

/-! A genuine monomial change of coordinates puts the standard root in the Xi-fixed line. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- One actual Golay sign has the prescribed opposite lower tetrad bits. -/
def leechRootedA2XiTransportSign : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 256), ⟨_, rfl⟩⟩

/-- The two required signs are checked against the original encoder. -/
theorem leechRootedA2XiTransportSign_bits :
    leechRootedA2XiTransportSign.val 1 = 0 ∧ leechRootedA2XiTransportSign.val 2 = 1 := by
  decide +kernel

/-- An actual monomial isometry carries the standard sum root to the Xi-fixed difference root. -/
theorem leechRootedA2XiTransport_exists :
    ∃ b : leechIsomSubgroup, b ∈ golayMonomialSubgroup ∧
      leechIntegralAction b leechRootedA2Root = leechRootedA2XiRoot := by
  let a : Fin 3 → Fin 24 := ![0, 1, 4]
  let c : Fin 3 → Fin 24 := ![1, 2, 4]
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a c
    (by decide +kernel) (by decide +kernel)
  have hp0 : p.val 0 = 1 := hp 0
  have hp1 : p.val 1 = 2 := hp 1
  refine ⟨golaySignIsometry leechRootedA2XiTransportSign * golayPermutationIsometry p,
    ⟨_, _, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  funext i
  have h0 : p.val.symm i = 0 ↔ i = 1 := by rw [p.val.symm_apply_eq, hp0]
  have h1 : p.val.symm i = 1 ↔ i = 2 := by rw [p.val.symm_apply_eq, hp1]
  have hb := leechRootedA2XiTransportSign_bits
  simp only [golayIntegerSign, golayIntegerPermute, leechRootedA2Root,
    leechRootedA2RootIntegral, h0, h1, leechRootedA2XiRoot]
  by_cases hi1 : i = 1
  · subst i
    simp [hb.1]
  · by_cases hi2 : i = 2
    · subst i
      simp [hb.2]
    · simp [hi1, hi2]

/-- Conjugating the original Xi by the genuine root transporter fixes the standard root. -/
theorem leechRootedA2XiTransport_conjugate_fixes (b : leechIsomSubgroup)
    (hb : leechIntegralAction b leechRootedA2Root = leechRootedA2XiRoot) :
    leechIntegralAction (b⁻¹ * co1XiIsometry * b) leechRootedA2Root =
      leechRootedA2Root := by
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply, hb,
    leechRootedA2XiRoot_fixed, ← hb, ← LinearEquiv.mul_apply, ← map_mul,
    inv_mul_cancel, map_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
