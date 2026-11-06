/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddPairEigen
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase

/-! A stabilizer of the distinguished Hadamard spin state has trivial
conjugation character on every actual pair-short lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem state_zero : generatedOddSpinState 0 1 0 (0 : SpinIndex) = 1 := by
  have hz : generatedOddSpinLow (0 : SpinIndex) = 0 := rfl
  simp [generatedOddSpinState, hz]

/-- An actual Pauli operator fixing the distinguished state commutes with any
preferred short lift for which that state is a nonzero eigenvector. -/
theorem generatedOddSpin_fixed_eigen_phase (q : Q) (r : GriessShortIndex) (a : ℝ)
    (ha : a ≠ 0)
    (hq : spinRepresentation q (generatedOddSpinState 0 1 0) = generatedOddSpinState 0 1 0)
    (hr : spinRepresentation (griessShortQ r) (generatedOddSpinState 0 1 0) =
      a • generatedOddSpinState 0 1 0) : localAxisQPhase r q = 1 := by
  let k := griessShortQ r
  let b := qBeta (toAdd q.base) (toAdd k.base) + qBeta (toAdd k.base) (toAdd q.base)
  have hc : q * k = qCentral b * k * q := by
    have h := congrArg (fun x : Q => x * q) (q_conjugation_central_phase q k)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have h := congrArg (fun x : Q => spinRepresentation x (generatedOddSpinState 0 1 0)) hc
  simp only [map_mul, LinearEquiv.mul_apply] at h
  change spinRepresentation q (spinRepresentation k (generatedOddSpinState 0 1 0)) =
    spinRepresentation (qCentral b) (spinRepresentation k
      (spinRepresentation q (generatedOddSpinState 0 1 0))) at h
  rw [hq, hr, map_smul, hq, spinRepresentation_central] at h
  have he := congrFun h (0 : SpinIndex)
  simp only [Pi.smul_apply, smul_eq_mul, state_zero, mul_one] at he
  have hb : qSign b = 1 := (mul_right_cancel₀ ha (show qSign b * a = 1 * a by
    simpa only [one_mul] using he.symm))
  apply toAdd.injective
  change b = 0
  exact (qSign_eq_one_iff b).mp hb

/-- Every actual pair-minus conjugation phase is trivial on the spin-state stabilizer. -/
theorem generatedOddSpinStateStabilizer_pair_minus_phase (q : Q)
    (hq : q ∈ generatedOddSpinStateStabilizer) (p : Fin 276) :
    localAxisQPhase (Sum.inl (0, p)) q = 1 := by
  apply generatedOddSpin_fixed_eigen_phase q _ 1 one_ne_zero
  · exact hq
  · change spinOperator _ _ = _
    simpa only [one_smul] using generatedOddSpin_pair_minus_eigen p

/-- Every actual pair-plus conjugation phase is trivial on the spin-state stabilizer. -/
theorem generatedOddSpinStateStabilizer_pair_plus_phase (q : Q)
    (hq : q ∈ generatedOddSpinStateStabilizer) (p : Fin 276) :
    localAxisQPhase (Sum.inl (1, p)) q = 1 := by
  apply generatedOddSpin_fixed_eigen_phase q _ (-1) (by norm_num)
  · exact hq
  · change spinOperator _ _ = _
    simpa only [neg_one_smul] using generatedOddSpin_pair_plus_eigen p

/-- All actual pair-short coordinates have trivial phase on the spin-state stabilizer. -/
theorem generatedOddSpinStateStabilizer_pair_phase (q : Q)
    (hq : q ∈ generatedOddSpinStateStabilizer) (s : Fin 2) (p : Fin 276) :
    localAxisQPhase (Sum.inl (s, p)) q = 1 := by
  have hs : s = 0 ∨ s = 1 := by decide +kernel +revert
  rcases hs with rfl | rfl
  · exact generatedOddSpinStateStabilizer_pair_minus_phase q hq p
  · exact generatedOddSpinStateStabilizer_pair_plus_phase q hq p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
