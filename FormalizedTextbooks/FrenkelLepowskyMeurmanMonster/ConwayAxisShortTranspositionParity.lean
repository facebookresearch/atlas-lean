/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpectrum

/-! The actual integer short-vector pairing and its extraspecial commutator parity.
Integrality is derived from the genuine integral basis half-norm identity. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- The binary commutator character of two actual preferred short lifts. -/
noncomputable def conwayAxisShortCommutator (r u : GriessShortIndex) : ZMod 2 :=
  qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ u).base) +
    qBeta (toAdd (griessShortQ u).base) (toAdd (griessShortQ r).base)

/-- Physical short-vector pairings are integers, and their parity is exactly
the actual extraspecial commutator character. -/
theorem conwayAxisShort_pairing_integer_parity (r u : GriessShortIndex) :
    ∃ n : ℤ, stdPairingFun (griessShortVector r) (griessShortVector u) = (n : ℝ) ∧
      conwayAxisShortCommutator r u = (n : ZMod 2) := by
  let w : leechIntegral := griessShortLatticeVector r + griessShortLatticeVector u
  let k : ℤ := leechIntegralHalfNorm (leechExplicitCoordinates w)
  have hsq : leechSquareSum w.val = 16 * k := by
    rw [← leechExplicitCoordinates_vector w, leechBasis_squareSum]
  have hsum : leechSquareSum w.val = 64 +
      2 * leechIntegralPairing (griessShortIntegral r) (griessShortIntegral u) := by
    change leechSquareSum (griessShortIntegral r + griessShortIntegral u) = _
    rw [leechSquareSum_add, griessShortIntegral_squareSum, griessShortIntegral_squareSum]
    ring
  have hi : leechIntegralPairing (griessShortIntegral r) (griessShortIntegral u) =
      8 * (k - 4) := by omega
  have hpair : stdPairingFun (griessShortVector r) (griessShortVector u) =
      ((k - 4 : ℤ) : ℝ) := by
    rw [griessShortVector_pairing, hi]
    push_cast
    ring
  have hw : leechHyperbolicCoordinates (leechReduction w) =
      toAdd (griessShortQ r).base + toAdd (griessShortQ u).base := by
    dsimp only [w]
    rw [map_add, map_add]
    rfl
  have hp := leechHyperbolicCoordinates_halfNorm w
  rw [hsq, Int.mul_ediv_cancel_left _ (by decide : (16 : ℤ) ≠ 0), hw] at hp
  have hr := griessShortQ_squareQuad r
  have hu := griessShortQ_squareQuad u
  change qBeta (toAdd (griessShortQ r).base) (toAdd (griessShortQ r).base) = 0 at hr
  change qBeta (toAdd (griessShortQ u).base) (toAdd (griessShortQ u).base) = 0 at hu
  change (k : ZMod 2) = qBeta (toAdd (griessShortQ r).base + toAdd (griessShortQ u).base)
    (toAdd (griessShortQ r).base + toAdd (griessShortQ u).base) at hp
  rw [qBeta_add_left, qBeta_add_right, qBeta_add_right, hr, hu] at hp
  simp only [zero_add, add_zero] at hp
  refine ⟨k - 4, hpair, ?_⟩
  rw [Int.cast_sub, Int.cast_ofNat, show (4 : ZMod 2) = 0 by decide, sub_zero]
  exact hp.symm

/-- The integer pairing of distinct actual short labels is one of the five source values. -/
theorem conwayAxisShort_pairing_cases (r u : GriessShortIndex) (hur : u ≠ r) :
    ∃ n : ℤ, (-2 ≤ n ∧ n ≤ 2) ∧
      stdPairingFun (griessShortVector r) (griessShortVector u) = (n : ℝ) ∧
      conwayAxisShortCommutator r u = (n : ZMod 2) := by
  obtain ⟨n, hn, hp⟩ := conwayAxisShort_pairing_integer_parity r u
  obtain ⟨hl, hh⟩ := griessShort_pairing_bounds r u hur.symm
  rw [hn] at hl hh
  exact ⟨n, ⟨by exact_mod_cast hl, by exact_mod_cast hh⟩, hn, hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
