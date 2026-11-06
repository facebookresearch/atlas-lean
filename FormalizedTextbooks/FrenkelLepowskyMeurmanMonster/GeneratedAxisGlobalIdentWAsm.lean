/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWCore

/-! # Factory assembly with the exact packed self dot

Variants of `ident_forward_self` / `ident_inverse_self` in which the tensor self part of the target
is the exact packed dot `tdot w Y Y` (a field-by-field loop), so that no overflow bound for the
multiplicative self dot is needed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-- Forward identification from self pairings, with the exact packed self dot of the target
tensor (no overflow bound needed for the self dot). -/
theorem ident_forward_selfT (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF true L W = selfMatQ W)
    (hp : pairSumQ true L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo true L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w true X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w true Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!true) X) Y : ℚ) / (2 * D * E) =
        (tdot w Y Y : ℚ) / (E * E)) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply ident_forward_GMZ i j h g L W hL hW hLt hWt hX hY hB hBC hx hy (wo := wo)
  rw [pairTriGMZ_parts hok rfl rfl rfl rfl rfl rfl]
  have h128 := self_eq_128 W hW hWt _ hy (identLocal_norm j g)
  rw [selfOctP_eq] at hn
  rw [selfOddP_eq] at ha
  rw [← h128, hm, hp]
  have : W.sden * (W.sden * (selfPairsZ W : ℚ) + L.sden * (octSumZ wo true L W : ℚ) / 8 +
      (oddWZ w true X W : ℚ) / (2 * D)) =
      W.sden * W.sden * ((selfPairsZ W : ℚ) + (selfOctZ W : ℚ) + (selfOddZ W : ℚ)) := by
    rw [hn, ha]
    ring
  rw [this, ht]
  ring

/-- Inverse identification from self pairings, with the exact packed self dot. -/
theorem ident_inverse_selfT (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF false L W = selfMatQ W)
    (hp : pairSumQ false L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo false L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w false X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w false Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!false) X) Y : ℚ) / (2 * D * E) =
        (tdot w Y Y : ℚ) / (E * E)) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) := by
  apply ident_inverse_GMZ i j h g L W hL hW hLt hWt hX hY hB hBC hx hy (wo := wo)
  rw [pairTriGMZ_parts hok rfl rfl rfl rfl rfl rfl]
  have h128 := self_eq_128 W hW hWt _ hy (identLocal_norm j g)
  rw [selfOctP_eq] at hn
  rw [selfOddP_eq] at ha
  rw [← h128, hm, hp]
  have : W.sden * (W.sden * (selfPairsZ W : ℚ) + L.sden * (octSumZ wo false L W : ℚ) / 8 +
      (oddWZ w false X W : ℚ) / (2 * D)) =
      W.sden * W.sden * ((selfPairsZ W : ℚ) + (selfOctZ W : ℚ) + (selfOddZ W : ℚ)) := by
    rw [hn, ha]
    ring
  rw [this, ht]
  ring
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
