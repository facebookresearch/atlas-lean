/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Local sign permutations governing pair-block multiplication on an octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCGeneral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
/-- Toggle two octad signs and choose the representative whose last sign is positive. -/
def trialityOctadPairFlip (a b : Fin 8) (e : Fin 64) : Fin 64 :=
  ⟨((trialityEvenMask e ^^^ (2 ^ a.val ^^^ 2 ^ b.val)) ^^^
    if a = 7 ∨ b = 7 then 255 else 0) % 64, by omega⟩
def trialityOctadPairComplement (a b : Fin 8) : ZMod 2 := if a = 7 ∨ b = 7 then 1 else 0
def trialityOctadLocalBit (e : Fin 64) (a : Fin 8) : ZMod 2 :=
  if (trialityEvenMask e).testBit a.val then 1 else 0
def trialityOctadPairColor (a b : Fin 8) (e : Fin 64) : Fin 2 :=
  if (trialityEvenMask e).testBit a.val = (trialityEvenMask e).testBit b.val then 1 else 0
set_option maxHeartbeats 0 in
-- The 8-local-coordinate identity is a finite check in the kernel.
set_option maxRecDepth 10000 in
theorem trialityOctadPairFlip_bit : ∀ (a b : Fin 8) (e : Fin 64), a ≠ b →
    ∀ k : Fin 8, trialityOctadLocalBit (trialityOctadPairFlip a b e) k =
      trialityOctadLocalBit e k + (if k = a then 1 else 0) +
        (if k = b then 1 else 0) + trialityOctadPairComplement a b := by
  unfold trialityOctadLocalBit trialityOctadPairFlip trialityOctadPairComplement
  decide +kernel
set_option maxHeartbeats 0 in
-- The sign-normalization parity identity is a finite check in the kernel.
set_option maxRecDepth 10000 in
theorem trialityOctadPairFlip_omega : ∀ (a b : Fin 8) (e : Fin 64), a ≠ b →
    griessOctadOmegaCoefficient (trialityOctadPairFlip a b e) =
      griessOctadOmegaCoefficient e + ((trialityOctadPairColor a b e).val : ZMod 2) := by
  unfold griessOctadOmegaCoefficient trialityOctadPairFlip trialityOctadPairColor
  decide +kernel
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
