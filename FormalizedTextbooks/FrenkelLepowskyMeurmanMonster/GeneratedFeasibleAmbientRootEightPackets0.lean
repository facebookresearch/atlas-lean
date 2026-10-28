/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightData

/-! Address packets 0 to 23 of the orthogonality check for the positive final
Root8 axis. Each packet checks 1024 short addresses: the packed short numerator is below 48 in
absolute value, or both signed axes are tested exactly against the matrix numerator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Addresses 0 to 1023 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_00 : ∀ u : Fin 1024,
    if hb : 0 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨0 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 1024 to 2047 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_01 : ∀ u : Fin 1024,
    if hb : 1 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨1 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 2048 to 3071 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_02 : ∀ u : Fin 1024,
    if hb : 2 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨2 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 3072 to 4095 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_03 : ∀ u : Fin 1024,
    if hb : 3 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨3 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 4096 to 5119 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_04 : ∀ u : Fin 1024,
    if hb : 4 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨4 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 5120 to 6143 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_05 : ∀ u : Fin 1024,
    if hb : 5 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨5 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 6144 to 7167 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_06 : ∀ u : Fin 1024,
    if hb : 6 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨6 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 7168 to 8191 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_07 : ∀ u : Fin 1024,
    if hb : 7 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨7 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 8192 to 9215 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_08 : ∀ u : Fin 1024,
    if hb : 8 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨8 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 9216 to 10239 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_09 : ∀ u : Fin 1024,
    if hb : 9 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨9 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 10240 to 11263 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_10 : ∀ u : Fin 1024,
    if hb : 10 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨10 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 11264 to 12287 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_11 : ∀ u : Fin 1024,
    if hb : 11 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨11 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 12288 to 13311 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_12 : ∀ u : Fin 1024,
    if hb : 12 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨12 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 13312 to 14335 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_13 : ∀ u : Fin 1024,
    if hb : 13 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨13 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 14336 to 15359 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_14 : ∀ u : Fin 1024,
    if hb : 14 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨14 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 15360 to 16383 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_15 : ∀ u : Fin 1024,
    if hb : 15 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨15 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 16384 to 17407 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_16 : ∀ u : Fin 1024,
    if hb : 16 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨16 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 17408 to 18431 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_17 : ∀ u : Fin 1024,
    if hb : 17 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨17 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 18432 to 19455 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_18 : ∀ u : Fin 1024,
    if hb : 18 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨18 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 19456 to 20479 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_19 : ∀ u : Fin 1024,
    if hb : 19 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨19 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 20480 to 21503 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_20 : ∀ u : Fin 1024,
    if hb : 20 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨20 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 21504 to 22527 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_21 : ∀ u : Fin 1024,
    if hb : 21 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨21 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 22528 to 23551 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_22 : ∀ u : Fin 1024,
    if hb : 22 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨22 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 23552 to 24575 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_23 : ∀ u : Fin 1024,
    if hb : 23 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨23 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
