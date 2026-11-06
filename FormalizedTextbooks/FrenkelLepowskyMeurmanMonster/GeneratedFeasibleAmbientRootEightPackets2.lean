/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightData

/-! Address packets 48 to 71 of the orthogonality check for the positive final
Root8 axis. Each packet checks 1024 short addresses: the packed short numerator is below 48 in
absolute value, or both signed axes are tested exactly against the matrix numerator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Addresses 49152 to 50175 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_48 : ∀ u : Fin 1024,
    if hb : 48 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨48 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 50176 to 51199 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_49 : ∀ u : Fin 1024,
    if hb : 49 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨49 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 51200 to 52223 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_50 : ∀ u : Fin 1024,
    if hb : 50 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨50 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 52224 to 53247 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_51 : ∀ u : Fin 1024,
    if hb : 51 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨51 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 53248 to 54271 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_52 : ∀ u : Fin 1024,
    if hb : 52 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨52 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 54272 to 55295 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_53 : ∀ u : Fin 1024,
    if hb : 53 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨53 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 55296 to 56319 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_54 : ∀ u : Fin 1024,
    if hb : 54 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨54 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 56320 to 57343 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_55 : ∀ u : Fin 1024,
    if hb : 55 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨55 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 57344 to 58367 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_56 : ∀ u : Fin 1024,
    if hb : 56 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨56 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 58368 to 59391 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_57 : ∀ u : Fin 1024,
    if hb : 57 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨57 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 59392 to 60415 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_58 : ∀ u : Fin 1024,
    if hb : 58 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨58 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 60416 to 61439 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_59 : ∀ u : Fin 1024,
    if hb : 59 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨59 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 61440 to 62463 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_60 : ∀ u : Fin 1024,
    if hb : 60 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨60 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 62464 to 63487 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_61 : ∀ u : Fin 1024,
    if hb : 61 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨61 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 63488 to 64511 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_62 : ∀ u : Fin 1024,
    if hb : 62 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨62 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 64512 to 65535 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_63 : ∀ u : Fin 1024,
    if hb : 63 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨63 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 65536 to 66559 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_64 : ∀ u : Fin 1024,
    if hb : 64 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨64 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 66560 to 67583 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_65 : ∀ u : Fin 1024,
    if hb : 65 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨65 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 67584 to 68607 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_66 : ∀ u : Fin 1024,
    if hb : 66 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨66 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 68608 to 69631 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_67 : ∀ u : Fin 1024,
    if hb : 67 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨67 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 69632 to 70655 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_68 : ∀ u : Fin 1024,
    if hb : 68 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨68 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 70656 to 71679 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_69 : ∀ u : Fin 1024,
    if hb : 69 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨69 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 71680 to 72703 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_70 : ∀ u : Fin 1024,
    if hb : 70 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨70 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 72704 to 73727 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_71 : ∀ u : Fin 1024,
    if hb : 71 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨71 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
