/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightData

/-! Address packets 24 to 47 of the orthogonality check for the positive final
Root8 axis. Each packet checks 1024 short addresses: the packed short numerator is below 48 in
absolute value, or both signed axes are tested exactly against the matrix numerator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Addresses 24576 to 25599 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_24 : ∀ u : Fin 1024,
    if hb : 24 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨24 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 25600 to 26623 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_25 : ∀ u : Fin 1024,
    if hb : 25 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨25 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 26624 to 27647 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_26 : ∀ u : Fin 1024,
    if hb : 26 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨26 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 27648 to 28671 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_27 : ∀ u : Fin 1024,
    if hb : 27 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨27 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 28672 to 29695 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_28 : ∀ u : Fin 1024,
    if hb : 28 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨28 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 29696 to 30719 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_29 : ∀ u : Fin 1024,
    if hb : 29 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨29 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 30720 to 31743 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_30 : ∀ u : Fin 1024,
    if hb : 30 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨30 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 31744 to 32767 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_31 : ∀ u : Fin 1024,
    if hb : 31 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨31 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 32768 to 33791 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_32 : ∀ u : Fin 1024,
    if hb : 32 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨32 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 33792 to 34815 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_33 : ∀ u : Fin 1024,
    if hb : 33 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨33 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 34816 to 35839 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_34 : ∀ u : Fin 1024,
    if hb : 34 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨34 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 35840 to 36863 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_35 : ∀ u : Fin 1024,
    if hb : 35 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨35 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 36864 to 37887 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_36 : ∀ u : Fin 1024,
    if hb : 36 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨36 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 37888 to 38911 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_37 : ∀ u : Fin 1024,
    if hb : 37 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨37 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 38912 to 39935 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_38 : ∀ u : Fin 1024,
    if hb : 38 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨38 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 39936 to 40959 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_39 : ∀ u : Fin 1024,
    if hb : 39 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨39 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 40960 to 41983 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_40 : ∀ u : Fin 1024,
    if hb : 40 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨40 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 41984 to 43007 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_41 : ∀ u : Fin 1024,
    if hb : 41 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨41 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 43008 to 44031 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_42 : ∀ u : Fin 1024,
    if hb : 42 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨42 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 44032 to 45055 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_43 : ∀ u : Fin 1024,
    if hb : 43 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨43 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 45056 to 46079 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_44 : ∀ u : Fin 1024,
    if hb : 44 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨44 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 46080 to 47103 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_45 : ∀ u : Fin 1024,
    if hb : 45 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨45 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 47104 to 48127 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_46 : ∀ u : Fin 1024,
    if hb : 46 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨46 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 48128 to 49151 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_47 : ∀ u : Fin 1024,
    if hb : 47 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨47 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
