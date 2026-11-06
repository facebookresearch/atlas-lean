/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightData

/-! Address packets 72 to 95 of the orthogonality check for the positive final
Root8 axis. Each packet checks 1024 short addresses: the packed short numerator is below 48 in
absolute value, or both signed axes are tested exactly against the matrix numerator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
-- Addresses 73728 to 74751 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_72 : ∀ u : Fin 1024,
    if hb : 72 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨72 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 74752 to 75775 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_73 : ∀ u : Fin 1024,
    if hb : 73 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨73 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 75776 to 76799 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_74 : ∀ u : Fin 1024,
    if hb : 74 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨74 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 76800 to 77823 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_75 : ∀ u : Fin 1024,
    if hb : 75 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨75 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 77824 to 78847 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_76 : ∀ u : Fin 1024,
    if hb : 76 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨76 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 78848 to 79871 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_77 : ∀ u : Fin 1024,
    if hb : 77 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨77 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 79872 to 80895 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_78 : ∀ u : Fin 1024,
    if hb : 78 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨78 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 80896 to 81919 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_79 : ∀ u : Fin 1024,
    if hb : 79 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨79 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 81920 to 82943 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_80 : ∀ u : Fin 1024,
    if hb : 80 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨80 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 82944 to 83967 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_81 : ∀ u : Fin 1024,
    if hb : 81 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨81 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 83968 to 84991 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_82 : ∀ u : Fin 1024,
    if hb : 82 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨82 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 84992 to 86015 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_83 : ∀ u : Fin 1024,
    if hb : 83 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨83 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 86016 to 87039 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_84 : ∀ u : Fin 1024,
    if hb : 84 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨84 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 87040 to 88063 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_85 : ∀ u : Fin 1024,
    if hb : 85 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨85 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 88064 to 89087 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_86 : ∀ u : Fin 1024,
    if hb : 86 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨86 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 89088 to 90111 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_87 : ∀ u : Fin 1024,
    if hb : 87 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨87 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 90112 to 91135 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_88 : ∀ u : Fin 1024,
    if hb : 88 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨88 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 91136 to 92159 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_89 : ∀ u : Fin 1024,
    if hb : 89 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨89 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 92160 to 93183 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_90 : ∀ u : Fin 1024,
    if hb : 90 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨90 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 93184 to 94207 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_91 : ∀ u : Fin 1024,
    if hb : 91 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨91 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 94208 to 95231 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_92 : ∀ u : Fin 1024,
    if hb : 92 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨92 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 95232 to 96255 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_93 : ∀ u : Fin 1024,
    if hb : 93 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨93 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 96256 to 97279 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_94 : ∀ u : Fin 1024,
    if hb : 94 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨94 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Addresses 97280 to 98303 are checked.
theorem generatedFeasibleAmbient_rootEight_packet_95 : ∀ u : Fin 1024,
    if hb : 95 * 1024 + u.val < 98280 then
      generatedFeasibleAmbientRootEightCheck
        (generatedNinthLowerSpinShortIndex ⟨95 * 1024 + u.val, hb⟩)
    else True := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
