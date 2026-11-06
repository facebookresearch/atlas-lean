/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportPacket10Part10Block07

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBoundedQuantifier

/-! Exact full preferred-short Q images and signed coefficients on every nonzero source
in a bounded original row packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_00 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 0 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 0 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_00

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_01 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 1 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 1 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_01

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_02 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 2 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 2 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_02

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_03 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 3 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 3 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_03

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_04 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 4 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 4 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_04

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_05 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 5 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 5 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_05

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_06 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 6 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 6 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_06

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_07 : ∀ u : Fin 1024,
    if h : 10 * 8192 + 7 * 1024 + u.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10
        ⟨10 * 8192 + 7 * 1024 + u.val, h⟩ else True := by
  exact generatedNinth_lower_spin_short_support_packet_10_part_10_block_07

set_option maxHeartbeats 8000000 in
-- Join every bounded block while retaining the complete signed preferred-Q statement.
/-- Every nonzero original source in this bounded packet has its full signed Q image. -/
theorem generatedNinth_lower_spin_short_support_packet_10_part_10 : ∀ a : Fin 8192,
    if h : 10 * 8192 + a.val < 98280 then
      generatedNinthLowerSpinShortSupportCondition 10 ⟨10 * 8192 + a.val, h⟩ else True := by
  have hall : ∀ b : Fin 8, ∀ u : Fin 1024,
      if h : 10 * 8192 + b.val * 1024 + u.val < 98280 then
        generatedNinthLowerSpinShortSupportCondition 10
          ⟨10 * 8192 + b.val * 1024 + u.val, h⟩ else True := by
    intro b u
    fin_cases b
    · simpa only [Nat.add_assoc] using block_00 u
    · simpa only [Nat.add_assoc] using block_01 u
    · simpa only [Nat.add_assoc] using block_02 u
    · simpa only [Nat.add_assoc] using block_03 u
    · simpa only [Nat.add_assoc] using block_04 u
    · simpa only [Nat.add_assoc] using block_05 u
    · simpa only [Nat.add_assoc] using block_06 u
    · simpa only [Nat.add_assoc] using block_07 u
  intro a
  let b : Fin 8 := ⟨a.val / 1024, by omega⟩
  let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hn : b.val * 1024 + u.val = a.val := by
    dsimp [b, u]
    omega
  simpa only [Nat.add_assoc, hn] using hall b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
