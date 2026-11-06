/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Finite Golay code data checked against the published MOG generator table.
Source: Seysen, arXiv:2002.10921v3, §§2 and 6.2; the masks are published in
mmgroup `golay_basis_data.inc`, commit 728688938a1c9fd27f3aee9b63464ea6b8d17965.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBasisData
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Encode twelve binary Golay coefficients using the published generator masks. -/
def golayEncodedMask (d : ℕ) : ℕ :=
  (List.finRange 12).foldl (fun m j => m ^^^
    (if d.testBit j.val then golayGeneratorMasks j else 0)) 0

/-- The binary coefficients represented by a twelve-bit code label. -/
def golayLabelCoefficients (d : Fin 4096) : Fin 12 → ZMod 2 :=
  fun j => if d.val.testBit j.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Reassembling all 4096 coefficient labels certifies the finite encoding.
theorem golayLabelCoefficients_reassemble : ∀ d : Fin 4096,
    (∑ j, (golayLabelCoefficients d j).val * 2 ^ j.val) = d.val := by
  decide +kernel

theorem golayLabelCoefficients_injective : Function.Injective golayLabelCoefficients := by
  intro d e h
  apply Fin.ext
  rw [← golayLabelCoefficients_reassemble d, ← golayLabelCoefficients_reassemble e, h]

/-- Every binary coefficient vector has a unique twelve-bit code label. -/
theorem golayLabelCoefficients_bijective : Function.Bijective golayLabelCoefficients := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨golayLabelCoefficients_injective, by simp⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The five possible weights are checked on all 4096 binary code labels.
theorem golayEncodedMask_weights : ∀ d : Fin 4096,
    golayMaskWeight (golayEncodedMask d.val) ∈ ([0, 8, 12, 16, 24] : List ℕ) := by
  decide +kernel

/-- The 759 octads, indexed by the increasing order of their twelve-bit code labels. -/
def golayOctads : Finset (Fin 4096) :=
  Finset.univ.filter (fun d => golayMaskWeight (golayEncodedMask d.val) = 8)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Enumerating 4096 codewords checks the octad count directly from the published generators.
theorem golayOctads_card : golayOctads.card = 759 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
