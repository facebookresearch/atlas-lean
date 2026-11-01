/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixActualPairTransport

/-! Genuine integral flags and their norm-four points in the original Leech lattice. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The actual canonical norm-four root, with its two original signs. -/
def leechNormSixHS100RootIntegral (i : Fin 24) : ℤ :=
  if i = 0 then 4 else if i = 1 then -4 else 0

/-- The actual canonical norm-six companion, with all twenty-four coordinates retained. -/
def leechNormSixHS100CompanionIntegral (i : Fin 24) : ℤ :=
  if i = 0 then 5 else 1

/-- The complete norm-four root satisfies the original Leech congruences. -/
theorem leechNormSixHS100RootIntegral_mem : leechNormSixHS100RootIntegral ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, ⟨0, map_zero golayEncoder⟩, ?_, ?_⟩
  · intro i
    by_cases h0 : i = 0
    · norm_num [leechNormSixHS100RootIntegral, h0]
      decide
    · by_cases h1 : i = 1 <;> norm_num [leechNormSixHS100RootIntegral, h0, h1]
      decide
  · norm_num [leechNormSixHS100RootIntegral, Fin.sum_univ_succ]

/-- The complete norm-six companion satisfies the original Leech congruences. -/
theorem leechNormSixHS100CompanionIntegral_mem :
    leechNormSixHS100CompanionIntegral ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨1, Or.inr rfl, 0, ⟨0, map_zero golayEncoder⟩, ?_, ?_⟩
  · intro i
    by_cases h0 : i = 0 <;> norm_num [leechNormSixHS100CompanionIntegral, h0]
    decide
  · norm_num [leechNormSixHS100CompanionIntegral, Fin.sum_univ_succ]
    decide

/-- The genuine canonical norm-four lattice vector. -/
def leechNormSixHS100Root : leechIntegral :=
  ⟨leechNormSixHS100RootIntegral, leechNormSixHS100RootIntegral_mem⟩

/-- The genuine canonical norm-six lattice vector. -/
def leechNormSixHS100Companion : leechIntegral :=
  ⟨leechNormSixHS100CompanionIntegral, leechNormSixHS100CompanionIntegral_mem⟩

/-- The canonical root has actual integer square sum thirty-two. -/
theorem leechNormSixHS100Root_square : leechSquareSum leechNormSixHS100Root.val = 32 := by
  norm_num [leechNormSixHS100Root, leechNormSixHS100RootIntegral,
    leechSquareSum, Fin.sum_univ_succ]

/-- The canonical companion has actual integer square sum forty-eight. -/
theorem leechNormSixHS100Companion_square :
    leechSquareSum leechNormSixHS100Companion.val = 48 := by
  norm_num [leechNormSixHS100Companion, leechNormSixHS100CompanionIntegral,
    leechSquareSum, Fin.sum_univ_succ]

/-- The two complete canonical lattice vectors have their actual integer pairing sixteen. -/
theorem leechNormSixHS100Flag_pairing :
    leechIntegralPairing leechNormSixHS100Root.val leechNormSixHS100Companion.val = 16 := by
  norm_num [leechNormSixHS100Root, leechNormSixHS100Companion,
    leechNormSixHS100RootIntegral, leechNormSixHS100CompanionIntegral,
    leechIntegralPairing, Fin.sum_univ_succ]

/-- The original physical point conditions for a genuine ordered lattice flag. -/
def LeechNormSixHS100PointCondition (x y z : leechIntegral) : Prop :=
  leechSquareSum z.val = 32 ∧ leechIntegralPairing x.val z.val = 0 ∧
    leechIntegralPairing y.val z.val = 24

/-- Actual norm-four lattice vectors with the original two prescribed flag pairings. -/
def LeechNormSixHS100Points (x y : leechIntegral) : Type :=
  {z : leechIntegral // LeechNormSixHS100PointCondition x y z}

/-- Pairing with the actual signed root uses precisely the two original coordinates. -/
theorem leechNormSixHS100Root_pairing (z : leechIntegral) :
    leechIntegralPairing leechNormSixHS100Root.val z.val = 4 * (z.val 0 - z.val 1) := by
  norm_num [leechNormSixHS100Root, leechNormSixHS100RootIntegral,
    leechIntegralPairing, Fin.sum_univ_succ]
  ring

/-- Pairing with the actual companion retains every coordinate, including its high coordinate. -/
theorem leechNormSixHS100Companion_pairing (z : leechIntegral) :
    leechIntegralPairing leechNormSixHS100Companion.val z.val =
      4 * z.val 0 + ∑ i, z.val i := by
  simp only [leechNormSixHS100Companion, leechNormSixHS100CompanionIntegral,
    leechIntegralPairing, Fin.sum_univ_succ]
  norm_num
  ring

/-- The complete original point conditions have their exact canonical coordinate form. -/
theorem leechNormSixHS100PointCondition_coordinates (z : leechIntegral) :
    LeechNormSixHS100PointCondition leechNormSixHS100Root leechNormSixHS100Companion z ↔
      leechSquareSum z.val = 32 ∧ z.val 0 = z.val 1 ∧ 4 * z.val 0 + ∑ i, z.val i = 24 := by
  rw [LeechNormSixHS100PointCondition, leechNormSixHS100Root_pairing,
    leechNormSixHS100Companion_pairing]
  constructor
  · rintro ⟨hn, hp, hy⟩
    exact ⟨hn, by omega, hy⟩
  · rintro ⟨hn, hp, hy⟩
    exact ⟨hn, by rw [hp]; ring, hy⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
