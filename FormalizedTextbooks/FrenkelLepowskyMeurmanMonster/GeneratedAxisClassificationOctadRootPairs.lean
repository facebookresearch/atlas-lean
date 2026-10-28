/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadRootPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPatternLabels
public import Mathlib.Data.Nat.Bitwise

/-! Transport of the checked 56 decompositions to the original preferred Q lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary addition expressed as ordinary eight-bit exclusive-or. -/
def generatedOctadMaskXor (m n : Fin 256) : Fin 256 :=
  ⟨Nat.xor m.val n.val, by
    simpa using Nat.xor_lt_two_pow (n := 8) m.isLt n.isLt⟩

/-- Eight-bit decoding loses no information. -/
theorem generatedOctadMaskBits_injective : Function.Injective generatedOctadMaskBits := by
  intro m n h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have he := congrArg (fun v => v ⟨j, hj⟩) h
    change (if m.val.testBit j then (1 : ZMod 2) else 0) =
      (if n.val.testBit j then 1 else 0) at he
    have hc : ∀ a b : Bool, (if a then (1 : ZMod 2) else 0) =
        (if b then 1 else 0) → a = b := by decide +kernel
    exact hc _ _ he
  · have hp : 256 ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 8 ≤ j)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m.isLt hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le n.isLt hp)]

/-- Decoding intertwines exclusive-or and binary vector addition. -/
theorem generatedOctadMaskBits_xor (m n : Fin 256) :
    generatedOctadMaskBits (generatedOctadMaskXor m n) =
      generatedOctadMaskBits m + generatedOctadMaskBits n := by
  ext j
  change (if (m.val ^^^ n.val).testBit j.val then (1 : ZMod 2) else 0) =
    (if m.val.testBit j.val then 1 else 0) +
      (if n.val.testBit j.val then 1 else 0)
  simp only [Nat.testBit_xor]
  cases m.val.testBit j.val <;> cases n.val.testBit j.val <;> decide +kernel

/-- A preferred-root addition is exactly its compressed binary addition. -/
theorem generatedOctadPattern_add_iff (r s t : Fin 120) :
    generatedOctadPatternBits r + generatedOctadPatternBits s = generatedOctadPatternBits t ↔
      generatedOctadMaskXor (generatedOctadPatternMask r) (generatedOctadPatternMask s) =
        generatedOctadPatternMask t := by
  rw [← generatedOctadPatternMask_bits r, ← generatedOctadPatternMask_bits s,
    ← generatedOctadPatternMask_bits t, ← generatedOctadMaskBits_xor]
  exact generatedOctadMaskBits_injective.eq_iff

/-- Root patterns are precisely the set bits of the checked compressed root set. -/
noncomputable def generatedOctadRootMaskEquiv : Fin 120 ≃
    {m : Fin 256 // generatedOctadRootMaskSet.testBit m.val = true} :=
  Equiv.ofBijective
    (fun p => ⟨generatedOctadPatternMask p,
      (generatedOctadRootMaskSet_exact _).mpr ⟨p, rfl⟩⟩)
    ⟨fun p q h => generatedOctadPatternMask_injective (congrArg Subtype.val h),
      fun m => by
        obtain ⟨p, hp⟩ := (generatedOctadRootMaskSet_exact m.val).mp m.property
        exact ⟨p, Subtype.ext hp⟩⟩

/-- The inverse root-label equivalence has its specified eight-bit value. -/
theorem generatedOctadRootMaskEquiv_symm_val (m : Fin 256)
    (hm : generatedOctadRootMaskSet.testBit m.val = true) :
    generatedOctadPatternMask (generatedOctadRootMaskEquiv.symm ⟨m, hm⟩) = m :=
  congrArg Subtype.val (generatedOctadRootMaskEquiv.apply_symm_apply ⟨m, hm⟩)

/-- Cancelling a fixed eight-bit addend twice gives the original label. -/
theorem generatedOctadMaskXor_cancel (m n : Fin 256) :
    generatedOctadMaskXor m (generatedOctadMaskXor m n) = n := by
  apply Fin.ext
  exact Nat.xor_xor_cancel_left _ _

/-- Ordered root decompositions are the checked compressed-label filter. -/
noncomputable def generatedOctadRootPairEquiv (t : Fin 120) :
    {rs : Fin 120 × Fin 120 // generatedOctadPatternBits rs.1 +
      generatedOctadPatternBits rs.2 = generatedOctadPatternBits t} ≃
    {m : Fin 256 // generatedOctadRootMaskSet.testBit m.val = true ∧
      generatedOctadRootMaskSet.testBit
        (generatedOctadMaskXor m (generatedOctadPatternMask t)).val = true} where
  toFun rs := by
    have he := (generatedOctadPattern_add_iff _ _ _).mp rs.property
    have hs : generatedOctadMaskXor (generatedOctadPatternMask rs.val.1)
        (generatedOctadPatternMask t) = generatedOctadPatternMask rs.val.2 := by
      rw [← he, generatedOctadMaskXor_cancel]
    refine ⟨generatedOctadPatternMask rs.val.1, ?_, ?_⟩
    · exact (generatedOctadRootMaskSet_exact _).mpr ⟨rs.val.1, rfl⟩
    · rw [hs]
      exact (generatedOctadRootMaskSet_exact _).mpr ⟨rs.val.2, rfl⟩
  invFun m := by
    let r := generatedOctadRootMaskEquiv.symm ⟨m.val, m.property.1⟩
    let s := generatedOctadRootMaskEquiv.symm
      ⟨generatedOctadMaskXor m.val (generatedOctadPatternMask t), m.property.2⟩
    have hr : generatedOctadPatternMask r = m.val :=
      congrArg Subtype.val (generatedOctadRootMaskEquiv.apply_symm_apply _)
    have hs : generatedOctadPatternMask s =
        generatedOctadMaskXor m.val (generatedOctadPatternMask t) :=
      congrArg Subtype.val (generatedOctadRootMaskEquiv.apply_symm_apply _)
    refine ⟨(r, s), (generatedOctadPattern_add_iff _ _ _).mpr ?_⟩
    rw [hr, hs, generatedOctadMaskXor_cancel]
  left_inv rs := by
    apply Subtype.ext
    apply Prod.ext
    · exact generatedOctadRootMaskEquiv.symm_apply_apply rs.val.1
    · apply generatedOctadPatternMask_injective
      change generatedOctadPatternMask (generatedOctadRootMaskEquiv.symm _) = _
      rw [generatedOctadRootMaskEquiv_symm_val]
      change generatedOctadMaskXor (generatedOctadPatternMask rs.val.1)
        (generatedOctadPatternMask t) = generatedOctadPatternMask rs.val.2
      have he := (generatedOctadPattern_add_iff _ _ _).mp rs.property
      exact (congrArg (generatedOctadMaskXor (generatedOctadPatternMask rs.val.1))
        he.symm).trans (generatedOctadMaskXor_cancel _ _)
  right_inv m := by
    apply Subtype.ext
    change generatedOctadPatternMask
      (generatedOctadRootMaskEquiv.symm ⟨m.val, m.property.1⟩) = m.val
    exact congrArg Subtype.val (generatedOctadRootMaskEquiv.apply_symm_apply
      ⟨m.val, m.property.1⟩)

/-- Exactly 56 ordered pairs of actual finite root patterns add to each root. -/
theorem generatedOctadRootPairs_card (t : Fin 120) :
    Nat.card {rs : Fin 120 × Fin 120 // generatedOctadPatternBits rs.1 +
      generatedOctadPatternBits rs.2 = generatedOctadPatternBits t} = 56 := by
  classical
  rw [Nat.card_congr (generatedOctadRootPairEquiv t), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simpa only [generatedOctadMaskXor] using generatedOctadRootMaskSet_pair_count t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
