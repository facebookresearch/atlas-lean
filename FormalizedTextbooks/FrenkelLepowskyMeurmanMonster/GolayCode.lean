/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The binary Golay encoder and its code-weight properties.
Source: Seysen, arXiv:2002.10921v3, §§2 and 6.2.
The bit-mask encoder is proved equal to the linear encoder by induction
on its XOR fold; this transports the kernel-checked finite weight data.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCoordinates
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators


def golayEncoder : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun a i := ∑ j, a j * (golayGeneratorBit j i : ZMod 2)
  map_add' a b := by ext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' k a := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    rw [Finset.mul_sum]

/-- The standard identification of a binary bit with its element of F₂. -/
def golayBooleanCast (b : Bool) : ZMod 2 := if b then 1 else 0

theorem golayBooleanCast_xor (a b : Bool) :
    golayBooleanCast (a ^^ b) = golayBooleanCast a + golayBooleanCast b := by
  cases a <;> cases b <;> decide

theorem golayMaskFold_linear (xs : List (Fin 12)) (d m : ℕ) (i : Fin 24) :
    golayBooleanCast ((xs.foldl (fun n j => n ^^^
      (if d.testBit j.val then golayGeneratorMasks j else 0)) m).testBit i.val) =
      golayBooleanCast (m.testBit i.val) +
        (xs.map (fun j => (if d.testBit j.val then 1 else 0 : ZMod 2) *
          (golayGeneratorBit j i : ZMod 2))).sum := by
  induction xs generalizing m with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_xor, golayBooleanCast_xor,
      List.map_cons, List.sum_cons]
    have h : golayBooleanCast ((if d.testBit a.val then golayGeneratorMasks a else 0).testBit
        i.val) = (if d.testBit a.val then 1 else 0 : ZMod 2) *
          (golayGeneratorBit a i : ZMod 2) := by
      by_cases hd : d.testBit a.val = true
      · simp [hd, golayBooleanCast, golayGeneratorBit]
      · simp [hd, golayBooleanCast]
    rw [h, add_assoc]

theorem golayLabelEncoder_match : ∀ d : Fin 4096, ∀ i : Fin 24,
    (golayEncoder (golayLabelCoefficients d) i).val =
      if (golayEncodedMask d.val).testBit i.val then 1 else 0 := by
  intro d i
  have h := golayMaskFold_linear (List.finRange 12) d.val 0 i
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn] at h
  simp only [Nat.zero_testBit, golayBooleanCast, Bool.false_eq_true, ite_false, zero_add] at h
  change (if (golayEncodedMask d.val).testBit i.val then 1 else 0 : ZMod 2) =
    golayEncoder (golayLabelCoefficients d) i at h
  have hone : (1 : ZMod 2).val = 1 := by decide
  cases hb : (golayEncodedMask d.val).testBit i.val <;>
    simpa [hb, hone] using congrArg ZMod.val h.symm

/-- The binary Golay code, the range of the published twelve-generator encoder. -/
def golayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) := golayEncoder.range

theorem golayCode_weights (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) :
    (∑ i, (c i).val) ∈ ([0, 8, 12, 16, 24] : List ℕ) := by
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.2 a
  rw [← hd]
  have h : (∑ i, (golayEncoder (golayLabelCoefficients d) i).val) =
      golayMaskWeight (golayEncodedMask d.val) := by
    apply Finset.sum_congr rfl
    intro i _
    exact golayLabelEncoder_match d i
  rw [h]
  exact golayEncodedMask_weights d

theorem golayCode_weight_four (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) :
    4 ∣ ∑ i, (c i).val := by
  have h := golayCode_weights c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h <;> rw [h] <;> norm_num

theorem golayCode_weight_ge_eight (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hn : c ≠ 0) : 8 ≤ ∑ i, (c i).val := by
  have hz : (∑ i, (c i).val) ≠ 0 := by
    intro h
    apply hn
    ext i
    change c i = 0
    have hi : (c i).val = 0 := by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (c j).val)
        (Finset.mem_univ i)
      omega
    exact (ZMod.val_eq_zero (c i)).mp hi
  have h := golayCode_weights c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

/-! The published cocode basis is dual to the twelve code generators.
This gives an explicit left inverse of the encoder, without an exhaustive
pairwise search over the 4096 codewords. -/

def golayCocodeBit (j : Fin 12) (i : Fin 24) : ZMod 2 :=
  if (golayCocodeGeneratorMasks j).testBit i.val then 1 else 0

set_option maxHeartbeats 4000000 in
-- Kernel-check the 144 finite code/cocode dot products.
theorem golayBasis_cocode_dual : ∀ j k : Fin 12,
    (∑ i : Fin 24, (golayGeneratorBit j i : ZMod 2) * golayCocodeBit k i) =
      if j = k then 1 else 0 := by
  decide +kernel

def golayDecoder : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) where
  toFun c k := ∑ i, c i * golayCocodeBit k i
  map_add' c d := by ext k; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    rw [Finset.mul_sum]

theorem golayDecoder_encoder (a : Fin 12 → ZMod 2) : golayDecoder (golayEncoder a) = a := by
  ext k
  change (∑ i, (∑ j, a j * (golayGeneratorBit j i : ZMod 2)) * golayCocodeBit k i) = a k
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, golayBasis_cocode_dual]
  simp

theorem golayEncoder_injective : Function.Injective golayEncoder := by
  intro a b h
  have hh := congrArg golayDecoder h
  simpa only [golayDecoder_encoder] using hh

set_option maxRecDepth 10000 in
-- The finite label check traverses 4096 entries.
set_option maxHeartbeats 4000000 in
-- Check the coefficient separating the two complementary halves of the code labels.
theorem golayLabel_last_zero : ∀ d : Fin 4096,
    golayLabelCoefficients d 11 = 0 ↔ d.val < 2048 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Normalize the encoder evaluated on the last coordinate basis vector.
theorem golay_all_one : golayEncoder (Pi.single 11 1) = (fun _ => 1) := by
  ext i
  change (∑ j : Fin 12, ((Pi.single (11 : Fin 12) (1 : ZMod 2) : Fin 12 → ZMod 2) j) *
    (golayGeneratorBit j i : ZMod 2)) = 1
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have hh : ∀ i : Fin 24, (golayGeneratorBit 11 i : ZMod 2) = 1 := by decide +kernel
  exact hh i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
