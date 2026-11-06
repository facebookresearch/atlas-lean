/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSourceMasks

/-! Sparse physical masks and their exact original Golay cocode images. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem physical_or_bits {ι : Type*} (xs : List ι) (f : ι → ℕ) (i : ℕ) :
    (xs.foldr (fun x m => f x ||| m) 0).testBit i =
      xs.any (fun x => (f x).testBit i) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]

/-- A physical mask selected from eight distinct actual coordinate positions. -/
def generatedAxisGlobalSparsePhysicalMask (c : Fin 8 → Fin 24) (m : ℕ) : ℕ :=
  (List.finRange 8).foldr (fun k z => (if m.testBit k.val then 2 ^ (c k).val else 0) ||| z) 0

/-- Distinct physical coordinate powers have exactly their selected original binary vector. -/
theorem generatedAxisGlobalSparsePhysicalMask_decode (c : Fin 8 → Fin 24)
    (hc : Function.Injective c) (m : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalSparsePhysicalMask c m) =
      ∑ k : Fin 8, (if m.testBit k.val then (1 : ZMod 2) else 0) • Pi.single (c k) 1 := by
  funext i
  have hbits : (generatedAxisGlobalSparsePhysicalMask c m).testBit i.val = true ↔
      ∃ k : Fin 8, m.testBit k.val = true ∧ c k = i := by
    rw [generatedAxisGlobalSparsePhysicalMask, physical_or_bits, List.any_eq_true]
    constructor
    · rintro ⟨k, _, h⟩
      cases hb : m.testBit k.val
      · simp [hb] at h
      · simp only [hb, ↓reduceIte, Nat.testBit_two_pow,
          decide_eq_true_eq] at h
        exact ⟨k, hb, Fin.ext h⟩
    · rintro ⟨k, hb, hk⟩
      refine ⟨k, List.mem_finRange k, ?_⟩
      simp [hb, hk]
  by_cases h : ∃ k : Fin 8, m.testBit k.val = true ∧ c k = i
  · obtain ⟨k, hk, hki⟩ := h
    have hb := hbits.mpr ⟨k, hk, hki⟩
    simp only [monsterCo1GeometryBinaryMaskDecode, hb, ↓reduceIte, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp [hk, hki]
    · intro j _ hj
      have hji : c j ≠ i := fun he => hj (hc (he.trans hki.symm))
      simp [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hji)]
    · simp
  · have hb : (generatedAxisGlobalSparsePhysicalMask c m).testBit i.val = false := by
      cases hval : (generatedAxisGlobalSparsePhysicalMask c m).testBit i.val
      · rfl
      · exact False.elim (h (hbits.mp hval))
    simp only [monsterCo1GeometryBinaryMaskDecode, hb, Finset.sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : m.testBit k.val = true
    · have hki : c k ≠ i := fun he => h ⟨k, hk, he⟩
      simp [hk, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hki)]
    · simp [hk]

/-- Sparse cocode evaluation uses only the eight selected original generator columns. -/
def generatedAxisGlobalSparseCocodeMask (c : Fin 8 → Fin 24) (m : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun k : Fin 8 =>
    if m.testBit k.val then generatedAxisGlobalCocodeColumnMask (c k) else 0))

/-- Sparse cocode evaluation is exactly the syndrome of the original physical mask. -/
theorem generatedAxisGlobalSparseCocodeMask_decode (c : Fin 8 → Fin 24)
    (hc : Function.Injective c) (m : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalSparseCocodeMask c m) =
      golaySyndrome (monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedAxisGlobalSparsePhysicalMask c m)) := by
  rw [generatedAxisGlobalSparsePhysicalMask_decode c hc]
  simp only [map_sum, map_smul]
  unfold generatedAxisGlobalSparseCocodeMask
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  cases hb : m.testBit k.val
  · simp [hb, monsterCo1GeometryBinaryMaskDecode_zero]
  · simp only [Function.comp_apply, hb, ↓reduceIte,
      generatedAxisGlobalCocodeColumnMask_decode, one_smul]
    funext j
    change (golayGeneratorBit j (c k) : ZMod 2) =
      ∑ i : Fin 24, (Pi.single (c k) 1 : Fin 24 → ZMod 2) i * (golayGeneratorBit j i : ZMod 2)
    simp [Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
