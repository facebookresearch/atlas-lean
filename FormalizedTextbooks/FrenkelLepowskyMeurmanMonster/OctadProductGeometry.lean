/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Physical pairing of two actual signed vectors in one octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Restrict a supported sum to the eight physical coordinates of an octad. -/
theorem golayOctad_sum_supported (o : Fin 759) (f : Fin 24 → ℤ)
    (hf : ∀ i, (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true → f i = 0) :
    (∑ i, f i) = ∑ k : Fin 8, f (golayOctadCoordinate o k) := by
  let S := golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)
  calc
    _ = ∑ i ∈ S, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      apply hf
      simpa only [S, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    _ = _ := by
      symm
      apply Finset.sum_bij (fun k _ => golayOctadCoordinate o k)
      · intro k _
        simp only [S, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact golayOctadCoordinate_mem o k
      · intro k _ l _ h
        exact golayOctadCoordinate_injective o h
      · intro i hi
        let E := (golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)).orderIsoOfFin
          (golayOctad_support_card o)
        obtain ⟨k, hk⟩ := E.toEquiv.surjective ⟨i, hi⟩
        exact ⟨k, Finset.mem_univ k, congrArg Subtype.val hk⟩
      · intro k _
        rfl

/-- Each occupied physical coordinate has the prescribed local sign ±2. -/
theorem griessOctadIntegral_local (o : Fin 759) (e : Fin 64) (k : Fin 8) :
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) (golayOctadCoordinate o k) =
      if (trialityEvenMask e).testBit k.val then (-2 : ℤ) else 2 := by
  simp only [griessShortIntegral, golayOctadCoordinate_mem, ite_true,
    griessOctadSignMask_local]

/-- Pairing is determined by the Hamming distance of the two local even sign masks. -/
theorem griessOctad_same_pairing (o : Fin 759) (e f : Fin 64) :
    leechIntegralPairing (griessShortIntegral (Sum.inr (Sum.inl (o,e))))
      (griessShortIntegral (Sum.inr (Sum.inl (o,f)))) =
        32 - 8 * (trialityBitWeight8 (trialityEvenMask e ^^^ trialityEvenMask f) : ℤ) := by
  unfold leechIntegralPairing
  rw [golayOctad_sum_supported o]
  · simp_rw [griessOctadIntegral_local]
    have hsign : ∀ a b : Bool,
        (if a then (-2 : ℤ) else 2) * (if b then (-2 : ℤ) else 2) =
          4 - 8 * (if a.xor b then (1 : ℤ) else 0) := by decide +kernel
    simp_rw [hsign]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    congr 1
    congr 1
    simp only [trialityBitWeight8, Nat.cast_sum, Nat.cast_ite, Nat.testBit_xor,
      Nat.cast_one, Nat.cast_zero]
  · intro i hi
    simp [griessShortIntegral, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
