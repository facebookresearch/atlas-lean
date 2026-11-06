/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Bitwise
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FinitePoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteHexads
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22Nearby

/-! Exact original Golay hexad semantics of the cached distant-pair predicate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem pair_mask_support : ∀ i : Fin 231,
    ({(co1ResidueM22FinitePairs i).1, (co1ResidueM22FinitePairs i).2} : Finset (Fin 24)) =
      golayMaskSupport (co1ResidueM22FinitePointMasks i <<< 2) := by
  decide +kernel

private theorem hexad_mask_membership : ∀ (h : Fin 77) (k : Fin 24),
    (k ≠ 1 ∧ k ≠ 0 ∧
      (golayEncodedMask (co1ResidueM22FiniteHexadCodes h).val).testBit k.val = true) ↔
      (co1ResidueM22FiniteHexadMasks h <<< 2).testBit k.val = true := by
  decide +kernel

/-- The cached two-bit mask has exactly the support of its actual pair point. -/
theorem co1ResidueM22FinitePoint_support (i : Fin 231) :
    (co1ResidueM22FinitePoint i).val =
      golayMaskSupport (co1ResidueM22FinitePointMasks i <<< 2) := pair_mask_support i

/-- The cached shifted hexad mask has exactly the support of its actual original octad hexad. -/
theorem co1ResidueM22FiniteHexad_support (h : Fin 77) :
    co1ResidueM22Hexad 0 1 (co1ResidueM22FiniteOctad h).val =
      golayMaskSupport (co1ResidueM22FiniteHexadMasks h <<< 2) := by
  ext k
  simp only [co1ResidueM22Hexad, Finset.mem_erase, golayOctadSupport,
    co1ResidueM22FiniteOctad_label, golayMaskSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hexad_mask_membership h k

private theorem support_subset (a b : Nat) (ha : a < 2 ^ 24) :
    golayMaskSupport a ⊆ golayMaskSupport b ↔ a &&& b = a := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_land]
    by_cases hk : k < 24
    · have hh := @h ⟨k,hk⟩
      simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hh
      cases hta : a.testBit k <;> cases htb : b.testBit k <;> simp_all
    · have ha0 : a.testBit k = false := Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [ha0, Bool.false_and]
  · intro h k hk
    have ht := congrArg (fun n : Nat => n.testBit k.val) h
    simp only [Nat.testBit_land] at ht
    simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [hk, Bool.true_and] at ht
    exact ht
private theorem support_disjoint (a b : Nat) (ha : a < 2 ^ 24) :
    Disjoint (golayMaskSupport a) (golayMaskSupport b) ↔ a &&& b = 0 := by
  rw [Finset.disjoint_left]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_land, Nat.zero_testBit]
    by_cases hk : k < 24
    · have hh := @h ⟨k,hk⟩
      simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hh
      cases hta : a.testBit k <;> cases htb : b.testBit k <;> simp_all
    · have ha0 : a.testBit k = false := Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp only [ha0, Bool.false_and]
  · intro h k hk hl
    have ht := congrArg (fun n : Nat => n.testBit k.val) h
    simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
    simp only [Nat.testBit_land, Nat.zero_testBit, hk, hl, Bool.true_and] at ht
    exact Bool.noConfusion ht

private theorem point_masks_bound : ∀ i : Fin 231,
    co1ResidueM22FinitePointMasks i <<< 2 < 2 ^ 24 := by
  decide +kernel

private theorem point_subset_mask : ∀ (i : Fin 231) (h : Fin 77),
    golayMaskSupport (co1ResidueM22FinitePointMasks i <<< 2) ⊆
      golayMaskSupport (co1ResidueM22FiniteHexadMasks h <<< 2) ↔
      co1ResidueM22FinitePointMasks i &&& co1ResidueM22FiniteHexadMasks h =
        co1ResidueM22FinitePointMasks i := by
  intro i h
  rw [support_subset _ _ (point_masks_bound i), ← Nat.shiftLeft_and_distrib]
  simp [Nat.shiftLeft_eq]

private theorem points_disjoint_mask : ∀ (i j : Fin 231),
    Disjoint (golayMaskSupport (co1ResidueM22FinitePointMasks i <<< 2))
      (golayMaskSupport (co1ResidueM22FinitePointMasks j <<< 2)) ↔
      co1ResidueM22FinitePointMasks i &&& co1ResidueM22FinitePointMasks j = 0 := by
  intro i j
  rw [support_disjoint _ _ (point_masks_bound i), ← Nat.shiftLeft_and_distrib]
  exact Nat.shiftLeft_eq_zero_iff

/-- Actual containment of a pair point in an original hexad is the cached subset test. -/
theorem co1ResidueM22FinitePoint_subset_hexad (i : Fin 231) (h : Fin 77) :
    (co1ResidueM22FinitePoint i).val ⊆
      co1ResidueM22Hexad 0 1 (co1ResidueM22FiniteOctad h).val ↔
      co1ResidueM22FinitePointMasks i &&& co1ResidueM22FiniteHexadMasks h =
        co1ResidueM22FinitePointMasks i := by
  rw [co1ResidueM22FinitePoint_support, co1ResidueM22FiniteHexad_support]
  exact point_subset_mask i h

/-- Disjointness of actual pair points is precisely their cached bit test. -/
theorem co1ResidueM22FinitePoint_disjoint (i j : Fin 231) :
    Disjoint (co1ResidueM22FinitePoint i).val (co1ResidueM22FinitePoint j).val ↔
      co1ResidueM22FinitePointMasks i &&& co1ResidueM22FinitePointMasks j = 0 := by
  rw [co1ResidueM22FinitePoint_support, co1ResidueM22FinitePoint_support]
  exact points_disjoint_mask i j

/-- Sharing a genuine Golay hexad is exactly the existential cached containment condition. -/
theorem co1ResidueM22FinitePoint_common_hexad (i j : Fin 231) :
    co1ResidueM22CommonHexad 0 1 (co1ResidueM22FinitePoint i)
      (co1ResidueM22FinitePoint j) ↔
      ∃ h : Fin 77,
        co1ResidueM22FinitePointMasks i &&& co1ResidueM22FiniteHexadMasks h =
          co1ResidueM22FinitePointMasks i ∧
        co1ResidueM22FinitePointMasks j &&& co1ResidueM22FiniteHexadMasks h =
          co1ResidueM22FinitePointMasks j := by
  constructor
  · rintro ⟨o, h0, h1, hi, hj⟩
    have ho : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true ∧
        (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true := by
      simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one] using And.intro h0 h1
    obtain ⟨h, hh⟩ := co1ResidueM22FiniteOctadEquiv.surjective ⟨o, ho⟩
    have hv : (co1ResidueM22FiniteOctad h).val = o := congrArg Subtype.val hh
    refine ⟨h, (co1ResidueM22FinitePoint_subset_hexad i h).mp ?_,
      (co1ResidueM22FinitePoint_subset_hexad j h).mp ?_⟩
    · rwa [hv]
    · rwa [hv]
  · rintro ⟨h, hi, hj⟩
    refine ⟨(co1ResidueM22FiniteOctad h).val, ?_, ?_,
      (co1ResidueM22FinitePoint_subset_hexad i h).mpr hi,
      (co1ResidueM22FinitePoint_subset_hexad j h).mpr hj⟩
    · simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one] using
        (co1ResidueM22FiniteOctad h).property.1
    · simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
        Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one] using
        (co1ResidueM22FiniteOctad h).property.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
