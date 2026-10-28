/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteSemantics

/-! Exact distant edges and original three-pair hexad lines from the finite mask witnesses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem subset_union (a b c : Nat) :
    (a ||| b) &&& c = a ||| b ↔ a &&& c = a ∧ b &&& c = b := by
  constructor
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq
      intro k
      have hk := congrArg (fun n : Nat => n.testBit k) h
      simp only [Nat.testBit_land, Nat.testBit_lor] at hk ⊢
      cases hta : a.testBit k <;> cases htb : b.testBit k <;>
        cases htc : c.testBit k <;> simp_all
    · apply Nat.eq_of_testBit_eq
      intro k
      have hk := congrArg (fun n : Nat => n.testBit k) h
      simp only [Nat.testBit_land, Nat.testBit_lor] at hk ⊢
      cases hta : a.testBit k <;> cases htb : b.testBit k <;>
        cases htc : c.testBit k <;> simp_all
  · rintro ⟨ha, hb⟩
    apply Nat.eq_of_testBit_eq
    intro k
    have hka := congrArg (fun n : Nat => n.testBit k) ha
    have hkb := congrArg (fun n : Nat => n.testBit k) hb
    simp only [Nat.testBit_land, Nat.testBit_lor] at hka hkb ⊢
    cases hta : a.testBit k <;> cases htb : b.testBit k <;>
        cases htc : c.testBit k <;> simp_all

/-- The finite Boolean predicate is exactly the genuine auxiliary M22 distant relation. -/
theorem co1ResidueM22FiniteDistant_iff (i j : Fin 231) :
    co1ResidueM22FiniteDistant i j = true ↔
      co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint i) (co1ResidueM22FinitePoint j) := by
  rw [co1ResidueM22Distant, co1ResidueM22FinitePoint_disjoint,
    co1ResidueM22FinitePoint_common_hexad]
  simp only [co1ResidueM22FiniteDistant, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true_eq_eq_false, List.any_eq_false, List.mem_finRange,
    forall_const, subset_union]
  simp only [not_exists, not_and]

private theorem mask_support_union (a b : Nat) :
    golayMaskSupport a ∪ golayMaskSupport b = golayMaskSupport (a ||| b) := by
  ext k
  simp only [golayMaskSupport, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, Nat.testBit_lor, Bool.or_eq_true]

/-- A cached three-pair union equal to a genuine cached hexad yields an original source line. -/
theorem co1ResidueM22FiniteLine_of_masks (i j k : Fin 231) (h : Fin 77)
    (he : co1ResidueM22FinitePointMasks i ||| co1ResidueM22FinitePointMasks j |||
      co1ResidueM22FinitePointMasks k = co1ResidueM22FiniteHexadMasks h) :
    co1ResidueM22Line 0 1 (co1ResidueM22FinitePoint i) (co1ResidueM22FinitePoint j)
      (co1ResidueM22FinitePoint k) := by
  refine ⟨(co1ResidueM22FiniteOctad h).val, ?_, ?_, ?_⟩
  · simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_zero] using (co1ResidueM22FiniteOctad h).property.1
  · simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_one] using (co1ResidueM22FiniteOctad h).property.2
  · rw [co1ResidueM22FinitePoint_support, co1ResidueM22FinitePoint_support,
      co1ResidueM22FinitePoint_support, co1ResidueM22FiniteHexad_support,
      mask_support_union, mask_support_union, ← Nat.shiftLeft_or_distrib,
      ← Nat.shiftLeft_or_distrib, he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
