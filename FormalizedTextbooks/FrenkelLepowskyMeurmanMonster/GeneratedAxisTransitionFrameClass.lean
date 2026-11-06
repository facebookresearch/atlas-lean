/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderFrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The genuine norm-eight coordinate-frame class in the lattice quotient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private def frameHalfDifference (i : Fin 24) : Fin 24 → ℤ :=
  fun j => 4 * ((Pi.single i 1 : Fin 24 → ℤ) j - (Pi.single 0 1 : Fin 24 → ℤ) j)

private theorem frameHalfDifference_mem (i : Fin 24) :
    frameHalfDifference i ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro j
    simp only [frameHalfDifference, Int.cast_mul, Int.cast_sub, Int.cast_ofNat,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero,
      add_zero, show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ j, frameHalfDifference i j = 0 := by
      simp only [frameHalfDifference, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    rw [hs]
    norm_num

/-- All twenty-four positive frame vectors represent the same actual lattice class. -/
theorem leechFrame_reduction_eq (i : Fin 24) :
    leechReduction (leechCoordinateFrameLattice i) =
      leechReduction (leechCoordinateFrameLattice 0) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨⟨frameHalfDifference i, frameHalfDifference_mem i⟩, ?_⟩
  apply Subtype.ext
  ext j
  simp only [leechDouble, AddMonoidHom.coe_mk, ZeroHom.coe_mk, two_nsmul,
    Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    leechCoordinateFrameLattice, leechCoordinateFrameVector,
    frameHalfDifference, Pi.single_apply]
  split_ifs <;> norm_num

private theorem quotient_neg_eq (v : LeechModTwo) : -v = v := by
  have h : (-1 : ZMod 2) = 1 := by decide
  simpa only [neg_one_smul, one_smul] using congrArg (fun a : ZMod 2 => a • v) h

/-- Either sign of each frame vector represents the same actual lattice class. -/
theorem leechSignedFrame_reduction (t : Fin 24 × ZMod 2) :
    leechReduction (leechSignedFrame t).val =
      leechReduction (leechCoordinateFrameLattice 0) := by
  by_cases ht : t.2 = 0
  · have hv : (leechSignedFrame t).val = leechCoordinateFrameLattice t.1 := by
      apply Subtype.ext
      simp [leechSignedFrame, ht, leechCoordinateFrameLattice]
    rw [hv, leechFrame_reduction_eq]
  · have hv : (leechSignedFrame t).val = -leechCoordinateFrameLattice t.1 := by
      apply Subtype.ext
      simp [leechSignedFrame, ht, leechCoordinateFrameLattice]
    rw [hv, map_neg, quotient_neg_eq, leechFrame_reduction_eq]

/-- The norm-eight vectors in the actual distinguished quotient class are
precisely the forty-eight signed coordinate-frame vectors. -/
theorem leechNormEight_frameClass_eq_signedFrame :
    {u : LeechNormEight | leechReduction u.val =
      leechReduction (leechCoordinateFrameLattice 0)} = Set.range leechSignedFrame := by
  ext u
  constructor
  · intro hu
    have hm : u.val - leechCoordinateFrameLattice 0 ∈ twiceLeechIntegral :=
      QuotientAddGroup.eq_iff_sub_mem.mp hu
    obtain ⟨w, hw⟩ := hm
    have he : u.val.val = fun i => 2 * w.val i + leechCoordinateFrameVector 0 i := by
      ext i
      have hi := congrArg (fun v : leechIntegral => v.val i) hw
      change ((2 : ℕ) • w).val i = (u.val - leechCoordinateFrameLattice 0).val i at hi
      simp only [two_nsmul, Submodule.coe_add, Submodule.coe_sub,
        Pi.add_apply, Pi.sub_apply, leechCoordinateFrameLattice] at hi
      omega
    obtain ⟨i, hi | hi⟩ := leechNormEight_coordinate_frame_class u.val w u.property he
    · refine ⟨(i, 0), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa only [leechSignedFrame, ite_true] using hi.symm
    · refine ⟨(i, 1), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa only [leechSignedFrame, show (1 : ZMod 2) ≠ 0 by decide, ite_false] using hi.symm
  · rintro ⟨t, rfl⟩
    exact leechSignedFrame_reduction t

/-- The actual distinguished norm-eight quotient fiber has forty-eight elements. -/
theorem leechNormEight_frameClass_card :
    Nat.card {u : LeechNormEight // leechReduction u.val =
      leechReduction (leechCoordinateFrameLattice 0)} = 48 := by
  change Nat.card {u : LeechNormEight | leechReduction u.val =
    leechReduction (leechCoordinateFrameLattice 0)} = 48
  rw [leechNormEight_frameClass_eq_signedFrame]
  rw [← Nat.card_congr (Equiv.ofInjective leechSignedFrame leechSignedFrame_injective)]
  norm_num [Nat.card_prod]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
