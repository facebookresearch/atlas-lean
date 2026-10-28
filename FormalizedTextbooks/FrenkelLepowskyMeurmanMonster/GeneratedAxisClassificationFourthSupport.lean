/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport

/-! Physical support under actual local short-coordinate transport.
This uses the genuine signed short permutation and its genuine preferred-Q
phase; no abstract root system or external dictionary action is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A transported short coefficient is nonzero precisely when the inverse
physical short vector lies in the original octad coordinate plane. -/
theorem generatedFourth_transported_short_support
    (f : localFiberSubgroup) (o : Fin 759) (e : Fin 64) (c : ZMod 2)
    (r : GriessShortIndex) :
    localShortOperator f
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r ≠ 0 ↔
    ∀ i : Fin 24, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false →
      (f⁻¹).val.2.val (griessShortVector r) i = 0 := by
  let s := (griessShortPermutation f.val.2).symm r
  have hp : griessShortPermutation (f⁻¹).val.2 r = s := by
    change griessShortPermutation (f.val.2⁻¹) r = s
    rw [map_inv]
    rfl
  have hq : qSign (localShortPhase f s) ≠ 0 := by
    have h := qSign_sq (localShortPhase f s)
    intro hz
    rw [hz] at h
    norm_num at h
  change qSign (localShortPhase f s) * _ ≠ 0 ↔ _
  rw [mul_ne_zero_iff, and_iff_right hq,
    generatedAxis_triality_octad_support_iff,
    generatedOctadShortSupport_iff_physical]
  rcases griessShortPermutation_vector (f⁻¹).val.2 r with hv | hv
  · rw [hp] at hv
    simp only [hv]
    rfl
  · rw [hp] at hv
    simp only [hv, Pi.neg_apply, neg_eq_zero]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
