/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairScalarCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOddMasks

/-! Sparse short addresses retain genuine catalogue indices, preferred Q lifts and signed values. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine sparse addresses for all three original short support families. -/
abbrev GeneratedSixthXiShortAddress :=
  Fin 552 ⊕ ((Fin 231 × Fin 64) ⊕ (Fin 512 × Fin 24))

/-- Sparse addresses resolve through already certified actual short catalogue labels. -/
def generatedSixthXiShortAddressIndex : GeneratedSixthXiShortAddress → GriessShortIndex
  | Sum.inl j => generatedSixthXiPairInput j
  | Sum.inr (Sum.inl (f, e)) => Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))
  | Sum.inr (Sum.inr (f, j)) => Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j))

/-- Exact preferred-Q masks use original physical pairs and genuine octad and odd caches. -/
def generatedSixthXiShortAddressMask : GeneratedSixthXiShortAddress → ℕ
  | Sum.inl j =>
    let x := generatedSixthXiPairSourceCoordinates j
    generatedSixthXiJoinMasks (nortonUIntegerLabel (if x.1 = 0 then 0 else Pi.single 11 1))
      (Nat.xor (generatedSixthXiSyndromeColumns x.2.1)
        (generatedSixthXiSyndromeColumns x.2.2))
  | Sum.inr (Sum.inl (f, e)) => generatedSixthXiOctadMask f e
  | Sum.inr (Sum.inr (f, j)) => generatedSixthXiOddMask f j

/-- Every displayed sparse mask is the complete genuine preferred Q lift. -/
theorem generatedSixth_xi_short_address_Q (x : GeneratedSixthXiShortAddress) :
    griessShortQ (generatedSixthXiShortAddressIndex x) =
      generatedSixthXiMaskQ (generatedSixthXiShortAddressMask x) := by
  rcases x with j | (⟨f, e⟩ | ⟨f, j⟩)
  · have ho := generatedSixth_xi_pair_source_ordered j
    have hn := ne_of_lt ho
    rw [generatedSixthXiShortAddressIndex, generatedSixthXiPairInput,
      generatedSixthXiPairShort, dite_eq_left hn, generatedSixth_xi_pair_mask_Q]
    simp only [generatedSixthXiPairMask, griessPairIndex_coordinates, ho, ite_true,
      generatedSixthXiShortAddressMask]
  · exact generatedSixth_xi_octad_mask_Q f e
  · exact generatedSixth_xi_odd_mask_Q f j

/-- Compact signed numerators remain the exact original coefficients multiplied by 32. -/
def generatedSixthXiShortAddressNumerator : GeneratedSixthXiShortAddress → ℤ
  | Sum.inl j => generatedSixthXiPairScalarInputNumerator j
  | Sum.inr (Sum.inl (f, e)) => generatedSixthFinalOctadCachedNumerator f e
  | Sum.inr (Sum.inr (f, j)) => generatedSixthFinalOddNumerator (generatedSixthMonomialOddCode f) j

/-- Each compact signed value equals the complete original short coefficient numerator. -/
theorem generatedSixth_xi_short_address_numerator (x : GeneratedSixthXiShortAddress) :
    generatedSixthFinalShortNumerator (generatedSixthXiShortAddressIndex x) =
      generatedSixthXiShortAddressNumerator x := by
  rcases x with j | (⟨f, e⟩ | ⟨f, j⟩)
  · exact (generatedSixth_xi_pair_input_numerator j).trans
      (generatedSixth_xi_pair_scalar_input_numerator j).symm
  · simp only [generatedSixthXiShortAddressIndex, generatedSixthXiShortAddressNumerator,
      generatedSixthFinalShortNumerator, generatedSixth_final_octad_cache_label]
    exact (generatedSixth_final_octad_cached_numerator f e).symm
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
