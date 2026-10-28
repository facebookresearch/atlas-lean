/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadRootPairs

/-! The 56 ordered decompositions are decompositions of actual preferred Q lifts,
with both factors in the actual nonzero short-coordinate support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The original Q product-base relation is the checked binary root addition. -/
theorem generatedOctadPatternLabel_product_iff (r s t : Fin 120) :
    (griessShortQ (generatedOctadPatternLabel r) *
      griessShortQ (generatedOctadPatternLabel s)).base =
        (griessShortQ (generatedOctadPatternLabel t)).base ↔
      generatedOctadPatternBits r + generatedOctadPatternBits s =
        generatedOctadPatternBits t := by
  have he : ∀ q q' : Q, q.base = q'.base ↔ toAdd q.base = toAdd q'.base := by
    intro q q'
    exact toAdd.injective.eq_iff.symm
  rw [he]
  change toAdd (griessShortQ (generatedOctadPatternLabel r)).base +
      toAdd (griessShortQ (generatedOctadPatternLabel s)).base =
      toAdd (griessShortQ (generatedOctadPatternLabel t)).base ↔ _
  rw [generatedOctadPatternLabel_base, generatedOctadPatternLabel_base,
    generatedOctadPatternLabel_base]
  change generatedOctadBasisBinaryMatrix.mulVecLin (generatedOctadPatternBits r) +
      generatedOctadBasisBinaryMatrix.mulVecLin (generatedOctadPatternBits s) =
      generatedOctadBasisBinaryMatrix.mulVecLin (generatedOctadPatternBits t) ↔ _
  rw [← map_add]
  exact generatedOctadBasis_binary_injective.eq_iff

/-- Transport the finite root decompositions to the actual supported labels. -/
noncomputable def generatedOctadActualRootPairEquiv (t : Fin 120) :
    {rs : Fin 120 × Fin 120 // generatedOctadPatternBits rs.1 +
      generatedOctadPatternBits rs.2 = generatedOctadPatternBits t} ≃
    {rs : {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} ×
        {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} //
      (griessShortQ rs.1.val * griessShortQ rs.2.val).base =
        (griessShortQ (generatedOctadPatternLabel t)).base} :=
  Equiv.subtypeEquiv (generatedOctadPatternEquiv.prodCongr generatedOctadPatternEquiv)
    (fun rs => (generatedOctadPatternLabel_product_iff rs.1 rs.2 t).symm)

/-- Exactly 56 ordered actual supported root pairs have a specified supported product base. -/
theorem generatedOctadActualRootPairs_card
    (u : GriessShortIndex) (hu : generatedOctadShortSupport generatedOctadBasisOctad u) :
    Nat.card {rs : {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} ×
        {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} //
      (griessShortQ rs.1.val * griessShortQ rs.2.val).base = (griessShortQ u).base} = 56 := by
  obtain ⟨t, ht⟩ := generatedOctadPatternEquiv.surjective ⟨u, hu⟩
  have ht' : generatedOctadPatternLabel t = u := congrArg Subtype.val ht
  rw [← ht', ← Nat.card_congr (generatedOctadActualRootPairEquiv t),
    generatedOctadRootPairs_card]

/-- The ordered-pair subtype used by actual convolution is the same actual root-pair set. -/
noncomputable def generatedOctadActualRootPairFilterEquiv (u : GriessShortIndex) :
    {rs : GriessShortIndex × GriessShortIndex //
      generatedOctadShortSupport generatedOctadBasisOctad rs.1 ∧
      generatedOctadShortSupport generatedOctadBasisOctad rs.2 ∧
      (griessShortQ rs.1 * griessShortQ rs.2).base = (griessShortQ u).base} ≃
    {rs : {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} ×
        {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} //
      (griessShortQ rs.1.val * griessShortQ rs.2.val).base = (griessShortQ u).base} where
  toFun rs := ⟨(⟨rs.val.1, rs.property.1⟩, ⟨rs.val.2, rs.property.2.1⟩), rs.property.2.2⟩
  invFun rs := ⟨(rs.val.1.val, rs.val.2.val),
    rs.val.1.property, rs.val.2.property, rs.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The genuine convolution filter contains exactly 56 supported ordered pairs. -/
theorem generatedOctadActualRootPairs_filter_card
    (u : GriessShortIndex) (hu : generatedOctadShortSupport generatedOctadBasisOctad u) :
    (Finset.univ.filter (fun rs : GriessShortIndex × GriessShortIndex =>
      generatedOctadShortSupport generatedOctadBasisOctad rs.1 ∧
      generatedOctadShortSupport generatedOctadBasisOctad rs.2 ∧
      (griessShortQ rs.1 * griessShortQ rs.2).base = (griessShortQ u).base)).card = 56 := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_congr (generatedOctadActualRootPairFilterEquiv u),
    generatedOctadActualRootPairs_card u hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
