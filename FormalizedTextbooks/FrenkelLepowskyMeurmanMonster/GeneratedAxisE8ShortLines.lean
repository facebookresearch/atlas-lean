/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! Actual short-line incidence and its cardinality in genuine E8 sections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Short lines whose actual integral representatives lie in the given section. -/
def generatedAxisE8ShortLines (S : Submodule ℤ leechIntegral) : Set GriessShortIndex :=
  {r | griessShortLatticeVector r ∈ S}

/-- The integral action carries each actual representative to its permuted representative
with its actual sign retained. -/
theorem generatedE8Short_integral_sign (g : leechIsomSubgroup) (r : GriessShortIndex) :
    leechIntegralAction g (griessShortLatticeVector r) =
        griessShortLatticeVector (griessShortPermutation g r) ∨
      leechIntegralAction g (griessShortLatticeVector r) =
        -griessShortLatticeVector (griessShortPermutation g r) := by
  apply leechShort_same_class _ _
    (by rw [leechIntegralAction_squareSum]; exact griessShortIntegral_squareSum r)
    (griessShortIntegral_squareSum _)
  exact (griessShortPermutation_class g r).symm

/-- The actual permutation transports precisely the short lines of the actual image section. -/
theorem generatedAxisE8ShortLines_image_mem (g : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) (r : GriessShortIndex) :
    griessShortPermutation g r ∈
        generatedAxisE8ShortLines (S.map (leechIntegralAction g).toLinearMap) ↔
      r ∈ generatedAxisE8ShortLines S := by
  change griessShortLatticeVector (griessShortPermutation g r) ∈
      S.map (leechIntegralAction g).toLinearMap ↔
    griessShortLatticeVector r ∈ S
  rcases generatedE8Short_integral_sign g r with h | h
  · rw [← h, Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_apply_apply]
  · have hh : griessShortLatticeVector (griessShortPermutation g r) =
        -leechIntegralAction g (griessShortLatticeVector r) := by
      rw [h, neg_neg]
    rw [hh, Submodule.neg_mem_iff, Submodule.mem_map_equiv]
    simp only [LinearEquiv.symm_apply_apply]

/-- Restricting the genuine short permutation gives a bijection on incident lines. -/
def generatedAxisE8ShortLinesEquiv (g : leechIsomSubgroup) (S : Submodule ℤ leechIntegral) :
    generatedAxisE8ShortLines S ≃
      generatedAxisE8ShortLines (S.map (leechIntegralAction g).toLinearMap) :=
  (griessShortPermutation g).subtypeEquiv
    (fun r => (generatedAxisE8ShortLines_image_mem g S r).symm)

/-- Coordinate section membership is exactly the proved actual octad short support. -/
theorem generatedAxisE8ShortLines_coordinate_mem (o : Fin 759) (r : GriessShortIndex) :
    r ∈ generatedAxisE8ShortLines (generatedAxisE8CoordinateSection (golayOctadWord o)) ↔
      generatedOctadShortSupport o r := by
  rw [generatedOctadShortSupport_iff_physical]
  change generatedOctadSupported (golayOctadWord o) (griessShortIntegral r) ↔ _
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have hbit (i : Fin 24) : golayOctadWord o i = 0 ↔
      (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false := by
    have h := not_congr (golayOctadWord_ne_zero_iff o i)
    simpa only [not_not, golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.not_eq_true] using h
  have hzero (i : Fin 24) : griessShortIntegral r i = 0 ↔ griessShortVector r i = 0 := by
    simp [griessShortVector, hsqrt]
  constructor
  · intro h i hi
    exact (hzero i).mp (h i ((hbit i).mpr hi))
  · intro h i hi
    exact (hzero i).mpr (h i ((hbit i).mp hi))

/-- Each coordinate E8 section contains exactly 120 actual unoriented short lines. -/
theorem generatedAxisE8ShortLines_coordinate_card (o : Fin 759) :
    Nat.card (generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) = 120 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (generatedAxisE8ShortLines_coordinate_mem o)), generatedOctad_short_support_card]

/-- Every actual image E8 section also contains exactly 120 actual short lines. -/
theorem generatedAxisE8ShortLines_image_card (o : Fin 759) (g : leechIsomSubgroup) :
    Nat.card (generatedAxisE8ShortLines (generatedAxisE8ImageSection g (golayOctadWord o))) =
      120 := by
  unfold generatedAxisE8ImageSection
  rw [← Nat.card_congr (generatedAxisE8ShortLinesEquiv g
    (generatedAxisE8CoordinateSection (golayOctadWord o)))]
  exact generatedAxisE8ShortLines_coordinate_card o

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
