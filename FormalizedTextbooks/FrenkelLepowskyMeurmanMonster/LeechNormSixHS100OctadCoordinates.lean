/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Flag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOrthogonalOctadCoordinates

/-! Exact positive octad points of the actual canonical lattice flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The genuine shortest lattice vector with positive coefficients on the entire original octad. -/
def leechNormSixHS100Octad (o : Fin 759) : leechIntegral :=
  griessShortLatticeVector (Sum.inr (Sum.inl (o, 0)))

/-- Every original physical octad coordinate is retained with its positive coefficient two. -/
theorem leechNormSixHS100Octad_coordinate (o : Fin 759) (i : Fin 24) :
    (leechNormSixHS100Octad o).val i =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 2 else 0 := by
  have hm : griessOctadSignMask o 0 = 0 := by
    have hz : trialityEvenMask (0 : Fin 64) = 0 := by decide +kernel
    simp [griessOctadSignMask, hz]
  simp only [leechNormSixHS100Octad, griessShortLatticeVector, griessShortIntegral,
    hm, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]

/-- The complete positive octad has original integer square sum thirty-two. -/
theorem leechNormSixHS100Octad_square (o : Fin 759) :
    leechSquareSum (leechNormSixHS100Octad o).val = 32 :=
  griessShortIntegral_squareSum (Sum.inr (Sum.inl (o, 0)))

/-- Every complete positive octad has coordinate sum sixteen. -/
theorem leechNormSixHS100Octad_sum (o : Fin 759) :
    (∑ i, (leechNormSixHS100Octad o).val i) = 16 := by
  simp_rw [leechNormSixHS100Octad_coordinate]
  have hc : (Finset.univ.filter fun i : Fin 24 =>
      (golayEncodedMask (golayOctadLabel o).val).testBit i.val).card = 8 :=
    golayOctad_support_card o
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [hc]
  norm_num

/-- Every actual octad through the two root coordinates is a genuine canonical flag point. -/
theorem leechNormSixHS100Octad_point (o : Fin 759)
    (ho : o ∈ generatedFeasibleOctadContainingLabels) :
    LeechNormSixHS100PointCondition leechNormSixHS100Root leechNormSixHS100Companion
      (leechNormSixHS100Octad o) := by
  obtain ⟨h0, h1⟩ := (Finset.mem_filter.mp ho).2
  rw [leechNormSixHS100PointCondition_coordinates]
  refine ⟨leechNormSixHS100Octad_square o, ?_, ?_⟩
  · simp only [leechNormSixHS100Octad_coordinate, Fin.val_zero, Fin.val_one, h0, h1, ↓reduceIte]
  · rw [leechNormSixHS100Octad_sum, leechNormSixHS100Octad_coordinate]
    simp only [Fin.val_zero, h0, ↓reduceIte]
    norm_num

/-- Original signed octad coordinates meeting the flag conditions must all be positive. -/
theorem leechNormSixHS100Octad_classification (z : leechIntegral) (o : Fin 759)
    (hv : ∀ i, if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then
      z.val i = -2 ∨ z.val i = 2 else z.val i = 0)
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) :
    o ∈ generatedFeasibleOctadContainingLabels ∧ z = leechNormSixHS100Octad o := by
  obtain ⟨_, h01, hyp⟩ := (leechNormSixHS100PointCondition_coordinates z).mp hz
  have hle (i : Fin 24) : z.val i ≤ (leechNormSixHS100Octad o).val i := by
    rw [leechNormSixHS100Octad_coordinate]
    cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val
    · have h := hv i
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢
      omega
    · have h := hv i
      simp only [hb, ↓reduceIte] at h ⊢
      rcases h with h | h <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
  rw [leechNormSixHS100Octad_sum] at hs
  have h0le : z.val 0 ≤ 2 := by
    have h := hle 0
    rw [leechNormSixHS100Octad_coordinate] at h
    split_ifs at h <;> omega
  have h0 : z.val 0 = 2 := by omega
  have hsum : (∑ i, z.val i) = 16 := by omega
  have hdiff : (∑ i, ((leechNormSixHS100Octad o).val i - z.val i)) = 0 := by
    rw [Finset.sum_sub_distrib, leechNormSixHS100Octad_sum, hsum]
    norm_num
  have he (i : Fin 24) : z.val i = (leechNormSixHS100Octad o).val i := by
    have h := Finset.single_le_sum (f := fun j : Fin 24 =>
      (leechNormSixHS100Octad o).val j - z.val j)
      (fun j _ => sub_nonneg.mpr (hle j)) (Finset.mem_univ i)
    rw [hdiff] at h
    have h' := hle i
    omega
  have hb0 : (golayEncodedMask (golayOctadLabel o).val).testBit 0 = true := by
    have h := he 0
    rw [leechNormSixHS100Octad_coordinate, h0] at h
    cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit 0
    · simp only [Fin.val_zero, hb, Bool.false_eq_true, ↓reduceIte] at h
      omega
    · rfl
  have hb1 : (golayEncodedMask (golayOctadLabel o).val).testBit 1 = true := by
    have h := he 1
    rw [leechNormSixHS100Octad_coordinate, ← h01, h0] at h
    cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit 1
    · simp only [Fin.val_one, hb, Bool.false_eq_true, ↓reduceIte] at h
      omega
    · rfl
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0, hb1⟩,
    Subtype.ext (funext he)⟩

/-- Both original signs of every full preferred octad label have the exact positive-octad classification. -/
theorem leechNormSixHS100Octad_catalog (z : leechIntegral) (o : Fin 759) (e : Fin 64)
    (hp : z.val = griessShortIntegral (Sum.inr (Sum.inl (o, e))) ∨
      z.val = -griessShortIntegral (Sum.inr (Sum.inl (o, e))))
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) :
    o ∈ generatedFeasibleOctadContainingLabels ∧ z = leechNormSixHS100Octad o := by
  refine leechNormSixHS100Octad_classification z o ?_ hz
  intro i
  rcases hp with hp | hp <;> rw [hp]
  all_goals
    cases hm : (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;>
      cases hs : (griessOctadSignMask o e).testBit i.val <;>
      simp [griessShortIntegral, Pi.neg_apply, hm, hs]

/-- Different original octads give different complete physical positive-octad vectors. -/
theorem leechNormSixHS100Octad_injective : Function.Injective leechNormSixHS100Octad := by
  intro o p h
  have he := griessShort_label_unique (Sum.inr (Sum.inl (o, 0)))
    (Sum.inr (Sum.inl (p, 0))) (Or.inl (congrArg Subtype.val h))
  simpa only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
