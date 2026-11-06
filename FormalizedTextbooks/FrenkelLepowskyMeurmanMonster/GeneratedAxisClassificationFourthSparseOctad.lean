/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthSupportEnumeration

/-! Sparse original middle octad coordinates and computable physical/Q bindings
for all 64 signs of each actual octad family occurring in those coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The finite code/sign pairs of the 63 actual octad coordinates are distinct. -/
theorem generatedFourthEvenRootCodeSign_injective : ∀ j k : Fin 63,
    generatedFourthEvenRootCode j = generatedFourthEvenRootCode k →
      generatedFourthEvenRootSign j = generatedFourthEvenRootSign k → j = k := by
  decide +kernel

/-- The 63 genuine preferred octad output labels are distinct. -/
theorem generatedFourthEvenRootOutputLabel_injective :
    Function.Injective generatedFourthEvenRootOutputLabel := by
  intro j k h
  have he : (generatedFourthEvenRootOctad j, generatedFourthEvenRootSign j) =
      (generatedFourthEvenRootOctad k, generatedFourthEvenRootSign k) := by
    simpa only [generatedFourthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl.injEq] using h
  have hc := congrArg golayOctadLabel (congrArg Prod.fst he)
  rw [generatedFourthEvenRootOctad_label, generatedFourthEvenRootOctad_label] at hc
  exact generatedFourthEvenRootCodeSign_injective j k hc (congrArg Prod.snd he)

/-- Every original middle octad row is an exact 63-term sparse signed sum. -/
theorem generatedFourth_middle_octad_sparse (o : Fin 759) (e : Fin 64) :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ j : Fin 63, if generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, e)) then
        qSign (generatedFourthEvenCoefficientPhase j) else 0 := by
  by_cases h : ∃ j : Fin 63,
      generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, e))
  · obtain ⟨j, hj⟩ := h
    have hc := generatedFourth_even_middle_coefficient j
    rw [generatedFourth_local_short, hj] at hc
    rw [hc]
    symm
    calc
      _ = if generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, e)) then
          qSign (generatedFourthEvenCoefficientPhase j) else 0 := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          have hk : generatedFourthEvenRootOutputLabel k ≠ Sum.inr (Sum.inl (o, e)) := by
            intro hk
            exact hkj (generatedFourthEvenRootOutputLabel_injective (hk.trans hj.symm))
          simp only [hk, ite_false]
        · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
      _ = _ := by simp only [hj, ite_true]
  · rw [generatedFourth_middle_octad_zero_outside o e h]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : generatedFourthEvenRootOutputLabel j ≠ Sum.inr (Sum.inl (o, e)) :=
      fun hj => h ⟨j, hj⟩
    simp only [hj, ite_false]

/-- Original sign masks for any of the 64 signs of a listed octad family. -/
def generatedFourthEvenOctadSignMask (j : Fin 63) (e : Fin 64) : Nat :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFourthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- The general finite sign-mask formula is the actual preferred catalogue mask. -/
theorem generatedFourth_even_octad_sign_mask (j : Fin 63) (e : Fin 64) :
    griessOctadSignMask (generatedFourthEvenRootOctad j) e =
      generatedFourthEvenOctadSignMask j e := by
  simp only [griessOctadSignMask, generatedFourth_even_coordinates_certificate,
    generatedFourthEvenOctadSignMask]

/-- Computable integer coordinates of every sign of every listed octad family. -/
def generatedFourthEvenOctadIntegral (j : Fin 63) (e : Fin 64) : Fin 24 → ℤ := fun i =>
  if (golayEncodedMask (generatedFourthEvenRootCode j).val).testBit i.val then
    if (generatedFourthEvenOctadSignMask j e).testBit i.val then -2 else 2
  else 0

/-- The computable integer coordinates are the genuine preferred physical octad vector. -/
theorem generatedFourth_even_octad_integral (j : Fin 63) (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))) =
      generatedFourthEvenOctadIntegral j e := by
  unfold generatedFourthEvenOctadIntegral
  simp only [griessShortIntegral, generatedFourthEvenRootOctad_label,
    generatedFourth_even_octad_sign_mask]

/-- Computable preferred-Q lifts of all sign rows in the listed octad families. -/
def generatedFourthEvenOctadQ (j : Fin 63) (e : Fin 64) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedFourthEvenOctadIntegral j e))), 1⟩

/-- Every computable general octad lift is exactly the intrinsic actual preferred Q lift. -/
theorem generatedFourthEvenOctadQ_eq (j : Fin 63) (e : Fin 64) :
    generatedFourthEvenOctadQ j e =
      griessShortQ (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))) := by
  rw [← monsterNortonShortQ_eq]
  unfold monsterNortonShortQ
  rw [generatedFourth_even_octad_integral]
  rfl

/-- Exactly 47 original Golay code families occur among the 63 actual octad rows. -/
theorem generatedFourth_even_code_families_card :
    (Finset.univ.image generatedFourthEvenRootCode).card = 47 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
