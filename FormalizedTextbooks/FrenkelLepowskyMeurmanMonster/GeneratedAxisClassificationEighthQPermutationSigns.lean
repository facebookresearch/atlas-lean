/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQPermutationRestriction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQMiddleLineLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatial

/-! Code signs adjust coordinate-flag permutations to fix the signed middle direction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original signs of the twelve nonzero middle coordinates; only coordinate sixteen is positive. -/
def generatedEighthMiddleDodecadSign (j : Fin 12) : ZMod 2 :=
  if generatedEighthDodecadCoordinates j = 16 then 0 else 1

private theorem middle_integer_certificate : ∀ i : Fin 24,
    generatedEighthFrameVectorData 7 0 i =
      if i = 20 then 4 else if Nat.testBit 0xc5066f i.val then
        (if i = 16 then 2 else -2) else 0 := by decide +kernel

private theorem coordinates_not_twenty : ∀ j : Fin 12,
    generatedEighthDodecadCoordinates j ≠ 20 := by decide +kernel

/-- The genuine middle direction has its original half and quarter coordinate values. -/
theorem generatedEighth_middle_unit_formula (i : Fin 24) :
    generatedEighthMiddleUnit i = if i = 20 then 1 / 2 else
      if generatedEighthDodecadWord.val i ≠ 0 then
        qSign (if i = 16 then (0 : ZMod 2) else 1) / 4 else 0 := by
  have h := generatedEighth_forward_matrix_coordinate i (0 : Fin 24)
  change generatedEighthMiddleUnit i = (generatedEighthFrameVectorData 7 0 i : ℝ) / 8 at h
  rw [h, middle_integer_certificate, generatedEighth_dodecad_coordinate]
  cases hb : Nat.testBit 0xc5066f i.val <;>
    by_cases h20 : i = 20 <;> by_cases h16 : i = 16 <;>
      norm_num [h20, h16, golayBooleanCast, qSign_zero, qSign_one]

/-- Each genuine dodecad coordinate has its original signed quarter value. -/
theorem generatedEighth_middle_unit_dodecad (j : Fin 12) :
    generatedEighthMiddleUnit (generatedEighthDodecadCoordinates j) =
      qSign (generatedEighthMiddleDodecadSign j) / 4 := by
  have hm := (generatedEighth_dodecad_coordinate_range (generatedEighthDodecadCoordinates j)).mpr
    ⟨j, rfl⟩
  rw [generatedEighth_middle_unit_formula, ite_eq_right (coordinates_not_twenty j), ite_eq_left hm]
  rfl

/-- Every genuine flag permutation admits a genuine code sign fixing the full middle direction. -/
theorem generatedEighth_flag_permutation_signed_unit (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedEighthPermutationFlagStabilizer) :
    ∃ c : golayCode, (golaySignIsometry c * golayPermutationIsometry p).val
      generatedEighthMiddleUnit = generatedEighthMiddleUnit := by
  obtain ⟨q, hq⟩ := generatedEighth_dodecad_permutation_restrict p hp
  let bits : Fin 12 → ZMod 2 := fun j => generatedEighthMiddleDodecadSign j +
    generatedEighthMiddleDodecadSign (q.symm j)
  let c := generatedEighthDodecadSignExtensionCode bits
  have heven : ∑ j, bits j = 0 :=
    generatedEighth_dodecad_sign_difference_even generatedEighthMiddleDodecadSign q
  have hc (j : Fin 12) : c.val (generatedEighthDodecadCoordinates j) = bits j :=
    generatedEighth_dodecad_even_sign_extension bits heven j
  have h20 : c.val 20 = 0 := generatedEighth_dodecad_sign_extension_twenty bits
  have hinv (j : Fin 12) : p.val.symm (generatedEighthDodecadCoordinates j) =
      generatedEighthDodecadCoordinates (q.symm j) := by
    apply p.val.injective
    rw [Equiv.apply_symm_apply, ← hq, Equiv.apply_symm_apply]
  have hp20 := ((generatedEighthPermutationFlagStabilizer_mem p).mp hp).1
  have hp20inv : p.val.symm 20 = 20 := (Equiv.symm_apply_eq p.val).mpr hp20.symm
  have hw := ((generatedEighthPermutationFlagStabilizer_mem p).mp hp).2
  refine ⟨c, ?_⟩
  funext i
  change qSign (c.val i) * generatedEighthMiddleUnit (p.val.symm i) = generatedEighthMiddleUnit i
  by_cases hi20 : i = 20
  · subst i
    rw [hp20inv, h20, qSign_zero, one_mul]
  · by_cases hi : generatedEighthDodecadWord.val i ≠ 0
    · obtain ⟨j, rfl⟩ := (generatedEighth_dodecad_coordinate_range i).mp hi
      rw [hinv, generatedEighth_middle_unit_dodecad,
        generatedEighth_middle_unit_dodecad, hc]
      dsimp only [bits]
      rw [qSign_add]
      calc
        (qSign (generatedEighthMiddleDodecadSign j) *
          qSign (generatedEighthMiddleDodecadSign (q.symm j))) *
            (qSign (generatedEighthMiddleDodecadSign (q.symm j)) / 4) =
          qSign (generatedEighthMiddleDodecadSign j) *
            (qSign (generatedEighthMiddleDodecadSign (q.symm j)) *
              qSign (generatedEighthMiddleDodecadSign (q.symm j))) / 4 := by ring
        _ = _ := by rw [qSign_sq, mul_one]
    · have hwi : generatedEighthDodecadWord.val (p.val.symm i) =
          generatedEighthDodecadWord.val i := congrFun hw i
      have hpre : p.val.symm i ≠ 20 := by
        intro he
        have he' := congrArg p.val he
        rw [Equiv.apply_symm_apply, hp20] at he'
        exact hi20 he'
      rw [generatedEighth_middle_unit_formula, generatedEighth_middle_unit_formula,
        ite_eq_right hpre, ite_eq_right hi20, hwi, ite_eq_right hi, mul_zero, ite_eq_right hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
