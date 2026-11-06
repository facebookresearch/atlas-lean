/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightPermutations

/-! The actual preparation and three-bases operations preserve the coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every Golay sign preserves coordinate support in both directions. -/
theorem generatedStandardOctadPreserves_sign (d : golayCode) :
    generatedStandardOctadPreserves (golaySignIsometry d) := by
  intro u
  rw [leechIntegralAction_golaySign]
  constructor
  · intro h i hi
    have he := h i hi
    change (if d.val i = 0 then u.val i else -u.val i) = 0 at he
    split_ifs at he <;> simpa using he
  · intro h i hi
    change (if d.val i = 0 then u.val i else -u.val i) = 0
    rw [h i hi]
    split_ifs <;> rfl

/-- A Golay permutation fixing the octad preserves its coordinate section. -/
theorem generatedStandardOctadPreserves_permutation (p : golayAutomorphismSubgroup)
    (hp : golayPermute p.val golayStandardOctad = golayStandardOctad) :
    generatedStandardOctadPreserves (golayPermutationIsometry p) := by
  have hb (i : Fin 24) : (p.val.symm i).val < 8 ↔ i.val < 8 := by
    have he := congrFun hp i
    change (if (p.val.symm i).val < 8 then (1 : ZMod 2) else 0) =
      (if i.val < 8 then 1 else 0) at he
    by_cases h1 : (p.val.symm i).val < 8 <;>
      by_cases h2 : i.val < 8 <;> simp_all
    omega
  intro u
  rw [leechIntegralAction_golayPermutation]
  constructor
  · intro h i hi
    have hip : 8 ≤ (p.val i).val := by
      have he := hb (p.val i)
      rw [p.val.symm_apply_apply] at he
      omega
    have he := h (p.val i) hip
    simpa only [golayIntegerPermute, p.val.symm_apply_apply] using he
  · intro h i hi
    exact h (p.val.symm i) (by have he := hb i; omega)

private theorem generatedStandardOctad_xi_forward (u : leechIntegral)
    (hu : generatedStandardOctadSupported u.val) :
    generatedStandardOctadSupported (leechIntegralAction co1XiIsometry u).val := by
  intro i hi
  have hnum : (co1XiNumerator *ᵥ u.val) i = 0 := by
    change ∑ j, co1XiNumerator i j * u.val j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : 8 ≤ j.val
    · rw [hu j hj, mul_zero]
    · have hb : i.val / 4 ≠ j.val / 4 := by omega
      simp [co1XiNumerator, hb]
  have hd := congrArg (fun v : Fin 24 → ℤ => v i) (co1Xi_integral_double u)
  change 2 * (leechIntegralAction co1XiIsometry u).val i = _ at hd
  rw [hnum] at hd
  omega

/-- The actual block matrix ξ preserves this section; its cube proves the converse. -/
theorem generatedStandardOctadPreserves_xi :
    generatedStandardOctadPreserves co1XiIsometry := by
  intro u
  constructor
  · intro h
    have h1 := generatedStandardOctad_xi_forward _ h
    have h2 := generatedStandardOctad_xi_forward _ h1
    have he : leechIntegralAction co1XiIsometry
        (leechIntegralAction co1XiIsometry (leechIntegralAction co1XiIsometry u)) = u := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
      rw [show co1XiIsometry * co1XiIsometry * co1XiIsometry = co1XiIsometry ^ 3 by
        simp [pow_succ, mul_assoc], co1XiIsometry_cube, map_one]
      rfl
    rw [he] at h2
    exact h2
  · exact generatedStandardOctad_xi_forward u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
