/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiQuadraticPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedDot24

/-! The exact full Xi phase uses folded row parity with every original central bit retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- Original combined cocycle rows retain precisely their strictly later coordinates. -/
def generatedSixthXiUpperPairRows : Fin 24 → ℕ :=
  ![9675332, 8390548, 16597344, 1250944, 9115456, 9638528,
    6681088, 8434944, 10008064, 3777536, 5193728, 8388608,
    0, 0, 8388608, 0, 8388608, 8388608, 8388608, 8388608, 0, 0, 8388608, 0]

/-- Every truncated row bit is the actual original strictly ordered cocycle coefficient. -/
theorem generatedSixth_xi_upper_pair_rows (i j : Fin 24) :
    generatedSixthXiBitScalar (generatedSixthXiUpperPairRows i) j.val =
      if i < j then generatedSixthXiBitScalar (generatedSixthXiCombinedPairRows i) j.val
      else 0 := by
  revert i j
  decide +kernel

/-- The displayed original cocycle rows fit in the actual twenty-four-coordinate module. -/
theorem generatedSixth_xi_upper_pair_rows_bound (i : Fin 24) :
    generatedSixthXiUpperPairRows i < 2 ^ 24 := by
  revert i
  decide +kernel

/-- Folded parity evaluates the original central and ordered cocycle polynomial. -/
def generatedSixthXiFoldedPhase (n : ℕ) : ZMod 2 :=
  generatedSixthXiFoldedParity (n &&& generatedSixthXiCoordinateCentralMask) +
    ∑ i : Fin 24, generatedSixthXiBitScalar n i.val *
      generatedSixthXiFoldedParity (n &&& generatedSixthXiUpperPairRows i)

/-- Bounded folded rows evaluate any original ordered scalar cocycle polynomial. -/
theorem generatedSixth_xi_folded_polynomial (n c : ℕ) (r p : Fin 24 → ℕ)
    (hc : c < 2 ^ 24) (hr : ∀ i, r i < 2 ^ 24)
    (hp : ∀ i j : Fin 24, generatedSixthXiBitScalar (r i) j.val =
      if i < j then generatedSixthXiBitScalar (p i) j.val else 0) :
    generatedSixthXiFoldedParity (n &&& c) +
      (∑ i : Fin 24, generatedSixthXiBitScalar n i.val *
        generatedSixthXiFoldedParity (n &&& r i)) =
    generatedSixthQSelectedPhase (fun i => generatedSixthXiBitScalar c i.val)
      (fun i j => generatedSixthXiBitScalar (p i) j.val)
      (monsterCo1GeometryBinaryMaskDecode n) (List.finRange 24) := by
  rw [generatedSixth_xi_folded_dot24 n c hc]
  simp_rw [generatedSixth_xi_folded_dot24 n _ (hr _)]
  rw [generatedSixth_xi_selected_quadratic]
  change (∑ i : Fin 24, generatedSixthXiBitScalar n i.val *
    generatedSixthXiBitScalar c i.val) +
      (∑ i : Fin 24, generatedSixthXiBitScalar n i.val *
        ∑ j : Fin 24, generatedSixthXiBitScalar n j.val *
          generatedSixthXiBitScalar (r i) j.val) =
    (∑ i : Fin 24, generatedSixthXiBitScalar n i.val *
      generatedSixthXiBitScalar c i.val) +
      ∑ i : Fin 24, ∑ j : Fin 24, if i < j then
        generatedSixthXiBitScalar n i.val * generatedSixthXiBitScalar n j.val *
          generatedSixthXiBitScalar (p i) j.val else 0
  apply congrArg (fun z : ZMod 2 =>
    (∑ i : Fin 24, generatedSixthXiBitScalar n i.val * generatedSixthXiBitScalar c i.val) + z)
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh := congrArg (fun z : ZMod 2 => generatedSixthXiBitScalar n i.val *
    (generatedSixthXiBitScalar n j.val * z)) (hp i j)
  refine hh.trans ?_
  by_cases h : i < j
  · simp only [h, ite_true, mul_assoc]
  · simp only [h, ite_false, mul_zero]

/-- The folded phase equals the full actual preferred-Q phase for every original input mask. -/
theorem generatedSixth_xi_folded_phase (n : ℕ) :
    generatedSixthXiFoldedPhase n = generatedSixthXiFastMaskPhase n := by
  rw [← generatedSixth_xi_combined_mask_phase, generatedSixthXiFoldedPhase,
    generatedSixthXiCombinedMaskPhase, generatedSixth_xi_selected_mask_phase]
  exact generatedSixth_xi_folded_polynomial n generatedSixthXiCoordinateCentralMask
    generatedSixthXiUpperPairRows generatedSixthXiCombinedPairRows (by decide +kernel)
    generatedSixth_xi_upper_pair_rows_bound generatedSixth_xi_upper_pair_rows

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
