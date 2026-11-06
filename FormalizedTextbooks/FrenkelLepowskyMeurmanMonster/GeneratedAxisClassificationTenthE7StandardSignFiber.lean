/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7TwistedSignFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8AffineData

/-! Complete actual Golay correction fibers in the standard Tenth coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The ordered standard coordinates transported to all six actual outside coordinates. -/
def generatedTenthE7StandardOutsideCoordinates : Fin 6 → Fin 24 :=
  ![14, 13, 10, 8, 22, 23]

/-- All twenty-four forward coordinates of the genuine original transport word. -/
theorem generatedTenth_e7_standard_transport_forward : ∀ i : Fin 24,
    generatedTenthE8StandardPermutation.val i =
      (![5, 6, 12, 15, 16, 21, 17, 23, 11, 1, 8, 2,
        14, 7, 4, 13, 0, 3, 9, 10, 22, 19, 18, 20] : Fin 24 → Fin 24) i := by
  decide +kernel

/-- The genuine source word transports the complete normal pair and outside support. -/
theorem generatedTenth_e7_standard_sign_transport_coordinates :
    generatedTenthE8StandardPermutation.val 4 = 16 ∧
      generatedTenthE8StandardPermutation.val 5 = 21 ∧
      ∀ i : Fin 6,
        generatedTenthE8StandardPermutation.val (generatedTenthE7StandardOutsideCoordinates i) =
          generatedTenthE7OutsideSignCoordinates i := by
  simp_rw [generatedTenth_e7_standard_transport_forward]
  decide +kernel

/-- Every actual code coordinate is carried forward by the genuine permutation. -/
theorem generatedTenth_e7_standard_code_forward (c : golayCode) (i : Fin 24) :
    (golayCodePermutation generatedTenthE8StandardPermutation c).val
      (generatedTenthE8StandardPermutation.val i) = c.val i := by
  change c.val (generatedTenthE8StandardPermutation.val.symm
    (generatedTenthE8StandardPermutation.val i)) = c.val i
  rw [generatedTenthE8StandardPermutation.val.symm_apply_apply]

/-- The entire standard-coordinate correction condition for the specified outside phase. -/
def generatedTenthE7StandardTwistedSignCondition (y : Fin 6 → ZMod 2) (c : golayCode) : Prop :=
  c.val 4 = c.val 5 ∧ ∀ i : Fin 6,
    c.val (generatedTenthE7StandardOutsideCoordinates i) + y i = c.val 14 + y 0

/-- Genuine transport identifies the full standard and physical correction conditions. -/
theorem generatedTenth_e7_standard_twisted_sign_transport (y : Fin 6 → ZMod 2)
    (c : golayCode) :
    generatedTenthE7StandardTwistedSignCondition y c ↔
      generatedTenthE7TwistedSignCondition y
        (golayCodePermutation generatedTenthE8StandardPermutation c) := by
  obtain ⟨h4, h5, hout⟩ := generatedTenth_e7_standard_sign_transport_coordinates
  unfold generatedTenthE7StandardTwistedSignCondition generatedTenthE7TwistedSignCondition
  have hc4 := generatedTenth_e7_standard_code_forward c 4
  have hc5 := generatedTenth_e7_standard_code_forward c 5
  rw [h4] at hc4
  rw [h5] at hc5
  have hc : ∀ i : Fin 6,
      (golayCodePermutation generatedTenthE8StandardPermutation c).val
        (generatedTenthE7OutsideSignCoordinates i) =
          c.val (generatedTenthE7StandardOutsideCoordinates i) := by
    intro i
    rw [← hout i, generatedTenth_e7_standard_code_forward]
  have hc0 := hc 0
  change (golayCodePermutation generatedTenthE8StandardPermutation c).val 4 =
    c.val 14 at hc0
  simp only [hc4, hc5, hc0, hc]

/-- The actual code permutation bijects the entire standard and physical fibers. -/
def generatedTenthE7StandardTwistedSignEquiv (y : Fin 6 → ZMod 2) :
    {c : golayCode // generatedTenthE7StandardTwistedSignCondition y c} ≃
      {c : golayCode // generatedTenthE7TwistedSignCondition y c} :=
  (golayCodePermutation generatedTenthE8StandardPermutation).subtypeEquiv
    (generatedTenth_e7_standard_twisted_sign_transport y)

/-- Every even standard outside phase has exactly128 actual original Golay corrections. -/
theorem generatedTenth_e7_standard_twisted_sign_fiber_card (y : Fin 6 → ZMod 2)
    (hy : ∑ i, y i = 0) :
    Nat.card {c : golayCode // generatedTenthE7StandardTwistedSignCondition y c} = 128 := by
  rw [Nat.card_congr (generatedTenthE7StandardTwistedSignEquiv y)]
  exact generatedTenth_e7_twisted_sign_fiber_card y hy

/-- Every permutation of the complete outside support has exactly128 actual code corrections. -/
theorem generatedTenth_e7_standard_permutation_phase_fiber_card (s : Equiv.Perm (Fin 6))
    (a : Fin 6 → ZMod 2) :
    Nat.card {c : golayCode //
      generatedTenthE7StandardTwistedSignCondition (fun i => a i + a (s i)) c} = 128 :=
  generatedTenth_e7_standard_twisted_sign_fiber_card _
    (generatedTenth_e7_permutation_phase_even s a)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
