/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual longest source involution and its determinant provide a central splitting. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationAbelianization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Certificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual corrected seven-letter longest involution in the original source presentation. -/
def y322CentralInvolution : Y322Presentation :=
  PresentedGroup.mk y322Relations y322E7Word12

/-- The exact original longest word has square one, by the checked source rewrite certificate. -/
theorem y322CentralInvolution_square : y322CentralInvolution * y322CentralInvolution = 1 := by
  simpa only [y322CentralInvolution, pow_two] using y322E7Word12_square

set_option maxRecDepth 10000 in
-- The literal 63-letter original longest word exceeds the default reduction recursion depth.
/-- The exact original longest involution has nontrivial genuine determinant sign. -/
theorem y322CentralInvolution_sign : y322Orthogonal3Sign y322CentralInvolution = -1 := by
  change (y322Orthogonal3Sign.comp (PresentedGroup.mk y322Relations)) y322E7Word12 = -1
  unfold y322E7Word12
  simp only [map_pow, map_mul]
  change (y322Orthogonal3Sign (PresentedGroup.of 0) *
    y322Orthogonal3Sign (PresentedGroup.of 1) * y322Orthogonal3Sign (PresentedGroup.of 4) *
    y322Orthogonal3Sign (PresentedGroup.of 6) * y322Orthogonal3Sign (PresentedGroup.of 2) *
    y322Orthogonal3Sign (PresentedGroup.of 5) * y322Orthogonal3Sign (PresentedGroup.of 3)) ^ 9 = -1
  simp only [y322Orthogonal3Sign_generator]
  norm_num

/-- A faithful actual source matrix representation proves full centrality of the longest word. -/
theorem y322CentralInvolution_commute_of_injective
    (hi : Function.Injective y322Orthogonal3Hom) (x : Y322Presentation) :
    y322CentralInvolution * x = x * y322CentralInvolution := by
  apply hi
  simp only [map_mul]
  apply Units.ext
  simp only [Units.val_mul]
  rw [y322CentralInvolution, y322Orthogonal3Hom_longest]
  simp only [neg_mul, mul_neg, one_mul, mul_one]

/-- The actual finite-field minus-one unit differs from one. -/
theorem y322Sign_minus_one_ne_one : (-1 : (ZMod 3)ˣ) ≠ 1 := by
  decide +kernel

/-- The literal sign section chooses the identity or the actual longest involution. -/
def y322SignSectionValue (u : (ZMod 3)ˣ) : Y322Presentation :=
  if u = 1 then 1 else y322CentralInvolution

/-- The literal two-valued section is a genuine homomorphism into the original source group. -/
def y322SignSection : (ZMod 3)ˣ →* Y322Presentation where
  toFun := y322SignSectionValue
  map_one' := by simp [y322SignSectionValue]
  map_mul' u v := by
    rcases y322ZModThree_units_two_values u with rfl | rfl <;>
      rcases y322ZModThree_units_two_values v with rfl | rfl
    all_goals simp [y322SignSectionValue, y322Sign_minus_one_ne_one, y322CentralInvolution_square]

/-- The actual longest-word section is a right inverse of the genuine source sign. -/
theorem y322SignSection_right_inverse (u : (ZMod 3)ˣ) :
    y322Orthogonal3Sign (y322SignSection u) = u := by
  rcases y322ZModThree_units_two_values u with rfl | rfl
  · simp [y322SignSection, y322SignSectionValue]
  · simp [y322SignSection, y322SignSectionValue, y322Sign_minus_one_ne_one,
      y322CentralInvolution_sign]

/-- Faithfulness of the actual matrices makes every sign-section value central in the source. -/
theorem y322SignSection_commute_of_injective
    (hi : Function.Injective y322Orthogonal3Hom) (u : (ZMod 3)ˣ) (x : Y322Presentation) :
    y322SignSection u * x = x * y322SignSection u := by
  rcases y322ZModThree_units_two_values u with rfl | rfl
  · simp [y322SignSection, y322SignSectionValue]
  · simpa [y322SignSection, y322SignSectionValue, y322Sign_minus_one_ne_one] using
      y322CentralInvolution_commute_of_injective hi x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
