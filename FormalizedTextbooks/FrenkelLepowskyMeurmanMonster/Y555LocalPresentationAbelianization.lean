/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual local abelianization is the finite-field determinant sign group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Determinant

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The determinant sign descends through the actual source commutator quotient. -/
def y322AbelianizationSign : Abelianization Y322Presentation →* (ZMod 3)ˣ :=
  Abelianization.lift y322Orthogonal3Sign

/-- Every actual source abelianization element is one or the first generator's image. -/
theorem y322Abelianization_two_values (x : Abelianization Y322Presentation) :
    x = 1 ∨ x = Abelianization.of (PresentedGroup.of 0 : Y322Presentation) := by
  induction x using QuotientGroup.induction_on with
  | H x => exact y322AbelianImage_two_values Abelianization.of x

/-- The two source abelianization values are distinguished by the genuine determinant sign. -/
theorem y322AbelianizationSign_injective : Function.Injective y322AbelianizationSign := by
  intro x y hxy
  rcases y322Abelianization_two_values x with hx | hx <;>
    rcases y322Abelianization_two_values y with hy | hy
  · exact hx.trans hy.symm
  · exfalso
    rw [hx, hy, map_one] at hxy
    exact y322Orthogonal3Sign_generator_ne_one hxy.symm
  · exfalso
    rw [hx, hy, map_one] at hxy
    exact y322Orthogonal3Sign_generator_ne_one hxy
  · exact hx.trans hy.symm

/-- The field with three elements has only the two units one and minus one. -/
theorem y322ZModThree_units_two_values (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide +kernel

/-- Both finite-field signs are actual values of the original source abelianization. -/
theorem y322AbelianizationSign_surjective : Function.Surjective y322AbelianizationSign := by
  intro u
  rcases y322ZModThree_units_two_values u with h | h
  · exact ⟨1, (map_one _).trans h.symm⟩
  · refine ⟨Abelianization.of (PresentedGroup.of 0), ?_⟩
    exact (y322Orthogonal3Sign_generator 0).trans h.symm

/-- The original source abelianization is isomorphic to the actual two-element sign group. -/
noncomputable def y322AbelianizationEquiv : Abelianization Y322Presentation ≃* (ZMod 3)ˣ :=
  MulEquiv.ofBijective y322AbelianizationSign
    ⟨y322AbelianizationSign_injective, y322AbelianizationSign_surjective⟩

/-- The actual source abelianization has order exactly two. -/
theorem y322Abelianization_card : Nat.card (Abelianization Y322Presentation) = 2 := by
  rw [Nat.card_congr y322AbelianizationEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

/-- The source determinant kernel is exactly its actual commutator subgroup. -/
theorem y322Orthogonal3Sign_ker : y322Orthogonal3Sign.ker = commutator Y322Presentation := by
  rw [← Abelianization.ker_of]
  ext x
  constructor
  · intro hx
    apply y322AbelianizationSign_injective
    change y322Orthogonal3Sign x = y322AbelianizationSign 1
    rw [map_one]
    exact hx
  · intro hx
    change Abelianization.of x = 1 at hx
    change y322AbelianizationSign (Abelianization.of x) = 1
    rw [hx, map_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
