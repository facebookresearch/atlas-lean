/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixRootedXiPreparation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixMonomialMultiplicity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddFiveOrbits

/-! Actual Xi reductions from the even and odd five-coordinate paired families to the odd
three-coordinate family, inside the genuine positive-root stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A literal Xi image of the odd three-coordinate shape transfers through genuine monomial
coordinates to the actual positive-root stabilizer. -/
theorem leechNormSixPair_xi_conjugate_reduction (u : LeechNormSixPair)
    (b : leechIsomSubgroup) (hb : b ∈ golayMonomialSubgroup)
    (hroot : leechIntegralAction b leechRootedA2Root = leechRootedA2XiRoot)
    (hshape : leechNormEightMultiplicity
      (leechIntegralAction co1XiIsometry (leechIntegralAction b u.val)).val =
        leechNormSixShapeCounts 3) :
    ∃ e : leechRootedA2PositiveRootSubgroup,
      leechNormEightMultiplicity (e • u).val.val = leechNormSixShapeCounts 3 := by
  have hr := leechRootedA2XiTransport_conjugate_fixes b hroot
  let e : leechRootedA2PositiveRootSubgroup :=
    ⟨⟨b⁻¹ * co1XiIsometry * b,
      (leechRootedA2RootLineSubgroup_mem _).mpr (Or.inl hr)⟩, hr⟩
  refine ⟨e, ?_⟩
  rw [leechNormSixPair_smul_val]
  change leechNormEightMultiplicity
    (leechIntegralAction (b⁻¹ * co1XiIsometry * b) u.val).val = _
  rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply,
    leechNormSix_monomial_multiplicity b⁻¹ (golayMonomialSubgroup.inv_mem hb)]
  exact hshape

/-- Every actual even paired norm-six vector reduces to the proved odd three-coordinate family
through a genuine positive-root stabilizer element. -/
theorem leechNormSixPair_even_xi_reduction (u : LeechNormSixPair) (s : Fin 4)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts s)
    (he : s = 0 ∨ s = 1) :
    ∃ e : leechRootedA2PositiveRootSubgroup,
      leechNormEightMultiplicity (e • u).val.val = leechNormSixShapeCounts 3 := by
  obtain ⟨i, j, hi0, hi1, hj0, hj1, hij, hival, hjval⟩ :=
    leechNormSixPair_even_outside u s hs he
  obtain ⟨b, hb, hroot, h0, h1, h2, h3⟩ := leechNormSix_rooted_xi_preparation
    u.val i j hi0 hi1 hj0 hj1 hij 2 0 hival (by rw [hjval])
  let w := leechIntegralAction b u.val
  let x := leechIntegralAction co1XiIsometry w
  have hx2 : x.val 2 = -3 := by
    have h := congrFun (co1Xi_integral_double w) 2
    rw [(co1Xi_first_four_numerator w.val).2.2.1, h0, h1, h2, h3] at h
    have hp := u.property.2
    change 2 * x.val 2 = -2 - u.val.val 0 + -u.val.val 1 - 0 at h
    omega
  have hxnorm : leechSquareSum x.val = 48 := by
    dsimp [x, w]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum]
    exact u.property.1
  have hxshape := leechNormSix_of_magnitude_three x hxnorm 2 (by rw [hx2]; rfl)
  exact leechNormSixPair_xi_conjugate_reduction u b hb hroot hxshape

/-- The actual odd five-coordinate family reduces to the same odd three-coordinate family
through a genuine positive-root stabilizer element. -/
theorem leechNormSixPair_odd_five_xi_reduction (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 2) :
    ∃ e : leechRootedA2PositiveRootSubgroup,
      leechNormEightMultiplicity (e • u).val.val = leechNormSixShapeCounts 3 := by
  obtain ⟨i, j, hi0, hi1, hj0, hj1, hij, hival, hjval⟩ :=
    leechNormSixPair_odd_five_outside u hs
  obtain ⟨b, hb, hroot, h0, h1, h2, h3⟩ := leechNormSix_rooted_xi_preparation
    u.val i j hi0 hi1 hj0 hj1 hij 1 1 hival hjval
  let w := leechIntegralAction b u.val
  let x := leechIntegralAction co1XiIsometry w
  have hx0 : (x.val 0).natAbs = 3 := by
    have h := congrFun (co1Xi_integral_double w) 0
    rw [(co1Xi_first_four_numerator w.val).1, h0, h1, h2, h3] at h
    change 2 * x.val 0 = -1 + u.val.val 0 + -u.val.val 1 + 1 at h
    rcases leechNormSixPair_odd_five_root_pattern u hs with ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩
    · rw [hu0, hu1] at h
      have hx : x.val 0 = 3 := by omega
      rw [hx]
      rfl
    · rw [hu0, hu1] at h
      have hx : x.val 0 = -3 := by omega
      rw [hx]
      rfl
  have hxnorm : leechSquareSum x.val = 48 := by
    dsimp [x, w]
    rw [leechIntegralAction_squareSum, leechIntegralAction_squareSum]
    exact u.property.1
  have hxshape := leechNormSix_of_magnitude_three x hxnorm 0 hx0
  exact leechNormSixPair_xi_conjugate_reduction u b hb hroot hxshape

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
