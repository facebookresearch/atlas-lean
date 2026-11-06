/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100PairPointStabilizer

/-! Actual orbit-stabilizer and full transitivity on the original one-hundred-point flag geometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The orbit of the actual positive pair has exactly one hundred complete original points. -/
theorem leechNormSixHS100PairPoint_orbit_card :
    Nat.card (MulAction.orbit
      (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
      leechNormSixHS100PairPoint) = 100 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
    leechNormSixHS100PairPoint)
  rw [Nat.card_prod, leechNormSixActualPairStabilizer_card _ _
    leechNormSixHS100Root_square leechNormSixHS100Companion_square
    leechNormSixHS100Flag_pairing] at h
  change _ * Nat.card leechNormSixHS100PairPointStabilizer = 44352000 at h
  rw [leechNormSixHS100PairPointStabilizer_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 443520) h

/-- The actual positive-pair orbit covers every point of the complete original catalogue. -/
theorem leechNormSixHS100PairPoint_orbit_univ :
    MulAction.orbit
      (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
      leechNormSixHS100PairPoint = Set.univ := by
  let : Finite (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :=
    Nat.finite_of_card_ne_zero (by rw [leechNormSixHS100CanonicalPoints_card]; decide)
  have hcard := leechNormSixHS100PairPoint_orbit_card.trans
    leechNormSixHS100CanonicalPoints_card.symm
  have hb := (Nat.bijective_iff_injective_and_card Subtype.val).mpr
    ⟨Subtype.val_injective, hcard⟩
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨w, hw⟩ := hb.2 z
  exact hw ▸ w.property

/-- The actual flag stabilizer sends the genuine positive pair to any original point. -/
theorem leechNormSixHS100PairPoint_reaches
    (z : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :
    ∃ g : leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion,
      g • leechNormSixHS100PairPoint = z := by
  have hz : z ∈ MulAction.orbit
      (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
      leechNormSixHS100PairPoint := by
    rw [leechNormSixHS100PairPoint_orbit_univ]
    trivial
  exact hz

/-- Any two complete canonical points are related by an actual flag-stabilizing Conway isometry. -/
theorem leechNormSixHS100Canonical_transitive
    (z w : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) :
    ∃ g : leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion,
      g • z = w := by
  obtain ⟨a, ha⟩ := leechNormSixHS100PairPoint_reaches z
  obtain ⟨b, hb⟩ := leechNormSixHS100PairPoint_reaches w
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, ← hb, mul_smul, inv_smul_smul]

/-- Every genuine norm-four/norm-six flag has a transitive actual Conway action on its complete points. -/
theorem leechNormSixHS100Points_transitive (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16)
    (z w : LeechNormSixHS100Points x y) :
    ∃ g : leechNormSixActualPairStabilizer x y, g • z = w := by
  obtain ⟨t, htx, hty⟩ := leechNormSixHS100Flag_transport x y hx hy hxy
  let zc : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion :=
    ⟨leechIntegralAction t z.val, by
      have hz := (leechNormSixHS100PointCondition_action t x y z.val).mpr z.property
      rwa [htx, hty] at hz⟩
  let wc : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion :=
    ⟨leechIntegralAction t w.val, by
      have hw := (leechNormSixHS100PointCondition_action t x y w.val).mpr w.property
      rwa [htx, hty] at hw⟩
  obtain ⟨h, he⟩ := leechNormSixHS100Canonical_transitive zc wc
  obtain ⟨hfx, hfy⟩ := (leechNormSixActualPairStabilizer_mem _ _ h.val).mp h.property
  have hevec : leechIntegralAction h.val (leechIntegralAction t z.val) =
      leechIntegralAction t w.val := congrArg Subtype.val he
  let g : leechIsomSubgroup := t⁻¹ * h.val * t
  have hga (u : leechIntegral) : leechIntegralAction g u =
      leechIntegralAction t⁻¹ (leechIntegralAction h.val (leechIntegralAction t u)) := by
    simp only [g, map_mul, LinearEquiv.mul_apply]
  have hcancel (u : leechIntegral) : leechIntegralAction t⁻¹ (leechIntegralAction t u) = u := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hgf : g ∈ leechNormSixActualPairStabilizer x y := by
    apply (leechNormSixActualPairStabilizer_mem x y g).mpr
    constructor
    · rw [hga, htx, hfx, ← htx]
      exact hcancel x
    · rw [hga, hty, hfy, ← hty]
      exact hcancel y
  refine ⟨⟨g, hgf⟩, ?_⟩
  apply Subtype.ext
  change leechIntegralAction g z.val = w.val
  rw [hga, hevec]
  exact hcancel w.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
