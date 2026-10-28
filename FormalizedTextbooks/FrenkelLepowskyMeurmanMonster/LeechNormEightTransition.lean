/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual three-bases isometry lowers the rank of every nonterminal norm-eight shape. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightTransitionData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCatalog

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The transformed tetrad is computed from the actual integral action, without rounding. -/
theorem leechNormEightXi_prepared_row (u : leechIntegral) (s : Fin 8)
    (hr : ∀ j : Fin 4, u.val (Fin.castAdd 20 j) = leechNormEightTargetRows s j) :
    ∀ j : Fin 4, (leechIntegralAction co1XiIsometry u).val (Fin.castAdd 20 j) =
      leechNormEightXiTargetRows s j := by
  have h0 : u.val 0 = leechNormEightTargetRows s 0 := hr 0
  have h1 : u.val 1 = leechNormEightTargetRows s 1 := hr 1
  have h2 : u.val 2 = leechNormEightTargetRows s 2 := hr 2
  have h3 : u.val 3 = leechNormEightTargetRows s 3 := hr 3
  obtain ⟨hn0, hn1, hn2, hn3⟩ := co1Xi_first_four_numerator u.val
  obtain ⟨hc0, hc1, hc2, hc3⟩ := leechNormEightXiTargetRows_double s
  have hd (i : Fin 24) :
      2 * (leechIntegralAction co1XiIsometry u).val i = (co1XiNumerator *ᵥ u.val) i := by
    exact congrArg (fun v : Fin 24 → ℤ => v i) (co1Xi_integral_double u)
  rw [h0, h1, h2, h3] at hn0 hn1 hn2 hn3
  intro j
  fin_cases j
  · have h := (hd 0).trans hn0
    change (leechIntegralAction co1XiIsometry u).val 0 = leechNormEightXiTargetRows s 0
    linarith only [h, hc0]
  · have h := (hd 1).trans hn1
    change (leechIntegralAction co1XiIsometry u).val 1 = leechNormEightXiTargetRows s 1
    linarith only [h, hc1]
  · have h := (hd 2).trans hn2
    change (leechIntegralAction co1XiIsometry u).val 2 = leechNormEightXiTargetRows s 2
    linarith only [h, hc2]
  · have h := (hd 3).trans hn3
    change (leechIntegralAction co1XiIsometry u).val 3 = leechNormEightXiTargetRows s 3
    linarith only [h, hc3]

/-- An actual prepared nonterminal vector moves to a strictly lower catalogue rank. -/
theorem leechNormEightXi_prepared_rank (u : leechIntegral) (s : Fin 8)
    (hs : leechSquareSum u.val = 64) (hs0 : s ≠ 0)
    (hr : ∀ j : Fin 4, u.val (Fin.castAdd 20 j) = leechNormEightTargetRows s j) :
    ∃ t : Fin 8,
      leechNormEightMultiplicity (leechIntegralAction co1XiIsometry u).val =
        leechNormEightShapeCounts t ∧ leechNormEightShapeRank t < leechNormEightShapeRank s := by
  obtain ⟨t, ht⟩ := leechNormEight_catalog (leechIntegralAction co1XiIsometry u)
    (by rw [leechIntegralAction_squareSum, hs])
  refine ⟨t, ht, leechNormEightXiTargetRows_rank_decreases s t hs0 ?_⟩
  intro k
  have hc := leechNormEight_row_multiplicity_le
    (leechIntegralAction co1XiIsometry u).val (leechNormEightXiTargetRows s)
    (leechNormEightXi_prepared_row u s hr) k
  rw [ht] at hc
  exact hc

/-- Preparation followed by the actual ξ is an element of the concrete generator subgroup
and lowers the norm-eight shape rank. -/
theorem leechNormEight_concrete_rank_step (u : leechIntegral) (s : Fin 8)
    (hs : leechSquareSum u.val = 64)
    (hshape : leechNormEightMultiplicity u.val = leechNormEightShapeCounts s) (hs0 : s ≠ 0) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧ ∃ t : Fin 8,
      leechNormEightMultiplicity (leechIntegralAction e u).val = leechNormEightShapeCounts t ∧
      leechNormEightShapeRank t < leechNormEightShapeRank s := by
  obtain ⟨e, he, hr⟩ := leechNormEight_monomial_preparation u s hshape
  obtain ⟨t, ht, hlt⟩ := leechNormEightXi_prepared_rank (leechIntegralAction e u) s
    (by rw [leechIntegralAction_squareSum, hs]) hs0 hr
  refine ⟨co1XiIsometry * e,
    leechConcreteGeneratorSubgroup.mul_mem co1XiIsometry_mem_concrete he, t, ?_, hlt⟩
  simpa only [map_mul, LinearEquiv.mul_apply] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
