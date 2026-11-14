/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PotentialGamesImprovement

@[expose] public section

/-! # Tests for improvement paths in exact potential games

Boundary checks on a concrete two-player identical-interest game: a
strict step decreases the potential (also in the step-predicate form), a
maximal two-step path ends at a pure Nash equilibrium, the `List.IsChain`
API applies to improvement paths, a one-step prefix is extendable with a
last profile that is not Nash, pinning maximality as load-bearing, and
the empty path is not maximal.
-/

namespace MathlibExtTest.GameTheory.PotentialGamesImprovement

/-- Identical-interest cost: each player's cost is the shared potential. -/
def testCost : Fin 2 → (∀ _ : Fin 2, Bool) → ℝ :=
  fun _ s => (if s 0 then (1 : ℝ) else 0) + (if s 1 then (1 : ℝ) else 0)

/-- Shared potential: the number of players playing `true`. -/
def testPot : (∀ _ : Fin 2, Bool) → ℝ :=
  fun s => (if s 0 then (1 : ℝ) else 0) + (if s 1 then (1 : ℝ) else 0)

/-- The identical-interest game is an exact potential game. -/
theorem testIsExact : IsExactPotential testCost testPot :=
  fun _ _ _ => rfl

/-- All-`true` profile (potential 2). -/
def profTT : ∀ _ : Fin 2, Bool := fun _ => true

/-- Profile after player 0 deviates to `false` (potential 1). -/
def profFT : ∀ _ : Fin 2, Bool := Function.update profTT 0 false

/-- Profile after player 1 follows to `false` (potential 0). -/
def profFF : ∀ _ : Fin 2, Bool := Function.update profFT 1 false

/-- A strict better-response step strictly decreases the potential,
checked on the concrete step from `profTT` to `profFT`. -/
theorem test_strict_step_decreases_potential :
    testPot profFT < testPot profTT := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  have hcost : testCost 0 profFT < testCost 0 profTT := by
    norm_num [testCost, profTT, hFT0, hFT1]
  exact strict_better_response_decreases_potential (Φ := testPot)
    testIsExact (s := profTT) (s' := profFT) rfl hcost

/-- The step-predicate form: the step from `profTT` to `profFT`, given as an
`IsStrictBetterResponse`, strictly decreases the potential. -/
theorem test_step_predicate_decreases_potential :
    testPot profFT < testPot profTT := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  have hcost : testCost 0 profFT < testCost 0 profTT := by
    norm_num [testCost, profTT, hFT0, hFT1]
  exact IsStrictBetterResponse.potential_lt ⟨0, false, rfl, hcost⟩ testIsExact

/-- The two-step improvement path `profTT → profFT → profFF` is maximal. -/
theorem test_two_step_path_is_maximal :
    IsMaximalImprovementPath testCost [profTT, profFT, profFF] := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hFF0 : profFF (0 : Fin 2) = false := by
    simp [profFF, profFT, hne01]
  have hFF1 : profFF (1 : Fin 2) = false := by simp [profFF, profFT]
  have hcost01 : testCost 0 profFT < testCost 0 profTT := by
    norm_num [testCost, profTT, hFT0, hFT1]
  have hcost12 : testCost 1 profFF < testCost 1 profFT := by
    norm_num [testCost, hFT0, hFT1, hFF0, hFF1]
  have hstep01 : IsStrictBetterResponse testCost profTT profFT :=
    ⟨0, false, rfl, hcost01⟩
  have hstep12 : IsStrictBetterResponse testCost profFT profFF :=
    ⟨1, false, rfl, hcost12⟩
  have hchain : IsImprovementPath testCost [profTT, profFT, profFF] :=
    .cons_cons hstep01 (.cons_cons hstep12 (.singleton _))
  have hclosed : ∀ s : ∀ _ : Fin 2, Bool,
      [profTT, profFT, profFF].getLast? = some s →
      ∀ s', ¬ IsStrictBetterResponse testCost s s' := by
    intro s hs s'
    have hred : [profTT, profFT, profFF].getLast? = some profFF := rfl
    rw [hred] at hs
    obtain rfl := Option.some_inj.mp hs
    rintro ⟨i, a, rfl, hlt⟩
    have e0 : testCost i profFF = 0 := by
      norm_num [testCost, hFF0, hFF1]
    have enn : (0 : ℝ) ≤ testCost i (Function.update profFF i a) := by
      unfold testCost
      split_ifs <;> norm_num
    linarith
  exact ⟨List.cons_ne_nil _ _, hchain, hclosed⟩

/-- A maximal two-step improvement path ends at a pure Nash equilibrium. -/
theorem test_maximal_two_step_path_is_nash :
    IsPureNash testCost profFF :=
  maximal_improvement_path_ends_at_nash test_two_step_path_is_maximal rfl

/-- Maximality alone supplies the endpoint: the last profile of the
maximal path, `profFF`, is a pure Nash equilibrium. -/
theorem test_maximal_path_last_is_nash :
    IsPureNash testCost profFF :=
  maximal_improvement_path_last_is_nash test_two_step_path_is_maximal

/-- Improvement paths are `List.IsChain`, so its API applies directly:
dropping the first profile of the maximal path leaves an improvement path. -/
theorem test_isChain_api :
    IsImprovementPath testCost [profFT, profFF] :=
  (List.isChain_cons_cons.mp test_two_step_path_is_maximal.2.1).2

/-- The one-step prefix path is a valid improvement path that is
extendable by a strict better-response step, hence not maximal, and its
last profile is not Nash: maximality is load-bearing for the termination
theorem. -/
theorem test_prefix_extendable_not_nash :
    IsImprovementPath testCost [profTT, profFT] ∧
    IsStrictBetterResponse testCost profFT profFF ∧
    ¬ IsMaximalImprovementPath testCost [profTT, profFT] ∧
    ¬ IsPureNash testCost profFT := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  have hcost01 : testCost 0 profFT < testCost 0 profTT := by
    norm_num [testCost, profTT, hFT0, hFT1]
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hFF0 : profFF (0 : Fin 2) = false := by
    simp [profFF, profFT, hne01]
  have hFF1 : profFF (1 : Fin 2) = false := by simp [profFF, profFT]
  have hcost12 : testCost 1 profFF < testCost 1 profFT := by
    norm_num [testCost, hFT0, hFT1, hFF0, hFF1]
  have hchain : IsImprovementPath testCost [profTT, profFT] :=
    .cons_cons ⟨0, false, rfl, hcost01⟩ (.singleton _)
  have hstep : IsStrictBetterResponse testCost profFT profFF :=
    ⟨1, false, rfl, hcost12⟩
  refine ⟨hchain, hstep, fun hmax => hmax.2.2 profFT rfl profFF hstep, ?_⟩
  intro hNash
  have hle : testCost 1 profFT ≤ testCost 1 profFF := hNash 1 false
  linarith

/-- The empty list is a (trivial) improvement path but has no last
profile, so it is not maximal. -/
theorem test_empty_path_not_maximal :
    IsImprovementPath testCost [] ∧ ¬ IsMaximalImprovementPath testCost [] :=
  ⟨List.IsChain.nil, fun hmax => hmax.1 rfl⟩

end MathlibExtTest.GameTheory.PotentialGamesImprovement
