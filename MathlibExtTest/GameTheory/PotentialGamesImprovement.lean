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
two-step path that cannot be extended is maximal and ends at a pure Nash
equilibrium, the `List.IsChain` API applies to improvement paths, a
nonempty path that can still be extended is not maximal and its last
profile is not Nash, a singleton path that cannot be extended is maximal
with a Nash endpoint, and the empty path is not maximal.
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

/-- The step `profTT → profFT`: player 0 deviates to `false` and lowers
their cost. -/
theorem test_step_profTT_profFT : IsStrictBetterResponse testCost profTT profFT := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  refine ⟨0, false, rfl, ?_⟩
  norm_num [testCost, profTT, hFT0, hFT1]

/-- The step `profFT → profFF`: player 1 follows to `false` and lowers
their cost. -/
theorem test_step_profFT_profFF : IsStrictBetterResponse testCost profFT profFF := by
  have hFT0 : profFT (0 : Fin 2) = false := by simp [profFT]
  have hne10 : (1 : Fin 2) ≠ 0 := by decide
  have hFT1 : profFT (1 : Fin 2) = true := by simp [profFT, profTT, hne10]
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hFF0 : profFF (0 : Fin 2) = false := by
    simp [profFF, profFT, hne01]
  have hFF1 : profFF (1 : Fin 2) = false := by simp [profFF, profFT]
  refine ⟨1, false, rfl, ?_⟩
  norm_num [testCost, hFT0, hFT1, hFF0, hFF1]

/-- No strict better-response step leaves `profFF`: both costs there are 0,
and every cost is nonnegative. -/
theorem test_no_step_from_profFF (s' : ∀ _ : Fin 2, Bool) :
    ¬ IsStrictBetterResponse testCost profFF s' := by
  have hne01 : (0 : Fin 2) ≠ 1 := by decide
  have hFF0 : profFF (0 : Fin 2) = false := by
    simp [profFF, profFT, hne01]
  have hFF1 : profFF (1 : Fin 2) = false := by simp [profFF, profFT]
  rintro ⟨i, a, rfl, hlt⟩
  have e0 : testCost i profFF = 0 := by
    norm_num [testCost, hFF0, hFF1]
  have enn : (0 : ℝ) ≤ testCost i (Function.update profFF i a) := by
    unfold testCost
    split_ifs <;> norm_num
  linarith

/-- The two-step improvement path `profTT → profFT → profFF` is maximal: by
`List.isChain_append`, extending it by `s'` would need a strict
better-response step from `profFF` to `s'`. -/
theorem test_two_step_path_is_maximal :
    IsMaximalImprovementPath testCost [profTT, profFT, profFF] := by
  refine ⟨List.cons_ne_nil _ _,
    .cons_cons test_step_profTT_profFT (.cons_cons test_step_profFT_profFF (.singleton _)), ?_⟩
  intro s' hext
  exact test_no_step_from_profFF s' ((List.isChain_append.mp hext).2.2 profFF rfl s' rfl)

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

/-- A nonempty improvement path that can still be extended is not maximal:
`[profTT, profFT] ++ [profFF]` is an improvement path. -/
theorem test_extendable_path_not_maximal :
    [profTT, profFT] ≠ [] ∧ IsImprovementPath testCost [profTT, profFT] ∧
    IsImprovementPath testCost ([profTT, profFT] ++ [profFF]) ∧
    ¬ IsMaximalImprovementPath testCost [profTT, profFT] := by
  have hext : IsImprovementPath testCost ([profTT, profFT] ++ [profFF]) :=
    .cons_cons test_step_profTT_profFT (.cons_cons test_step_profFT_profFF (.singleton _))
  exact ⟨List.cons_ne_nil _ _, .cons_cons test_step_profTT_profFT (.singleton _), hext,
    fun hmax => hmax.2.2 profFF hext⟩

/-- The one-step prefix path is a valid improvement path that is
extendable by a strict better-response step, hence not maximal, and its
last profile is not Nash: the termination theorem needs maximality. -/
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
  refine ⟨hchain, hstep, test_extendable_path_not_maximal.2.2.2, ?_⟩
  intro hNash
  have hle : testCost 1 profFT ≤ testCost 1 profFF := hNash 1 false
  linarith

/-- A singleton path that cannot be extended is maximal: `[profFF]` has no
extension, so the endpoint-closure lemma rules out every strict step out of
`profFF`, and the termination theorem shows `profFF` is a pure Nash
equilibrium. -/
theorem test_singleton_maximal_path_is_nash :
    IsMaximalImprovementPath testCost [profFF] ∧
    (∀ s', ¬ IsStrictBetterResponse testCost profFF s') ∧
    IsPureNash testCost profFF := by
  have hmax : IsMaximalImprovementPath testCost [profFF] :=
    ⟨List.cons_ne_nil _ _, .singleton _, fun s' hext =>
      test_no_step_from_profFF s' ((List.isChain_append.mp hext).2.2 profFF rfl s' rfl)⟩
  exact ⟨hmax, hmax.not_isStrictBetterResponse rfl,
    maximal_improvement_path_ends_at_nash hmax rfl⟩

/-- The empty list is a (trivial) improvement path but has no last
profile, so it is not maximal. -/
theorem test_empty_path_not_maximal :
    IsImprovementPath testCost [] ∧ ¬ IsMaximalImprovementPath testCost [] :=
  ⟨List.IsChain.nil, fun hmax => hmax.1 rfl⟩

end MathlibExtTest.GameTheory.PotentialGamesImprovement
