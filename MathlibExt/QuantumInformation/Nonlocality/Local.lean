/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Introduced by Avocado; upstream author line credits
Tsutomu Okano (@toskua) and Avocado; ported with attribution.
-/

module

public import MathlibExt.QuantumInformation.Nonlocality.Scenario
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Local Bell behaviors as finite convex mixtures

Finite convex mixtures of deterministic response functions for uniform Bell scenarios.
Defines the mixture behavior construction from `Convexity.StdSimplex` weights over
deterministic responses, defines locality by existence of such weights, and proves
deterministic behaviors are local via single point-mass weights. Includes the core
probability formula.
-/

@[expose] public section

open Finset BigOperators

namespace QuantumInformation
namespace Nonlocality

namespace BellScenario

/-- Finite convex mixture of deterministic behaviors weighted by `Convexity.StdSimplex`
weights over deterministic responses. -/
noncomputable def mixtureBehavior (S : BellScenario)
    (weights : Convexity.StdSimplex ℝ S.DeterministicResponse) : Behavior S where
  prob x y :=
    ∑ f : S.DeterministicResponse, weights.weights f * (deterministicBehavior S f).prob x y
  nonneg x y := by
    apply Finset.sum_nonneg
    intro f _
    apply mul_nonneg
    · exact weights.weights_nonneg f
    · exact (deterministicBehavior S f).nonneg x y
  normalized x := by
    calc
      ∑ y : S.OutcomeAssignment, ∑ f : S.DeterministicResponse,
          weights.weights f * (deterministicBehavior S f).prob x y
        = ∑ f : S.DeterministicResponse, ∑ y : S.OutcomeAssignment,
            weights.weights f * (deterministicBehavior S f).prob x y := by
          rw [Finset.sum_comm]
      _ = ∑ f : S.DeterministicResponse, weights.weights f *
            ∑ y : S.OutcomeAssignment, (deterministicBehavior S f).prob x y := by
          congr 1
          ext f
          rw [Finset.mul_sum]
      _ = ∑ f : S.DeterministicResponse, weights.weights f * 1 := by
          congr 1
          ext f
          rw [(deterministicBehavior S f).normalized]
      _ = ∑ f : S.DeterministicResponse, weights.weights f := by simp
      _ = 1 := weights.total_of_fintype

/-- Probability formula for the mixture behavior. -/
theorem mixtureBehavior_prob (S : BellScenario)
    (weights : Convexity.StdSimplex ℝ S.DeterministicResponse)
    (x : S.SettingAssignment) (y : S.OutcomeAssignment) :
    (mixtureBehavior S weights).prob x y =
      ∑ f : S.DeterministicResponse, weights.weights f * (deterministicBehavior S f).prob x y :=
  rfl

/-- A behavior is local iff it equals a finite convex mixture of deterministic behaviors. -/
def IsLocal (S : BellScenario) (B : Behavior S) : Prop :=
  ∃ weights : Convexity.StdSimplex ℝ S.DeterministicResponse,
    B = mixtureBehavior S weights

/-- Every deterministic behavior is local via single point-mass weight. -/
theorem deterministic_isLocal (S : BellScenario) (f : S.DeterministicResponse) :
    IsLocal S (deterministicBehavior S f) := by
  refine ⟨Convexity.StdSimplex.single (R := ℝ) f, ?_⟩
  apply Behavior.ext
  intro x y
  simp only [mixtureBehavior_prob, deterministicBehavior_prob]
  have hweight : ∀ g : S.DeterministicResponse,
      (Convexity.StdSimplex.single (R := ℝ) f).weights g =
        if g = f then 1 else 0 := by
    intro g
    by_cases hg : g = f
    · simp [hg, Convexity.StdSimplex.weights_single, Finsupp.single_eq_same]
    · simp [hg, Convexity.StdSimplex.weights_single, Finsupp.single_eq_of_ne]
  simp_rw [hweight]
  symm
  calc
    ∑ g : S.DeterministicResponse,
        (if g = f then (1 : ℝ) else 0) *
          (if y = S.responseToOutcome g x then 1 else 0)
      = ∑ g ∈ (Finset.univ : Finset S.DeterministicResponse),
          if g = f then
            (if y = S.responseToOutcome g x then (1 : ℝ) else 0)
          else 0 := by
        congr 1
        ext g
        by_cases hg : g = f <;> simp [hg]
    _ = if y = S.responseToOutcome f x then (1 : ℝ) else 0 := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end BellScenario

end Nonlocality
end QuantumInformation
