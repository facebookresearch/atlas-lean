/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.CubeCovering
public import MathlibExt.Geometry.Convex.Illumination
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

@[expose] public section

namespace ConvexCoveringTest

open ConvexCovering

abbrev E := EuclideanSpace ℝ (Fin 1)
noncomputable def tip : E := PiLp.single 2 0 (1 : ℝ)
def K : Set E := Metric.closedBall 0 1

lemma tip_norm : ‖tip‖ = 1 := by simp [tip, PiLp.norm_single]
lemma tip_frontier : tip ∈ frontier K := by
  rw [K, frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_sphere]
  simpa [dist_zero_right] using tip_norm

example : DirectionIlluminates K (-tip) tip := by
  refine ⟨tip_frontier, by simpa using tip_norm, 1, by norm_num, ?_⟩
  rw [K, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  simp

example : ExternalPointIlluminates K ((2 : ℝ) • tip) tip := by
  refine ⟨?_, tip_frontier, 2, by norm_num, ?_⟩
  · simp [K, Metric.mem_closedBall, dist_zero_right, norm_smul, tip_norm]
  · rw [K, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    have heq : (2 : ℝ) • tip + (2 : ℝ) • (tip - (2 : ℝ) • tip) = (0 : E) := by module
    simp [heq]

example : ¬ ExternalPointIlluminates K (0 : E) tip := by
  intro h
  exact h.1 (by simp [K])

example : ¬ DirectionIlluminates K (0 : E) tip := by
  intro h
  simpa using h.2.1

example : ¬ DirectionIlluminates K tip tip := by
  rintro ⟨_, _, t, ht, hi⟩
  have heq : tip + t • tip = (1 + t) • tip := by module
  rw [K, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_ball,
    dist_zero_right, heq, norm_smul, tip_norm, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 1 + t), mul_one] at hi
  linarith

example : IsAffineCube (coordinateCube 3) := by
  refine ⟨AffineEquiv.refl ℝ _, ?_⟩
  simp

example : CoveredBySmallerPositiveHomothets (∅ : Set E) 0 := by
  refine ⟨Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · simp

example : ¬ CoveredBySmallerPositiveHomothets (Set.univ : Set E) 0 := by
  rintro ⟨_, _, _, h⟩
  obtain ⟨i, _⟩ := h 0 (by simp)
  exact Fin.elim0 i

example : IsConvexBody (coordinateCube 0) := coordinateCube_isConvexBody 0
example : IsConvexBody (coordinateCube 3) := coordinateCube_isConvexBody 3
example : IsCentrallySymmetric (coordinateCube 3) := coordinateCube_isCentrallySymmetric 3

example : ¬ CoveredByInteriorTranslates (coordinateCube 3) 7 := by
  intro h
  have hbound := coordinateCube_coveringCount_ge_two_pow h
  norm_num at hbound

example : ¬ UniformInteriorTranslateBound 3 7 := by
  intro h
  have hbound := cubeLowerBound 7 h
  norm_num at hbound

example : ¬ UniformSymmetricInteriorTranslateBound 3 7 := by
  intro h
  have hbound := symmetricInteriorTranslateBound_ge_two_pow h
  norm_num at hbound

example : ∃ B : Set (EuclideanSpace ℝ (Fin 3)), IsConvexBody B ∧ IsCentrallySymmetric B ∧
    CoveredByInteriorTranslates B 8 ∧
    IsLeast {q : ℕ | CoveredByInteriorTranslates B q} 8 ∧
    translateCoveringNumber B (interior B) = (8 : WithTop ℕ) :=
  ⟨coordinateCube 3, coordinateCube_isConvexBody 3, coordinateCube_isCentrallySymmetric 3,
    coordinateCube_three_coveredByInteriorTranslates, coordinateCube_three_least_coveringCount,
    coordinateCube_three_translateCoveringNumber⟩

example : CoveredByTranslates (∅ : Set E) ({0} : Set E) 0 := by
  exact ⟨Fin.elim0, by simp⟩

example : translateCoveringNumber ({0} : Set E) ∅ = (⊤ : WithTop ℕ) := by
  have hnone : ∀ q : ℕ, ¬ CoveredByTranslates ({0} : Set E) ∅ q := by
    intro q
    rintro ⟨_, h⟩
    have hx := h (by simp : (0 : E) ∈ ({0} : Set E))
    simp at hx
  have hset : {q : ℕ | CoveredByTranslates ({0} : Set E) ∅ q} = ∅ := by
    ext q
    simp [hnone q]
  simp [translateCoveringNumber, hset]

#eval IO.println "C39SUPPORTED_BOUNDARY: actual eight-translate cube/minimum/value, ray directions and finite/empty guards"

end ConvexCoveringTest
