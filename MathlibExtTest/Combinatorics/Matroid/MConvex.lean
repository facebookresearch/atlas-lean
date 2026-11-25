/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.MConvex
import Mathlib.Tactic.FinCases

namespace MConvexTest

open MathlibExt.Combinatorics.Matroid.MConvex

/-! Indicator vectors evaluate as expected. -/

example : indicatorVec ({0, 2} : Finset (Fin 3)) 2 = 1 := by
  simp [indicatorVec_apply]

example : indicatorVec ({0, 2} : Finset (Fin 3)) 1 = 0 := by
  simp [indicatorVec_apply]

/-! The predicate is not vacuous: two disjoint pairs do not form an M-convex set (they are not
the bases of a matroid). -/

example : ¬ IsMConvex ({indicatorVec {0, 1}, indicatorVec {2, 3}} : Set (Fin 4 →₀ ℕ)) := by
  intro h
  obtain ⟨j, hj, hmem⟩ := h _ (Or.inl rfl) _ (Or.inr rfl) 0 (by simp [indicatorVec_apply])
  fin_cases j
  all_goals simp [indicatorVec_apply] at hj
  all_goals
    rcases hmem with h | h
    · have := DFunLike.congr_fun h 0
      simp [indicatorVec_apply] at this
    · have := DFunLike.congr_fun h 1
      simp [indicatorVec_apply] at this

/-! The bases of any matroid give an M-convex set. -/

example (M : Matroid (Fin 3)) : IsMConvex (baseVectors M) :=
  isMConvex_baseVectors M

/-! The two singletons of `Fin 2` form an M-convex set, hence the bases of a matroid (the
uniform matroid `U_{1,2}`). -/

theorem singletons_isMConvex :
    IsMConvex ({indicatorVec {0}, indicatorVec {1}} : Set (Fin 2 →₀ ℕ)) := by
  have e01 : indicatorVec ({0} : Finset (Fin 2)) - Finsupp.single 0 1 + Finsupp.single 1 1 =
      indicatorVec {1} := by
    rw [indicatorVec_exchange (by simp) (by simp)]
    rfl
  have e10 : indicatorVec ({1} : Finset (Fin 2)) - Finsupp.single 1 1 + Finsupp.single 0 1 =
      indicatorVec {0} := by
    rw [indicatorVec_exchange (by simp) (by simp)]
    rfl
  rintro α (rfl | rfl) β (rfl | rfl) i hi
  · fin_cases i <;> simp [indicatorVec_apply] at hi
  · fin_cases i
    · exact ⟨1, by simp [indicatorVec_apply], Or.inr e01⟩
    · simp [indicatorVec_apply] at hi
  · fin_cases i
    · simp [indicatorVec_apply] at hi
    · exact ⟨0, by simp [indicatorVec_apply], Or.inl e10⟩
  · fin_cases i <;> simp [indicatorVec_apply] at hi

example : ∃ M : Matroid (Fin 2), M.E = Set.univ ∧
    baseVectors M = ({indicatorVec {0}, indicatorVec {1}} : Set (Fin 2 →₀ ℕ)) := by
  refine exists_matroid_baseVectors_eq ⟨_, Or.inl rfl⟩ ?_ singletons_isMConvex
  rintro α (rfl | rfl) i <;> fin_cases i <;> simp [indicatorVec_apply]

end MConvexTest
