/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TotalSupportBalancing

/-! Tests for symmetric balancing under total support: the swap matrix `!![0, 1; 1, 0]` has
zero entries but total support, so it can be balanced (by many vectors); the matrix
`!![1, 1; 1, 0]` lacks total support and cannot be balanced; the zero matrix is excluded. -/

open Matrix

namespace MathlibExtTest.Biology.Dynamics.TotalSupportBalancing

open MathlibExt.Biology.Dynamics.SystemsBiology

/-- The swap matrix: symmetric, nonnegative, not positive. -/
def swapM : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem swapM_isSymm : swapM.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

theorem swapM_nonneg : ∀ i j, 0 ≤ swapM i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [swapM]

/-- The swap matrix has total support: both positive entries lie on the transposition. -/
theorem hasTotalSupport_swapM : HasTotalSupport swapM := by
  refine ⟨fun h => by simpa [swapM] using congrFun (congrFun h 0) 1, fun i j hij => ?_⟩
  refine ⟨Equiv.swap 0 1, ?_, fun k => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [swapM]
  · fin_cases k <;> simp [swapM]

/-- Hence a balancing exists (non-vacuity of the sufficiency theorem with zero entries). -/
example : ∃ d : Fin 2 → ℝ, (∀ i, 0 < d i) ∧
    (fun i j => d i * swapM i j * d j) ∈ doublyStochastic ℝ (Fin 2) :=
  exists_symmetric_balancing_of_hasTotalSupport swapM_isSymm swapM_nonneg hasTotalSupport_swapM

/-- The balancing is not unique without positivity: `d = (2, 1/2)` also balances `swapM`. -/
example : (fun i j => (![2, 1 / 2] : Fin 2 → ℝ) i * swapM i j * (![2, 1 / 2] : Fin 2 → ℝ) j) ∈
    doublyStochastic ℝ (Fin 2) := by
  refine mem_doublyStochastic_iff_sum.2 ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [swapM]
  · fin_cases i <;> norm_num [swapM, Fin.sum_univ_two]
  · fin_cases j <;> norm_num [swapM, Fin.sum_univ_two]

/-- `!![1, 1; 1, 0]` lacks total support: the entry `(0, 0)` lies on no positive diagonal,
since the identity uses the zero entry `(1, 1)`. By the Csima–Datta theorem it cannot be
balanced. -/
example : ¬ ∃ d : Fin 2 → ℝ, (∀ i, 0 < d i) ∧
    (fun i j => d i * (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j * d j) ∈
      doublyStochastic ℝ (Fin 2) := by
  rw [exists_symmetric_balancing_iff_hasTotalSupport (by norm_num)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp)]
  rintro ⟨-, hts⟩
  obtain ⟨σ, hσ, hpos⟩ := hts 0 0 (by simp)
  have h1 : σ 1 = 1 := by
    have hinj := σ.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
    rw [hσ] at hinj
    revert hinj
    generalize σ 1 = a
    fin_cases a <;> simp
  have := hpos 1
  rw [h1] at this
  simp at this

/-- Boundary case: the zero matrix (`n = 2`) has no total support, and no balancing. -/
example : ¬ ∃ d : Fin 2 → ℝ, (∀ i, 0 < d i) ∧
    (fun i j => d i * (0 : Matrix (Fin 2) (Fin 2) ℝ) i j * d j) ∈ doublyStochastic ℝ (Fin 2) := by
  rw [exists_symmetric_balancing_iff_hasTotalSupport (by norm_num) (by simp) (by simp)]
  exact fun h => h.1 rfl

#print axioms exists_symmetric_balancing_of_hasTotalSupport
#print axioms exists_symmetric_balancing_iff_hasTotalSupport

end MathlibExtTest.Biology.Dynamics.TotalSupportBalancing
