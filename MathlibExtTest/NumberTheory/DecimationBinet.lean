/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DecimationBinet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Tests for the Binet formula for decimated linear recurrences
-/

open MetaMathlibExt Polynomial

-- With roots 0 and 2, only the second initial term of each residue class
-- contributes after the first stride.
example (s : ℕ → ℂ) (hs : ∀ n, s (n + 4) = 2 * s (n + 2)) (q i : ℕ) (hi : i < 2) :
    s ((q + 1) * 2 + i) = 2 ^ q * s (2 + i) := by
  let A (j : ℕ) : ℂ := if j = 1 then 2 else 0
  let α (t : Fin 2) : ℂ := if t = 0 then 0 else 2
  have hα : Function.Injective α := by
    intro a b h
    fin_cases a <;> fin_cases b <;> norm_num [α] at *
  have hroot (t : Fin 2) :
      (X ^ 2 - ∑ j ∈ Finset.range 2, C (A j) * X ^ j : ℂ[X]).eval (α t) = 0 := by
    fin_cases t <;> norm_num [A, α, Finset.sum_range_succ]
  have h := decimation_binet (m := 2) (r := 2) (s := s)
    (by simpa [A, Finset.sum_range_succ] using hs) hα hroot ((q + 1) * 2 + i)
  have hmod : ((q + 1) * 2 + i) % 2 = i := by omega
  have hdiv : ((q + 1) * 2 + i) / 2 = q + 1 := by omega
  norm_num [hmod, hdiv, A, α, decimationCoeff, Finset.sum_range_succ, Fin.sum_univ_two,
    derivative_sub, derivative_pow, pow_succ] at h
  rw [h]
  ring

-- At stride zero the initial value is indexed by n itself.
example (s : ℕ → ℂ) (n : ℕ) : s n = decimationCoeff (fun _ ↦ 1) s 1 0 0 n := by
  simpa using decimation_binet (m := 1) (r := 0) (A := fun _ ↦ 1) (s := s)
    (by simp) (α := fun _ ↦ 1) (Function.injective_of_subsingleton _)
    (by simp) n
