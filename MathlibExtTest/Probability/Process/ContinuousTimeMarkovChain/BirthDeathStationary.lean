/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.BirthDeathStationary
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.BirthDeathStationary

private def twoStateQ (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-a, a; 2, -2]

private theorem twoStateQ_isRateMatrix {a : ℝ} (ha : 0 ≤ a) : IsRateMatrix (twoStateQ a) := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [twoStateQ, ha] at *
  · intro i
    fin_cases i <;> simp [twoStateQ, Fin.sum_univ_two]

private theorem twoStateQ_band (a : ℝ) (i j : Fin 2) (h : i ≠ j)
    (hf : i.val + 1 ≠ j.val) (hb : j.val + 1 ≠ i.val) : twoStateQ a i j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at *

private theorem twoStateQ_death (a : ℝ) (k : Fin 1) :
    0 < twoStateQ a k.succ k.castSucc := by
  fin_cases k
  norm_num [twoStateQ]

-- With rates 1 and 2, every stationary probability vector is (2/3, 1/3).
example (ρ : Fin 2 → ℝ) (hn : ∀ i, 0 ≤ ρ i) (hs : ∑ i, ρ i = 1)
    (hρ : ρ ᵥ* twoStateQ 1 = 0) : ρ = ![2 / 3, 1 / 3] := by
  have h := finite_birth_death_stationary_law (twoStateQ_isRateMatrix (a := 1) (by norm_num))
    (twoStateQ_band 1) (twoStateQ_death 1)
  have he := (h.2.2.1 ρ).mp ⟨hn, hs, hρ⟩
  rw [he]
  have hw₀ : finiteBirthDeathWeight (twoStateQ 1) 0 = 1 := by
    simp [finiteBirthDeathWeight]
  have hu : (univ : Finset (Fin 1)) = {0} := by decide
  have hw₁ : finiteBirthDeathWeight (twoStateQ 1) 1 = 1 / 2 := by
    norm_num [finiteBirthDeathWeight, hu, twoStateQ]
  have hsum : ∑ j, finiteBirthDeathWeight (twoStateQ 1) j = 1 + 1 / 2 := by
    rw [Fin.sum_univ_two, hw₀, hw₁]
  funext i
  rw [hsum]
  fin_cases i <;> norm_num [hw₀, hw₁]

-- A vanishing upward rate makes state 1 have zero weight and zero probability.
example : finiteBirthDeathWeight (twoStateQ 0) 1 = 0 ∧
    finiteBirthDeathWeight (twoStateQ 0) 1 / ∑ j, finiteBirthDeathWeight (twoStateQ 0) j = 0 := by
  have h := finite_birth_death_stationary_law (twoStateQ_isRateMatrix (a := 0) (by norm_num))
    (twoStateQ_band 0) (twoStateQ_death 0)
  exact h.2.2.2 0 (by simp [twoStateQ]) 1 (by decide)

-- The singleton case has no death-rate hypothesis to discharge and has probability one at 0.
example (ρ : Fin 1 → ℝ) :
    ((∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1 ∧ ρ ᵥ* (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0) ↔
      ρ = fun _ => 1 := by
  have hr : IsRateMatrix (0 : Matrix (Fin 1) (Fin 1) ℝ) :=
    ⟨fun _ => by simp, fun _ => by simp⟩
  have h := (finite_birth_death_stationary_law (K := 0) hr (fun _ _ _ _ _ => rfl)
    (fun k => Fin.elim0 k)).2.2.1 ρ
  have he : (fun i : Fin 1 => finiteBirthDeathWeight (0 : Matrix (Fin 1) (Fin 1) ℝ) i /
      ∑ j, finiteBirthDeathWeight (0 : Matrix (Fin 1) (Fin 1) ℝ) j) = fun _ => 1 := by
    funext i
    fin_cases i
    simp [finiteBirthDeathWeight]
  simpa only [he] using h

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.BirthDeathStationary
