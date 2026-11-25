/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Admixture.QpWaveFactorization
import Domains.Biology.PopulationGenetics.Admixture.LinearIdentifiability

/-! Tests for the drift-model factorization of qpWave f4 matrices: generic
restatements, the no-edge bound, and an uninformative-right-set example with a
nonzero left contrast. -/

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.QpWaveFactorization

example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E] [DecidableEq E]
    (M : DriftModel μ E P) {n r : ℕ} (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    ADMIXTOOLS.f4Matrix μ M.freq L R =
      M.contrastMatrix L * Matrix.diagonal M.len * (M.contrastMatrix R)ᵀ :=
  M.f4Matrix_eq_contrast_mul_diagonal_mul_transpose L R

example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) {n r : ℕ} (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤
      Nat.card {e : E // (∃ i, M.contrastMatrix L i e ≠ 0) ∧
        ∃ j, M.contrastMatrix R j e ≠ 0} :=
  M.rank_f4Matrix_le_support L R

example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) {n r : ℕ} (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤ (M.contrastMatrix R).rank :=
  M.rank_f4Matrix_le_rank_contrast_right L R

example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) {n r : ℕ} (L : Fin (n + 1) → P) (R : Fin (r + 1) → P)
    (hR : ∀ (j : Fin r) (e : E), M.weight (R j.succ) e = M.weight (R 0) e) :
    ADMIXTOOLS.f4Matrix μ M.freq L R = 0 :=
  M.f4Matrix_eq_zero_of_weight_right_succ_eq L R hR

-- No edges: rank bound is `0` (the matrix is over `Fin n × Fin r`).
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {n r : ℕ}
    (M : DriftModel μ Empty P) (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    (ADMIXTOOLS.f4Matrix μ M.freq L R).rank ≤ 0 := by
  have h := M.rank_f4Matrix_le_support L R
  simpa using h

-- Acceptance: left contrast nonzero (admixture-side difference present) but the right
-- set has a repeated reference population, so every right contrast vanishes and `F = 0`.
-- Realized by `DriftModel.ofLen` on one edge: populations `0,1,2` have weights `0,1,0`.
example :
    let w : Fin 3 → Unit → ℝ := ![fun _ => 0, fun _ => 1, fun _ => 0]
    let M := DriftModel.ofLen w (fun _ => (1 : ℝ)) (fun _ => by norm_num)
    M.contrastMatrix ![0, 1] 0 () ≠ 0 ∧
      ADMIXTOOLS.f4Matrix Measure.count M.freq ![0, 1] ![2, 2] = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · simp [DriftModel.contrastMatrix, DriftModel.ofLen]
  · apply DriftModel.f4Matrix_eq_zero_of_weight_right_succ_eq
    intro j e
    fin_cases j
    simp [DriftModel.ofLen]

end MathlibExtTest.Biology.PopulationGenetics.Admixture.QpWaveFactorization
