/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Admixture.QpAdmWeights
import MathlibExt.Biology.PopulationGenetics.Admixture.GeneralGraph
import MathlibExt.Biology.PopulationGenetics.Admixture.LinearIdentifiability

/-! Tests for qpAdm weight identifiability: the model equation inputs, generic
restatements, the `k = 0` endpoint, and a concrete negative-weight drift
example. -/

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.QpAdmWeights

open MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

example (hp : ∀ X, MemLp (p X) 2 μ) {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) (w : Fin (k + 1) → ℝ) (hw : ∑ l, w l = 1)
    (hT : ∀ ω, p T ω = ∑ l, w l * p (S l) ω) :
    qpAdmTargetVector μ p T S R =
      qpAdmSourceMatrix μ p S R *ᵥ (fun l : Fin k => w l.succ) :=
  qpAdmTargetVector_eq_qpAdmSourceMatrix_mulVec hp S R w hw hT

example {k r : ℕ} {T : P} (S : Fin (k + 1) → P) (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R) :
    (∀ v : Fin k → ℝ, qpAdmSourceMatrix μ p S R *ᵥ v = qpAdmTargetVector μ p T S R →
      v = w) ↔ (qpAdmSourceMatrix μ p S R).rank = k :=
  qpAdm_unique_iff_rank_eq S R hw

example {k r : ℕ} {T : P} (S : Fin (k + 1) → P) (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R)
    (hrank : (qpAdmSourceMatrix μ p S R).rank = k) :
    w = ((qpAdmSourceMatrix μ p S R)ᵀ * qpAdmSourceMatrix μ p S R)⁻¹ *ᵥ
      ((qpAdmSourceMatrix μ p S R)ᵀ *ᵥ qpAdmTargetVector μ p T S R) :=
  qpAdm_weights_eq_inv_gram_mulVec S R hw hrank


-- `k = 0`: no unknown weights; rank condition and uniqueness are automatic.
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}
    {r : ℕ} {T : P} (S : Fin (0 + 1) → P) (R : Fin (r + 1) → P)
    (_h : qpAdmSourceMatrix μ p S R *ᵥ (0 : Fin 0 → ℝ) = qpAdmTargetVector μ p T S R) :
    ∀ v : Fin 0 → ℝ, qpAdmSourceMatrix μ p S R *ᵥ v = qpAdmTargetVector μ p T S R →
      v = 0 := by
  intro v _
  exact Subsingleton.elim _ _

-- Acceptance (negative weight, realized in a drift model): one edge, populations
-- `T,S0,S1,R0,R1 = 0,1,2,3,4 : ℕ` with weights `-1,0,1,0,1` and `len = 1`. Then
-- the qpAdm equation is `-1 = w₁ * 1`; the affine representation of `T` has
-- weights `(2,-1)`, so `w₁ = -1 < 0` and `w₀ = 2 > 1`.
example :
    ∃ M : DriftModel Measure.count Unit ℕ,
      (∀ X : ℕ, ∀ ω : Unit, M.freq X ω = 1 / 2 + [(-1 : ℝ), 0, 1, 0, 1].getD X 0) ∧
      qpAdmTargetVector Measure.count M.freq 0 ![1, 2] ![3, 4] = ![-1] ∧
      qpAdmSourceMatrix Measure.count M.freq ![1, 2] ![3, 4] = ![![1]] ∧
      (∀ ω, M.freq 0 ω = (2 : ℝ) * M.freq 1 ω + (-1 : ℝ) * M.freq 2 ω) := by
  classical
  refine ⟨DriftModel.ofLen (fun X _ => [(-1 : ℝ), 0, 1, 0, 1].getD X 0)
    (fun _ => (1 : ℝ)) (fun _ => by norm_num), ?_, ?_, ?_, ?_⟩
  · intro X ω
    obtain rfl : ω = () := Subsingleton.elim ω ()
    simp [DriftModel.freq, DriftModel.ofLen]
  · funext j
    fin_cases j
    simp only [qpAdmTargetVector, Matrix.cons_val_zero]
    rw [DriftModel.f4_freq]
    simp [DriftModel.ofLen, Matrix.cons_val_one]
  · ext i j
    fin_cases i
    fin_cases j
    simp only [qpAdmSourceMatrix, Matrix.of_apply, Matrix.cons_val_zero]
    rw [DriftModel.f4_freq]
    simp [DriftModel.ofLen, Matrix.cons_val_one]
  · intro ω
    obtain rfl : ω = () := Subsingleton.elim ω ()
    norm_num [DriftModel.freq, DriftModel.ofLen]

end MathlibExtTest.Biology.PopulationGenetics.Admixture.QpAdmWeights
