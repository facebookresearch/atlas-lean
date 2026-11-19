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


example {k r : ℕ} {T : P} (S : Fin (k + 1) → P) (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R)
    (hrank : (qpAdmSourceMatrix μ p S R).rank ≠ k) :
    ∃ d : Fin k → ℝ, d ≠ 0 ∧ ∀ s : ℝ,
      qpAdmSourceMatrix μ p S R *ᵥ (w + s • d) = qpAdmTargetVector μ p T S R :=
  exists_line_of_rank_ne S R hw hrank

example {k r : ℕ} {T : P} (S : Fin (k + 1) → P) (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R) (v : Fin k → ℝ) :
    MathlibExt.Biology.PopulationGenetics.QpGraph.scoreS1 1 (qpAdmTargetVector μ p T S R)
        (qpAdmSourceMatrix μ p S R *ᵥ v) ≤
      MathlibExt.Biology.PopulationGenetics.QpGraph.scoreS1 1 (qpAdmTargetVector μ p T S R)
        (qpAdmSourceMatrix μ p S R *ᵥ w) :=
  qpAdm_weights_maximize_scoreS1_one S R hw v

-- `k = 0`: no unknown weights; rank condition and uniqueness are automatic.
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}
    {r : ℕ} {T : P} (S : Fin (0 + 1) → P) (R : Fin (r + 1) → P)
    (_h : qpAdmSourceMatrix μ p S R *ᵥ (0 : Fin 0 → ℝ) = qpAdmTargetVector μ p T S R) :
    ∀ v : Fin 0 → ℝ, qpAdmSourceMatrix μ p S R *ᵥ v = qpAdmTargetVector μ p T S R →
      v = 0 := by
  intro v _
  exact Subsingleton.elim _ _

-- Acceptance (negative qpAdm weight from a valid drift model): one edge of
-- length `1`, populations `T,S0,S1,R0,R1 = 0,1,2,3,4 : ℕ` with lineage
-- weights `1/2, 3/10, 1/10, 0, 1/2 ∈ [0,1]`, so the realized frequencies
-- are `1, 4/5, 3/5, 1/2, 1 ∈ [0,1]`. The qpAdm equation is
-- `1/10 = w₁ * (-1/10)`; the affine representation of `T` has weights
-- `(2,-1)`, so `w₁ = -1 < 0` and `w₀ = 2 > 1` even though every lineage
-- weight and allele frequency is a genuine probability.
example :
    ∃ M : DriftModel Measure.count Unit ℕ,
      (∀ X : ℕ, ∀ ω : Unit, M.freq X ω = 1 / 2 + [(1 / 2 : ℝ), 3 / 10, 1 / 10, 0, 1 / 2].getD X 0) ∧
      M.freq 0 () = 1 ∧ M.freq 1 () = 4 / 5 ∧ M.freq 2 () = 3 / 5 ∧
        M.freq 3 () = 1 / 2 ∧ M.freq 4 () = 1 ∧
      qpAdmTargetVector Measure.count M.freq 0 ![1, 2] ![3, 4] = ![1 / 10] ∧
      qpAdmSourceMatrix Measure.count M.freq ![1, 2] ![3, 4] = ![![-1 / 10]] ∧
      (∀ ω, M.freq 0 ω = (2 : ℝ) * M.freq 1 ω + (-1 : ℝ) * M.freq 2 ω) := by
  classical
  refine ⟨DriftModel.ofLen (fun X _ => [(1 / 2 : ℝ), 3 / 10, 1 / 10, 0, 1 / 2].getD X 0)
    (fun _ => (1 : ℝ)) (fun _ => by norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X ω
    obtain rfl : ω = () := Subsingleton.elim ω ()
    simp [DriftModel.freq, DriftModel.ofLen]
  · norm_num [DriftModel.freq, DriftModel.ofLen]
  · norm_num [DriftModel.freq, DriftModel.ofLen]
  · norm_num [DriftModel.freq, DriftModel.ofLen]
  · norm_num [DriftModel.freq, DriftModel.ofLen]
  · norm_num [DriftModel.freq, DriftModel.ofLen]
  · funext j
    fin_cases j
    simp only [qpAdmTargetVector, Matrix.cons_val_zero]
    rw [DriftModel.f4_freq]
    simp [DriftModel.ofLen, Matrix.cons_val_one]
    norm_num
  · ext i j
    fin_cases i
    fin_cases j
    simp only [qpAdmSourceMatrix, Matrix.of_apply, Matrix.cons_val_zero]
    rw [DriftModel.f4_freq]
    simp [DriftModel.ofLen, Matrix.cons_val_one]
    norm_num
  · intro ω
    obtain rfl : ω = () := Subsingleton.elim ω ()
    norm_num [DriftModel.freq, DriftModel.ofLen]

-- Concrete rank-deficient system: repeating the right reference population
-- makes the source matrix and target vector zero, so the solution `w = 0`
-- extends to a nontrivial line of solutions.
example :
    ∃ d : Fin 1 → ℝ, d ≠ 0 ∧ ∀ s : ℝ,
      qpAdmSourceMatrix Measure.count
          (DriftModel.ofLen (fun X (_ : Unit) => [(1 / 2 : ℝ), 3 / 10, 1 / 10, 0, 1 / 2].getD X 0) (fun _ => (1 : ℝ))
            (fun _ => by norm_num)).freq ![1, 2] ![3, 3] *ᵥ
            ((0 : Fin 1 → ℝ) + s • d) =
        qpAdmTargetVector Measure.count
          (DriftModel.ofLen (fun X (_ : Unit) => [(1 / 2 : ℝ), 3 / 10, 1 / 10, 0, 1 / 2].getD X 0) (fun _ => (1 : ℝ))
            (fun _ => by norm_num)).freq 0 ![1, 2] ![3, 3] := by
  classical
  set M := DriftModel.ofLen (fun X (_ : Unit) => [(1 / 2 : ℝ), 3 / 10, 1 / 10, 0, 1 / 2].getD X 0) (fun _ => (1 : ℝ))
    (fun _ => by norm_num) with hM
  have hsrc : qpAdmSourceMatrix Measure.count M.freq ![1, 2] ![3, 3] = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [qpAdmSourceMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.zero_apply]
    rw [DriftModel.f4_freq]
    simp [hM, DriftModel.ofLen]
  have htgt : qpAdmTargetVector Measure.count M.freq 0 ![1, 2] ![3, 3] = 0 := by
    funext j
    fin_cases j
    simp only [qpAdmTargetVector, Matrix.cons_val_zero, Pi.zero_apply]
    rw [DriftModel.f4_freq]
    simp [hM, DriftModel.ofLen]
  have hrank : (qpAdmSourceMatrix Measure.count M.freq ![1, 2] ![3, 3]).rank ≠ 1 := by
    rw [hsrc]
    simp
  refine ⟨![1], ?_, fun s => ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · rw [hsrc, htgt]
    simp

end MathlibExtTest.Biology.PopulationGenetics.Admixture.QpAdmWeights
