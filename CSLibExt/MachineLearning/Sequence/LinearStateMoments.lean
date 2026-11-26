/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CovarianceMatrix
import MathlibExt.Probability.CovarianceLinearMap
import Mathlib.Tactic.Ring

/-! # Mean and covariance of a linear state with uncorrelated noise -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix
open MathlibExt.Probability.Finance.PortfolioVariance (covMatrix)

namespace Cslib.MachineLearning.Sequence.LinearStateMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {n m : ℕ}

/-- State of the linear system after `k` updates with deterministic input `u` and noise `w`.
The update at index `k` takes the state from index `k` to `k + 1`. -/
def state (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (u : ℕ → Fin m → ℝ) (x₀ : Ω → Fin n → ℝ) (w : ℕ → Ω → Fin n → ℝ) :
    ℕ → Ω → Fin n → ℝ
  | 0 => x₀
  | k + 1 => fun ω => A *ᵥ state A B u x₀ w k ω + B *ᵥ u k + w k ω

omit [IsProbabilityMeasure P] in
private theorem memLp_mulVec (A : Matrix (Fin n) (Fin n) ℝ) {x : Ω → Fin n → ℝ}
    (hx : ∀ i, MemLp (fun ω => x ω i) 2 P) (i : Fin n) :
    MemLp (fun ω => (A *ᵥ x ω) i) 2 P := by
  simpa only [Matrix.mulVec, dotProduct] using
    (memLp_finsetSum Finset.univ (f := fun j ω => A i j * x ω j)
      (fun j _ => (hx j).const_mul (A i j)))

private theorem cov_mulVec_eq_zero (A : Matrix (Fin n) (Fin n) ℝ) {x : Ω → Fin n → ℝ}
    {y : Ω → ℝ} (hx : ∀ i, MemLp (fun ω => x ω i) 2 P) (hy : MemLp y 2 P)
    (hxy : ∀ i, covariance (fun ω => x ω i) y P = 0) (i : Fin n) :
    covariance (fun ω => (A *ᵥ x ω) i) y P = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [covariance_fun_sum_left (X := fun j ω => A i j * x ω j)
    (fun j => (hx j).const_mul _) hy]
  simp [covariance_const_mul_left, hxy]

private theorem integral_mulVec (A : Matrix (Fin n) (Fin n) ℝ) {x : Ω → Fin n → ℝ}
    (hx : ∀ i, MemLp (fun ω => x ω i) 2 P) (i : Fin n) :
    (∫ ω, (A *ᵥ x ω) i ∂P) = (A *ᵥ fun j => ∫ ω, x ω j ∂P) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finsetSum Finset.univ (f := fun j ω => A i j * x ω j)
    (fun j _ => ((hx j).const_mul _).integrable (by norm_num))]
  simp only [integral_const_mul]

private theorem covMatrix_mulVec (A : Matrix (Fin n) (Fin n) ℝ) {x : Ω → Fin n → ℝ}
    (hx : ∀ i, MemLp (fun ω => x ω i) 2 P) :
    covMatrix P (fun i ω => (A *ᵥ x ω) i) =
      A * covMatrix P (fun i ω => x ω i) * Aᵀ := by
  ext i j
  change covariance (fun ω => (A *ᵥ x ω) i) (fun ω => (A *ᵥ x ω) j) P = _
  rw [EarthScience.covariance_linear_map hx i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, covMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem state_memLp_and_cov_noise (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (u : ℕ → Fin m → ℝ)
    (x₀ : Ω → Fin n → ℝ) (w : ℕ → Ω → Fin n → ℝ)
    (hx₀ : ∀ i, MemLp (fun ω => x₀ ω i) 2 P)
    (hw : ∀ k i, MemLp (fun ω => w k ω i) 2 P)
    (hw₀ : ∀ k i j, covariance (fun ω => w k ω i) (fun ω => x₀ ω j) P = 0)
    (hww : ∀ k l, l < k → ∀ i j, covariance (fun ω => w k ω i) (fun ω => w l ω j) P = 0)
    (k : ℕ) :
    (∀ i, MemLp (fun ω => state A B u x₀ w k ω i) 2 P) ∧
    ∀ l, k ≤ l → ∀ i j,
      covariance (fun ω => state A B u x₀ w k ω i) (fun ω => w l ω j) P = 0 := by
  induction k with
  | zero =>
    refine ⟨hx₀, fun l _ i j => ?_⟩
    rw [state, covariance_comm]
    exact hw₀ l j i
  | succ k ih =>
    let a (i : Fin n) (ω : Ω) := (A *ᵥ state A B u x₀ w k ω) i
    let b (i : Fin n) := (B *ᵥ u k) i
    have ha (i : Fin n) : MemLp (a i) 2 P := memLp_mulVec A ih.1 i
    have hb (i : Fin n) : MemLp (fun _ : Ω => b i) 2 P := memLp_const _
    have hab (i : Fin n) : MemLp (fun ω => a i ω + b i) 2 P := (ha i).add (hb i)
    refine ⟨fun i => (hab i).add (hw k i), ?_⟩
    intro l hkl i j
    let y (ω : Ω) := w l ω j
    change covariance ((fun ω => a i ω + b i) + fun ω => w k ω i) y P = 0
    rw [covariance_add_left (hab i) (hw k i) (hw l j),
      covariance_add_const_left ((ha i).integrable (by norm_num)),
      cov_mulVec_eq_zero A ih.1 (hw l j) (fun j' => ih.2 l (Nat.le_of_succ_le hkl) j' j) i,
      covariance_comm (fun ω => w k ω i) y]
    simp only [y, hww l k (Nat.lt_of_succ_le hkl) j i, add_zero]

/-- **Mean and covariance propagation with uncorrelated noise.** For the state recurrence
`x(k+1) = A *ᵥ x(k) + B *ᵥ u(k) + w(k)`, assume square-integrable coordinates, deterministic
inputs, and that each noise vector is uncorrelated with the initial state and all earlier noise
vectors. Then the current state is uncorrelated with the current noise, the mean includes the
input and noise mean, and the covariance updates as `A Pₖ Aᵀ + Qₖ`. The hypotheses do not require
Gaussian laws, independence, or centered noise.

Source: Anderson and Moore, *Optimal Filtering*, §2.2, equation (2.20) and Problem 2.4;
the same update follows under the weaker uncorrelatedness assumptions. -/
theorem mean_covariance_update (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (u : ℕ → Fin m → ℝ)
    (x₀ : Ω → Fin n → ℝ) (w : ℕ → Ω → Fin n → ℝ)
    (hx₀ : ∀ i, MemLp (fun ω => x₀ ω i) 2 P) (hw : ∀ k i, MemLp (fun ω => w k ω i) 2 P)
    (hw₀ : ∀ k i j, covariance (fun ω => w k ω i) (fun ω => x₀ ω j) P = 0)
    (hww : ∀ k l, l < k → ∀ i j, covariance (fun ω => w k ω i) (fun ω => w l ω j) P = 0)
    (k : ℕ) :
    let x := state A B u x₀ w
    let mean := fun k i => ∫ ω, x k ω i ∂P
    let cov := fun k => covMatrix P (fun i ω => x k ω i)
    (∀ i, MemLp (fun ω => x k ω i) 2 P) ∧
    mean (k + 1) = A *ᵥ mean k + B *ᵥ u k + (fun i => ∫ ω, w k ω i ∂P) ∧
    (∀ i j, covariance (fun ω => x k ω i) (fun ω => w k ω j) P = 0) ∧
    cov (k + 1) = A * cov k * Aᵀ + covMatrix P (fun i ω => w k ω i) := by
  let x := state A B u x₀ w
  obtain ⟨hx, hcov⟩ := state_memLp_and_cov_noise A B u x₀ w hx₀ hw hw₀ hww k
  let a (i : Fin n) (ω : Ω) := (A *ᵥ x k ω) i
  let b (i : Fin n) := (B *ᵥ u k) i
  let v (i : Fin n) (ω : Ω) := w k ω i
  let c (i : Fin n) (ω : Ω) := a i ω + b i
  have ha (i : Fin n) : MemLp (a i) 2 P := memLp_mulVec A hx i
  have hb (i : Fin n) : MemLp (fun _ : Ω => b i) 2 P := memLp_const _
  have hc (i : Fin n) : MemLp (c i) 2 P := (ha i).add (hb i)
  have hac (i j : Fin n) : covariance (a i) (v j) P = 0 :=
    cov_mulVec_eq_zero A hx (hw k j) (fun l => hcov k le_rfl l j) i
  refine ⟨hx, ?_, hcov k le_rfl, ?_⟩
  · funext i
    change (∫ ω, c i ω + v i ω ∂P) =
      (A *ᵥ fun j => ∫ ω, x k ω j ∂P) i + b i + ∫ ω, v i ω ∂P
    rw [integral_add ((hc i).integrable (by norm_num)) ((hw k i).integrable (by norm_num))]
    change ((∫ ω, a i ω + b i ∂P) + ∫ ω, v i ω ∂P) = _
    rw [integral_add ((ha i).integrable (by norm_num)) (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    rw [integral_mulVec A hx i]
  · change covMatrix P (fun i ω => x (k + 1) ω i) =
      A * covMatrix P (fun i ω => x k ω i) * Aᵀ + covMatrix P v
    rw [← covMatrix_mulVec A hx]
    ext i j
    change covariance (c i + v i) (c j + v j) P =
      covariance (a i) (a j) P + covariance (v i) (v j) P
    rw [covariance_add_left (hc i) (hw k i) ((hc j).add (hw k j)),
      covariance_add_right (hc i) (hc j) (hw k j),
      covariance_add_right (hw k i) (hc j) (hw k j)]
    dsimp only [c]
    rw [covariance_add_const_left ((ha i).integrable (by norm_num)),
      covariance_add_const_right ((ha j).integrable (by norm_num)),
      covariance_add_const_left ((ha i).integrable (by norm_num)),
      covariance_add_const_right ((ha j).integrable (by norm_num)), hac i j,
      covariance_comm (v i) (a j), hac j i]
    simp [v]

end Cslib.MachineLearning.Sequence.LinearStateMoments
