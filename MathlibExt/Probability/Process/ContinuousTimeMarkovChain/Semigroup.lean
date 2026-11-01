/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The transition semigroup of a finite continuous-time Markov chain

For a real square matrix `Q` on a finite type `ι`, `ctmcTransition Q t = exp (t • Q)` is the
transition function of the continuous-time Markov chain with generator `Q` (Norris 1997, §2.1
and Theorem 2.1.1): for a rate matrix `Q` and `t ≥ 0`, `ctmcTransition Q t i j` is the
probability of being in state `j` at time `t` when starting from `i`. Only this matrix
function is studied; no path-space construction of the chain is made here.

The algebraic statements (`ctmcTransition_zero`, `ctmcTransition_add`, the Kolmogorov
equations, uniformization) hold for every real matrix `Q` and every real `t`. Stochasticity
needs `Q` to be a rate matrix, and nonnegativity also needs `t ≥ 0`.

## Main definitions

* `ProbabilityTheory.ctmcTransition Q t`: the matrix exponential `exp (t • Q)`.

## Main results

* `ctmcTransition_zero`, `ctmcTransition_add`: `P 0 = 1` and the semigroup (Chapman–Kolmogorov)
  property `P (s + t) = P s * P t`.
* `hasDerivAt_ctmcTransition_backward`, `hasDerivAt_ctmcTransition_forward`: the **Kolmogorov
  backward and forward equations** `P' t = Q * P t` and `P' t = P t * Q`.
* `ctmcTransition_eq_exp_smul_uniformized`: **uniformization**,
  `P t = e^{-c t} • exp (t • (Q + c • 1))`.
* `IsRateMatrix.sum_ctmcTransition`: the rows of `P t` sum to `1` for every `t`.
* `IsRateMatrix.ctmcTransition_nonneg`: the entries of `P t` are nonnegative for `t ≥ 0`.
* `IsRateMatrix.ctmcTransition_mem_rowStochastic`: `P t` is row-stochastic for `t ≥ 0`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.1 (Theorems 2.1.1
  and 2.1.2).
* A. Jensen, *Markoff chains as an aid in the study of Markoff processes*, Skand.
  Aktuarietidskr. 36 (1953), 87–91 (uniformization).
-/

@[expose] public section

open Finset Matrix NormedSpace

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transition function `P t = exp (t • Q)` of the finite continuous-time Markov chain
with generator `Q` (Norris 1997, Theorem 2.1.1). -/
noncomputable def ctmcTransition (Q : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  exp (t • Q)

variable (Q : Matrix ι ι ℝ)

/-- At time `0` the transition function is the identity. -/
@[simp]
theorem ctmcTransition_zero : ctmcTransition Q 0 = 1 := by
  simp [ctmcTransition]

/-- The **semigroup property** (Chapman–Kolmogorov equation): `P (s + t) = P s * P t`. -/
theorem ctmcTransition_add (s t : ℝ) :
    ctmcTransition Q (s + t) = ctmcTransition Q s * ctmcTransition Q t := by
  rw [ctmcTransition, ctmcTransition, ctmcTransition, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Q).smul_left s).smul_right t)

/-- Rescaling the generator rescales time: `exp (t • (a • Q)) = exp ((a * t) • Q)`. -/
theorem ctmcTransition_smul (a t : ℝ) : ctmcTransition (a • Q) t = ctmcTransition Q (a * t) := by
  simp only [ctmcTransition, smul_smul, mul_comm t a]

/-- The generator commutes with the transition function. -/
theorem commute_ctmcTransition (t : ℝ) : Commute Q (ctmcTransition Q t) :=
  ((Commute.refl Q).smul_right t).exp_right

/-- The **Kolmogorov backward equation** `P' t = Q * P t` (Norris 1997, Theorem 2.1.1). -/
theorem hasDerivAt_ctmcTransition_backward (t : ℝ) :
    HasDerivAt (ctmcTransition Q) (Q * ctmcTransition Q t) t := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  exact hasDerivAt_exp_smul_const' Q t

/-- The **Kolmogorov forward equation** `P' t = P t * Q` (Norris 1997, Theorem 2.1.1). -/
theorem hasDerivAt_ctmcTransition_forward (t : ℝ) :
    HasDerivAt (ctmcTransition Q) (ctmcTransition Q t * Q) t := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  exact hasDerivAt_exp_smul_const Q t

/-- **Uniformization**: for every real `c`,
`exp (t • Q) = e^{-c t} • exp (t • (Q + c • 1))` (Jensen 1953). -/
theorem ctmcTransition_eq_exp_smul_uniformized (c t : ℝ) :
    ctmcTransition Q t =
      Real.exp (-(c * t)) • ctmcTransition (Q + c • (1 : Matrix ι ι ℝ)) t := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := ι) (α := ℝ)
  have hexp (s : ℝ) : exp (s • (1 : Matrix ι ι ℝ)) = Real.exp s • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using!
      (algebraMap_exp_comm (𝔸 := Matrix ι ι ℝ) s).symm
  have hsplit : t • Q = -(c * t) • (1 : Matrix ι ι ℝ) + t • (Q + c • 1) := by
    rw [smul_add, smul_smul, mul_comm t c, neg_smul, add_comm (t • Q),
      ← add_assoc, neg_add_cancel, zero_add]
  unfold ctmcTransition
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_left _).smul_left _),
    hexp, smul_mul_assoc, one_mul]

/-- If `A` has nonnegative entries, so does `exp (t • A)` for `t ≥ 0`. -/
theorem ctmcTransition_nonneg_of_nonneg {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ}
    (ht : 0 ≤ t) (i j : ι) : 0 ≤ ctmcTransition A t i j := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := ι) (α := ℝ)
  have hp (n : ℕ) : ∀ i j, 0 ≤ ((t • A) ^ n) i j := by
    induction n with
    | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
    | succ n hn =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hn i k) (mul_nonneg ht (hA k j))
  have hij := Pi.hasSum.mp (Pi.hasSum.mp (exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)) i) j
  refine hij.nonneg fun n => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hp n i j)

/-- If `Q` annihilates the constant vector `1`, then `P t` fixes it: `P t *ᵥ 1 = 1`. -/
theorem ctmcTransition_mulVec_one {Q : Matrix ι ι ℝ} (hQ : Q *ᵥ 1 = 0) (t : ℝ) :
    ctmcTransition Q t *ᵥ 1 = 1 := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  set J : Matrix ι ι ℝ := Matrix.of fun _ _ => 1
  have hQJ : Q * J = 0 := by
    ext i j
    have := congrFun hQ i
    simpa [J, mul_apply, mulVec, dotProduct] using this
  have hd (u : ℝ) := HasDerivAt.mul_const (hasDerivAt_exp_smul_const Q u) J
  simp only [mul_assoc, hQJ, mul_zero] at hd
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [zero_smul, exp_zero, one_mul] at hc
  ext i
  have := congrFun (congrFun hc i) i
  simp only [J, mul_apply, of_apply, mul_one] at this
  simp only [ctmcTransition, mulVec, dotProduct, Pi.one_apply, mul_one]
  exact this

namespace IsRateMatrix

variable {Q}

/-- The rows of the transition function of a rate matrix sum to `1`, for every real `t`. -/
theorem sum_ctmcTransition (hQ : IsRateMatrix Q) (t : ℝ) (i : ι) :
    ∑ j, ctmcTransition Q t i j = 1 := by
  simpa [mulVec, dotProduct] using congrFun (ctmcTransition_mulVec_one hQ.mulVec_one t) i

/-- The transition function of a rate matrix has nonnegative entries for `t ≥ 0`, by
uniformization. -/
theorem ctmcTransition_nonneg (hQ : IsRateMatrix Q) {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    0 ≤ ctmcTransition Q t i j := by
  obtain ⟨c, -, hc⟩ := hQ.exists_add_smul_one_nonneg
  rw [ctmcTransition_eq_exp_smul_uniformized Q c t]
  exact mul_nonneg (Real.exp_pos _).le (ctmcTransition_nonneg_of_nonneg hc ht i j)

/-- The transition function of a rate matrix is row-stochastic for `t ≥ 0` (Norris 1997,
Theorem 2.1.2). -/
theorem ctmcTransition_mem_rowStochastic (hQ : IsRateMatrix Q) {t : ℝ} (ht : 0 ≤ t) :
    ctmcTransition Q t ∈ rowStochastic ℝ ι :=
  mem_rowStochastic_iff_sum.mpr ⟨hQ.ctmcTransition_nonneg ht, hQ.sum_ctmcTransition t⟩

end IsRateMatrix

end ProbabilityTheory
