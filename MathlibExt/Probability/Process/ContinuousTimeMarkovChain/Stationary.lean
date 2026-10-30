/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Semigroup
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination

/-!
# Stationarity and detailed balance for finite continuous-time Markov chains

A row vector `π` is **invariant** for the generator `Q` if `π Q = 0`; it is in **detailed
balance** with `Q` if `π i Q i j = π j Q j i` for all states. For a finite chain with
transition function `P t = exp (t • Q)`:

* `π Q = 0` if and only if `π P t = π` for every `t` (Norris 1997, §3.5, for finite state
  spaces);
* detailed balance implies invariance, and it propagates to the transition function:
  `π i P t i j = π j P t j i` for every `t` (Norris 1997, §3.7).

These statements are algebraic equations about arbitrary real vectors `π`; `π = 0`, for
instance, is in detailed balance with every matrix. Only when `π` is a probability vector
(nonnegative, summing to `1`) and `Q` is a rate matrix, so that `P t` is stochastic, are the
propagated equations the matrix form of the time-reversibility of the chain started from `π`;
stationary *distributions* are likewise the invariant probability vectors. No path-space
process is constructed here.

## Main definitions

* `ProbabilityTheory.IsDetailedBalance π Q`: `π i * Q i j = π j * Q j i` for all `i j`.

## Main results

* `vecMul_eq_zero_iff_forall_vecMul_ctmcTransition`: `π ᵥ* Q = 0 ↔ ∀ t, π ᵥ* P t = π`.
* `IsDetailedBalance.vecMul_eq_zero`: detailed balance and zero row sums imply `π ᵥ* Q = 0`.
* `IsDetailedBalance.ctmcTransition`: detailed balance for `Q` implies detailed balance for
  every `P t` (for a probability vector `π` and a rate matrix `Q`, reversibility).
* `IsDetailedBalance.vecMul_ctmcTransition`: hence `π ᵥ* P t = π`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §3.5 and §3.7.
-/

@[expose] public section

open Finset Matrix

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The row vector `π` is in **detailed balance** with the matrix `Q`:
`π i * Q i j = π j * Q j i` for all `i j` (Norris 1997, §3.7). This is only the algebraic
equation: it holds for `π = 0` and every `Q`. For a probability vector `π` and a stochastic
matrix it is the reversibility of the chain started from `π`. -/
def IsDetailedBalance (π : ι → ℝ) (Q : Matrix ι ι ℝ) : Prop :=
  ∀ i j, π i * Q i j = π j * Q j i

/-- **Invariance under the semigroup**: `π Q = 0` if and only if `π P t = π` for every real
`t` (Norris 1997, §3.5, finite state space). -/
theorem vecMul_eq_zero_iff_forall_vecMul_ctmcTransition [DecidableEq ι] (π : ι → ℝ)
    (Q : Matrix ι ι ℝ) :
    π ᵥ* Q = 0 ↔ ∀ t, π ᵥ* ctmcTransition Q t = π := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := ι) (R := ℝ) (α := ℝ)
  let L : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
    (Matrix.vecMulBilin ℝ ℝ π).toContinuousLinearMap
  have hd (t : ℝ) : HasDerivAt (fun s => π ᵥ* ctmcTransition Q s)
      ((π ᵥ* Q) ᵥ* ctmcTransition Q t) t := by
    simpa [L, ctmcTransition, Matrix.vecMul_vecMul] using!
      L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' Q t)
  constructor
  · intro h t
    have hz (s : ℝ) : HasDerivAt (fun u => π ᵥ* ctmcTransition Q u) 0 s := by
      simpa [h] using hd s
    have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
      (fun s => (hz s).deriv) t 0
    simpa [ctmcTransition] using hc
  · intro h
    have hc : HasDerivAt (fun t => π ᵥ* ctmcTransition Q t) 0 0 := by
      simpa only [h] using hasDerivAt_const (0 : ℝ) π
    simpa [ctmcTransition] using (hd 0).unique hc

namespace IsDetailedBalance

variable {π : ι → ℝ} {Q : Matrix ι ι ℝ}

/-- Detailed balance with a matrix whose rows sum to `0` implies invariance `π Q = 0`
(Norris 1997, §3.7). -/
theorem vecMul_eq_zero (h : IsDetailedBalance π Q) (hQ : ∀ i, ∑ j, Q i j = 0) :
    π ᵥ* Q = 0 := by
  ext j
  simp only [vecMul, dotProduct, Pi.zero_apply]
  calc ∑ i, π i * Q i j = ∑ i, π j * Q j i := sum_congr rfl fun i _ => h i j
    _ = 0 := by rw [← mul_sum, hQ j, mul_zero]

/-- **Detailed balance propagates to the transition function**: detailed balance for `Q`
implies `π i P t i j = π j P t j i` for every `t` (Norris 1997, §3.7). For a probability
vector `π` and a rate matrix `Q` this is the reversibility of the chain started from `π`. -/
theorem ctmcTransition [DecidableEq ι] (h : IsDetailedBalance π Q) (t : ℝ) :
    IsDetailedBalance π (ctmcTransition Q t) := by
  have hs : SemiconjBy (diagonal π) (t • Q) (t • Qᵀ) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
      Matrix.transpose_apply]
    linear_combination t * h i j
  have he : diagonal π * NormedSpace.exp (t • Q) = NormedSpace.exp (t • Qᵀ) * diagonal π :=
    open scoped Matrix.Norms.Operator in hs.exp_right
  rw [← Matrix.transpose_smul, Matrix.exp_transpose] at he
  intro i j
  simpa [ProbabilityTheory.ctmcTransition, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_comm] using congrFun (congrFun he i) j

/-- Detailed balance with a matrix whose rows sum to `0` (for instance a rate matrix) makes `π`
invariant for every `P t`. -/
theorem vecMul_ctmcTransition [DecidableEq ι] (h : IsDetailedBalance π Q)
    (hQ : ∀ i, ∑ j, Q i j = 0) (t : ℝ) :
    π ᵥ* ProbabilityTheory.ctmcTransition Q t = π :=
  (vecMul_eq_zero_iff_forall_vecMul_ctmcTransition π Q).mp (h.vecMul_eq_zero hQ) t

end IsDetailedBalance

end ProbabilityTheory
