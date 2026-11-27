/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.BoundaryESSStabilityReLtZero
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

namespace DomainsTest.Biology.Ecology.BoundaryESSStabilityReLtZero

open Matrix

/-- The payoff matrix of a two-strategy coordination game. -/
private def A2 : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

/-- The pure strategy `0`. -/
private def p2 : Fin 2 → ℝ := ![1, 0]

private theorem Ap2 : A2 *ᵥ p2 = ![2, 0] := by
  funext i
  fin_cases i <;> simp [A2, p2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem hpAp2 : p2 ⬝ᵥ A2 *ᵥ p2 = 2 := by
  rw [Ap2]
  simp [dotProduct, Fin.sum_univ_two, p2]

private theorem hqAp2 (q : Fin 2 → ℝ) : q ⬝ᵥ A2 *ᵥ p2 = 2 * q 0 := by
  rw [Ap2]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]

/-- The pure strategy `0` is a regular ESS of the coordination game `A2`. -/
private theorem isRegularESS_A2 : IsRegularESS A2 p2 := by
  have hpmem : p2 ∈ simplex (Fin 2) := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [p2]
    · simp [p2, Fin.sum_univ_two]
  refine ⟨⟨hpmem, ?_⟩, ?_, ?_⟩
  · intro q hq hne
    left
    rw [hqAp2, hpAp2]
    have hq0 : ∀ i, 0 ≤ q i := hq.1
    have hsum2 : q 0 + q 1 = 1 := by
      have h1 := hq.2
      rwa [Fin.sum_univ_two] at h1
    have hq0lt : q 0 < 1 := by
      by_contra hcon
      have hle : 1 ≤ q 0 := le_of_not_gt hcon
      have hq00 := hq0 0
      have hq01 := hq0 1
      have h10 : q 1 = 0 := by linarith
      have h01 : q 0 = 1 := by linarith
      apply hne
      funext i
      fin_cases i
      · simpa [p2] using h01
      · simpa [p2] using h10
    linarith
  · intro i hi
    fin_cases i
    · simp [p2] at hi
    · rw [hpAp2, Ap2]
      simp
  · intro x hx0 hsum hsupp
    have hp10 : p2 1 = 0 := by simp [p2]
    have hx1 : x 1 = 0 := hsupp 1 hp10
    have hsum2 : x 0 + x 1 = 0 := by
      have h1 := hsum
      rwa [Fin.sum_univ_two] at h1
    have hx0' : x 0 = 0 := by linarith
    exfalso
    apply hx0
    funext i
    fin_cases i
    · exact hx0'
    · exact hx1

/-- Every tangent eigenvalue of the Jacobian at `p2` has negative real part. -/
private theorem re_lt_zero_A2 (μ : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (hμ : (replicatorJacobian A2 p2).map (fun a : ℝ => (a : ℂ)) *ᵥ v = μ • v) :
    μ.re < 0 :=
  IsRegularESS.re_lt_zero isRegularESS_A2 μ v hv hsum hμ

/-- Zero is not a tangent eigenvalue of the Jacobian at `p2`. -/
private theorem zero_not_tangent_eigenvalue (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (hsum : ∑ i, v i = 0)
    (hμ : (replicatorJacobian A2 p2).map (fun a : ℝ => (a : ℂ)) *ᵥ v = (0 : ℂ) • v) :
    False := by
  have h := re_lt_zero_A2 0 v hv hsum hμ
  simp at h

end DomainsTest.Biology.Ecology.BoundaryESSStabilityReLtZero
