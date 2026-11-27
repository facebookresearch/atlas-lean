/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The Press–Dyson determinant lemma

Memory-one strategies define a Markov matrix and the Press–Dyson determinant. For a stationary
distribution, the dot product with any vector is the ratio of its Press–Dyson determinant to
that of the constant-one vector, provided the latter determinant is nonzero.

Sources: W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
"Zero-determinant strategies", eqs. (1)–(7), and "X unilaterally sets Y's score", eqs. (8)–(10).
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

open Matrix Set

/-- Y's cooperation probabilities re-indexed to X's view of the outcome:
`(q₁, q₃, q₂, q₄)`. -/
def yView (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0, q 2, q 1, q 3]

/-- The **Markov matrix** `M(p, q)` of outcomes `cc, cd, dc, dd`: from outcome `s`, X
cooperates with probability `p s`, Y cooperates with probability `yView q s`, independently;
X cooperates in outcomes `0, 1` and Y in outcomes `0, 2`. -/
def markovMatrix (p q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun s s' =>
    (if s' = 0 ∨ s' = 1 then p s else 1 - p s) *
      (if s' = 0 ∨ s' = 2 then yView q s else 1 - yView q s)

/-- `v` is a **stationary distribution** of `M`: `vᵀ M = vᵀ`, `v ≥ 0` and `∑ v = 1`. -/
def IsStationary (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  v ᵥ* M = v ∧ (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1

/-- X's column `p̃ = (-1 + p₁, -1 + p₂, p₃, p₄)`. -/
def pTilde (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-1 + p 0, -1 + p 1, p 2, p 3]

/-- Y's column `q̃ = (-1 + q₁, q₃, -1 + q₂, q₄)`. -/
def qTilde (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-1 + q 0, q 2, -1 + q 1, q 3]

/-- The Press–Dyson determinant `D(p, q, f)`, with columns
`(-1 + p₁q₁, p₂q₃, p₃q₂, p₄q₄)`, `p̃`, `q̃` and `f`. -/
def pdDet (p q f : Fin 4 → ℝ) : ℝ :=
  (Matrix.of fun i j =>
    ![![-1 + p 0 * q 0, p 1 * q 2, p 2 * q 1, p 3 * q 3] i, pTilde p i, qTilde q i, f i] j).det

/-- `p` is a memory-one strategy: every component lies in `[0, 1]`. -/
def IsStrategy (p : Fin 4 → ℝ) : Prop :=
  ∀ i, p i ∈ Icc (0 : ℝ) 1

private def pdMatrix (p q f : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    ![![-1 + p 0 * q 0, p 1 * q 2, p 2 * q 1, p 3 * q 3] i, pTilde p i, qTilde q i, f i] j

private theorem stationary_vecMul_pdMatrix {p q v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix p q) v) :
    v ᵥ* pdMatrix p q 1 = ![0, 0, 0, 1] := by
  have h0 := congrFun hv.1 (0 : Fin 4)
  have h1 := congrFun hv.1 (1 : Fin 4)
  have h2 := congrFun hv.1 (2 : Fin 4)
  simp [vecMul, dotProduct, Fin.sum_univ_succ, markovMatrix, yView] at h0 h1 h2
  ext j
  fin_cases j
  · simp [vecMul, dotProduct, Fin.sum_univ_succ, pdMatrix, pTilde, qTilde]
    linear_combination h0
  · simp [vecMul, dotProduct, Fin.sum_univ_succ, pdMatrix, pTilde, qTilde]
    linear_combination h0 + h1
  · simp [vecMul, dotProduct, Fin.sum_univ_succ, pdMatrix, pTilde, qTilde]
    linear_combination h0 + h2
  · simpa [vecMul, dotProduct, Fin.sum_univ_succ, pdMatrix] using hv.2.2

private theorem cramer_pdMatrix (p q f : Fin 4 → ℝ) :
    cramer (pdMatrix p q 1) f 3 = pdDet p q f := by
  rw [cramer_apply]
  change ((pdMatrix p q 1).updateCol 3 f).det = (pdMatrix p q f).det
  congr 1
  ext i j
  fin_cases j <;> simp [pdMatrix, updateCol]

/-- **Press–Dyson determinant lemma** (Press and Dyson 2012, eqs. (4)–(6)). For memory-one
strategies `p, q` (components in `[0, 1]`), every stationary distribution `v` of `M(p, q)` with
`D(p, q, 1) ≠ 0`, and every `f : Fin 4 → ℝ`, `v · f = D(p, q, f) / D(p, q, 1)`.

Source: Press and Dyson (2012), "Zero-determinant strategies", eqs. (4)–(6). -/
public theorem dotProduct_eq_div_pdDet {p q : Fin 4 → ℝ} (hp : IsStrategy p)
    (hq : IsStrategy q) {v : Fin 4 → ℝ} (hv : IsStationary (markovMatrix p q) v)
    (hD : pdDet p q 1 ≠ 0) (f : Fin 4 → ℝ) : v ⬝ᵥ f = pdDet p q f / pdDet p q 1 := by
  have _ := hp
  have _ := hq
  have h := congrArg (fun w => v ⬝ᵥ w) (mulVec_cramer (pdMatrix p q 1) f)
  rw [dotProduct_mulVec, stationary_vecMul_pdMatrix hv, dotProduct_smul,
    smul_eq_mul] at h
  have hc : (![0, 0, 0, 1] : Fin 4 → ℝ) ⬝ᵥ cramer (pdMatrix p q 1) f =
      pdDet p q f := by
    simpa [dotProduct, Fin.sum_univ_succ] using cramer_pdMatrix p q f
  rw [hc] at h
  apply (eq_div_iff hD).2
  simpa only [pdDet, pdMatrix, mul_comm] using h.symm

end WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted
