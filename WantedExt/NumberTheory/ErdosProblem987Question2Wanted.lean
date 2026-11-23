/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 987, question 2
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem987Question2Wanted

/-! Source record `UM-00002427-Q002`. -/
/-- The additive character `e(t) = exp(2πit)`. -/
noncomputable def eCirc (t : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I)

/-- The exponential sum `∑_{j < n} e(k x_j)`. -/
noncomputable def seqSum (x : ℕ → ℝ) (k n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, eCirc ((k : ℝ) * x j)

/-- `A_k = limsup_{n → ∞} |∑_{j < n} e(k x_j)|`, valued in `ℝ≥0∞`. -/
noncomputable def Ak (x : ℕ → ℝ) (k : ℕ) : ENNReal :=
  Filter.limsup (fun n : ℕ => ENNReal.ofReal ‖seqSum x k n‖) (Filter.atTop : Filter ℕ)

/-- Some sequence in `(0, 1)` has `A_k = o(k)`: for every `ε > 0`, eventually `A_k ≤ ε k`. -/
def conjecture : Prop :=
  ∃ (x : ℕ → ℝ), (∀ n, 0 < x n ∧ x n < 1) ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Ak x k ≤ ENNReal.ofReal (ε * (k : ℝ))

-- Carried source audit `UM-00002427-Q002` (see the Moved/ record).

/--
Resolved true: Alexeev, Putterman, Sawhney, Sellke, and Valiant constructed a sequence with Aₖ ≪
√(k log k), hence Aₖ = o(k). Source: Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke,
and Gregory Valiant, Short proofs in combinatorics, probability and number theory II,
arXiv:2604.06609v1, https://arxiv.org/abs/2604.06609v1; T. F. Bloom, Erdős Problem #987,
erdosproblems.com, https://www.erdosproblems.com/987. Moved from
`OpenConjectures/NumberTheory/ErdosProblem987Question2`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem987Question2Wanted
