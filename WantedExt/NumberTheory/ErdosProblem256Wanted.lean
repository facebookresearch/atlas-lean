/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 256
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem256Wanted

/-! Source record `UM-00002011-Q001`. -/
/-- The product `∏_i (1 - z^{a_i})`. -/
noncomputable def trigProd (n : ℕ) (a : Fin n → ℕ) (z : ℂ) : ℂ :=
  Finset.prod Finset.univ (fun i => 1 - z ^ (a i))

/-- Exponent tuples `1 ≤ a_1 ≤ ⋯ ≤ a_n`. -/
def admissible (n : ℕ) (a : Fin n → ℕ) : Prop :=
  (∀ i, 1 ≤ a i) ∧ Monotone a

/-- `max_{|z| = 1} |∏_i (1 - z^{a_i})|`, as a supremum over the unit circle. -/
noncomputable def maxOnCircle (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  sSup { x : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖trigProd n a z‖ }

/-- The circle maxima of all admissible exponent tuples of length `n`. -/
noncomputable def setMaxValues (n : ℕ) : Set ℝ :=
  { y : ℝ | ∃ a : Fin n → ℕ, admissible n a ∧ y = maxOnCircle n a }

/-- `f(n)`: the largest lower bound for the circle maxima of all admissible tuples of length `n`,
i.e. their infimum (`0` for `n = 0`). -/
noncomputable def fErdos (n : ℕ) : ℝ :=
  if n = 0 then 0 else sInf (setMaxValues n)

/-- `log f(n) ≫ n^c` for some `c > 0`. -/
def conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → Real.log (fErdos n) ≥ C * ((n :
    ℝ) ^ c)

-- Carried source audit `UM-00002011-Q001` (see the Moved/ record).

/--
Resolved false: The formalized question, whether log f(n) ≫ n^c for some c > 0, has a negative
answer: erdosproblems.com/256 (checked 2026-10-22) records that Belov and Konyagin (1996) proved
log f(n) ≪ (log n)^4. The page's open-ended request to estimate f(n) is not a proposition and is
not formalized. Source: A. S. Belov and S. V. Konyagin, An estimate of the constant term of a
nonnegative trigonometric polynomial with integer coefficients, Mathematical Notes 59 (1996),
no. 4, 451–453, https://doi.org/10.1007/BF02308695; T. F. Bloom, Erdős Problem #256,
erdosproblems.com, https://www.erdosproblems.com/256. Moved from
`OpenConjectures/NumberTheory/ErdosProblem256`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem256Wanted
