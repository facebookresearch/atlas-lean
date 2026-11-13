/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Lucas-polytopic numbers

This file formalizes the definitions in Orozco López,
*Simplicial d-Polytopic Numbers Defined on Lucas Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Orozco/oroz2.tex>.
-/

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- The Lucas bracket recurrence before imposing the nondegeneracy needed by
quotient formulas. -/
def lucasBracketAux (s t : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => s * lucasBracketAux s t (n + 1) + t * lucasBracketAux s t n

/-- Parameters for which every positive Lucas bracket is nonzero. The final
condition is what makes all factorial quotients below genuine field quotients,
rather than Lean's totalized `0 / 0`. -/
structure LucasParameters where
  /-- The coefficient of `{n + 1}ₛₜ` in the Lucas bracket recurrence. -/
  s : ℝ
  /-- The coefficient of `{n}ₛₜ` in the Lucas bracket recurrence. -/
  t : ℝ
  s_ne_zero : s ≠ 0
  t_ne_zero : t ≠ 0
  bracket_ne_zero : ∀ n, n ≠ 0 → lucasBracketAux s t n ≠ 0

/-- The Lucas bracket sequence with initial values zero and one and recurrence
`{n + 2}ₛₜ = s * {n + 1}ₛₜ + t * {n}ₛₜ`. -/
def lucasBracket (P : LucasParameters) : ℕ → ℝ
  | n => lucasBracketAux P.s P.t n

theorem lucasBracket_ne_zero (P : LucasParameters) {n : ℕ} (hn : n ≠ 0) :
    lucasBracket P n ≠ 0 :=
  P.bracket_ne_zero n hn

/-- The `s,t`-factorial, the product of Lucas brackets from one through `n`. -/
def lucasFactorial (P : LucasParameters) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, lucasBracket P (k + 1)

theorem lucasFactorial_ne_zero (P : LucasParameters) (n : ℕ) :
    lucasFactorial P n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact lucasBracket_ne_zero P (Nat.succ_ne_zero k)

/-- The Lucasnomial coefficient. As for `Nat.choose`, it is zero when
`k > n`; within its source domain it is the displayed quotient of
`s,t`-factorials. -/
noncomputable def lucasnomial (P : LucasParameters) (n k : ℕ) : ℝ :=
  if k ≤ n then lucasFactorial P n / (lucasFactorial P k * lucasFactorial P (n - k)) else 0

@[simp]
theorem lucasnomial_eq_zero_of_lt (P : LucasParameters) {n k : ℕ} (h : n < k) :
    lucasnomial P n k = 0 := by
  simp [lucasnomial, Nat.not_le.mpr h]

/-- The `n`-th simplicial `d`-Lucas-polytopic number. -/
noncomputable def lucasPolytopicNumber (P : LucasParameters) (n d : ℕ) : ℝ :=
  lucasnomial P (n + d - 1) d

/-- The Lucas analogue of the `n`-th triangular number. -/
noncomputable def lucasTriangularNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 1) 2

/-- The Lucas analogue of the `n`-th tetrahedral number. -/
noncomputable def lucasTetrahedralNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 2) 3

/-- The Lucas analogue of the `n`-th pentachoron number. -/
noncomputable def lucasPentachoronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 3) 4

/-- The Lucas analogue of the `n`-th hexateron number. -/
noncomputable def lucasHexateronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 4) 5

end MetaMathlibExt
