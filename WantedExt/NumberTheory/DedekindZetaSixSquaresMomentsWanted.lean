/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Power moments of Dedekind zeta coefficients over sums of six squares

Statements from Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the
Coefficients of the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25
(2025), Article A101.

For a number field `K`, `a_K(n)` is the number of integral ideals of `𝓞 K` of norm `n`, and
`S_ℓ(x) = ∑_{x₁² + ⋯ + x₆² ≤ x} a_K(x₁² + ⋯ + x₆²)^ℓ = ∑_{1 ≤ n ≤ x} r₆(n) a_K(n)^ℓ`
(the paper's equation (12); the zero vector is left out, as in that equation).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import WantedExt.NumberTheory.SquaresTriangularRepresentationsWanted

namespace MetaMathlibExt

@[expose] public section

open Complex NumberField

/-- Fourth moment of the Dirichlet `L`-function of the non-principal character `χ` modulo `4`
on the critical line: for every `ε > 0`, `∫_1^T |L(1/2 + i t, χ)|⁴ dt ≪_ε T^{1 + ε}` uniformly
for `T ≥ 1`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Lemma 5, third display (`integers-2025-A101-lem-5`). -/
public theorem_wanted dirichletLFunction_mod_four_fourth_moment_le {ε : ℝ} (hε : 0 < ε)
    (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (1 : ℝ)..T, ‖χ.LFunction (1 / 2 + t * I)‖ ^ 4 ≤ C * T ^ (1 + ε)

/-- The coefficient `a_K(n)` of the Dedekind zeta function `ζ_K(s) = ∑ a_K(n) n^{-s}`: the
number of ideals of `𝓞 K` of absolute norm `n`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (2). -/
noncomputable def dedekindZetaCoeff (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- `a_K(1) = 1`: the unit ideal is the only ideal of norm `1`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (2). -/
theorem dedekindZetaCoeff_one (K : Type*) [Field K] [NumberField K] :
    dedekindZetaCoeff K 1 = 1 := by
  rw [dedekindZetaCoeff, Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2)⟩

/-- The moment `S_ℓ(x) = ∑_{1 ≤ n ≤ x} r₆(n) a_K(n)^ℓ`, with `r₆(n)` the number of
representations of `n` as a sum of six squares of integers (`sumOfSquaresRepCount 6 n`).

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (4), and Section 2, equation (12). -/
noncomputable def sixSquaresDedekindMoment (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (sumOfSquaresRepCount 6 n : ℝ) * (dedekindZetaCoeff K n : ℝ) ^ ℓ

/-- `S_ℓ(x) = 0` for `x < 1`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (4). -/
theorem sixSquaresDedekindMoment_of_lt_one (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    {x : ℝ} (hx : x < 1) : sixSquaresDedekindMoment K ℓ x = 0 := by
  simp [sixSquaresDedekindMoment, Nat.floor_eq_zero.mpr hx]

/-- The exponent `a_{0,ℓ} = 1 + ∑_{i=1}^{⌊ℓ/2⌋} C(ℓ, 2i) (2i)!/(i!(i+1)!)`, the multiplicity of
the constant term in `a_K(p)^ℓ`; `(2i)!/(i!(i+1)!)` is the Catalan number `catalan i`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2 and equation (19). -/
def dedekindSixSquaresA0 (ℓ : ℕ) : ℕ :=
  1 + ∑ i ∈ Finset.Icc 1 (ℓ / 2), ℓ.choose (2 * i) * catalan i

/-- The exponent `a_{3,ℓ} = ∑_{i=1}^{⌈ℓ/2 - 1⌉} C(ℓ, 2i+1) · 4(2i+1)!/((i-1)!(i+3)!)`
(`⌈ℓ/2 - 1⌉ = ⌊(ℓ - 1)/2⌋`; each quotient is an integer).

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2. -/
def dedekindSixSquaresA3 (ℓ : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ℓ.choose (2 * i + 1) *
    (4 * (2 * i + 1).factorial / ((i - 1).factorial * (i + 3).factorial))

/-- The values `a_{0,ℓ}, a_{3,ℓ}` for `ℓ = 3, 4, 5`: `(4, 1)`, `(9, 4)`, `(21, 14)` (Table 1).

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Table 1. -/
theorem dedekindSixSquaresA0_A3_small :
    (dedekindSixSquaresA0 3, dedekindSixSquaresA3 3) = (4, 1) ∧
      (dedekindSixSquaresA0 4, dedekindSixSquaresA3 4) = (9, 4) ∧
      (dedekindSixSquaresA0 5, dedekindSixSquaresA3 5) = (21, 14) := by
  decide +kernel

/-- For a cubic field `K` of negative discriminant (so non-normal over `ℚ`) and every `ε > 0`,
`S_2(x) = c₁x³ + c₂x³ log x + O(x^{25/9+ε})` for some constants `c₁, c₂`, and
`S_3(x) = x³ P₃(log x) + O(x^{79/27+ε})` for a polynomial `P₃` of degree `4`.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 1 (`integers-2025-A101-thm-1`). -/
public theorem_wanted sixSquaresDedekindMoment_two_three (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (hD : discr K < 0) :
    (∃ c₁ c₂ : ℝ, ∀ ε : ℝ, 0 < ε →
      (fun x => sixSquaresDedekindMoment K 2 x - c₁ * x ^ 3 - c₂ * x ^ 3 * Real.log x) =O[Filter.atTop]
        fun x => x ^ ((25 : ℝ) / 9 + ε)) ∧
    ∃ P : Polynomial ℝ, P.natDegree = 4 ∧ ∀ ε : ℝ, 0 < ε →
      (fun x => sixSquaresDedekindMoment K 3 x - x ^ 3 * P.eval (Real.log x)) =O[Filter.atTop]
        fun x => x ^ ((79 : ℝ) / 27 + ε)

/-- For a cubic field `K` of negative discriminant (so non-normal over `ℚ`), every `ℓ ≥ 4` and
every `ε > 0`, `S_ℓ(x) = x³ P_ℓ(log x) + O(x^{3 - 2/3^ℓ + ε})` for a polynomial `P_ℓ` of degree
`a_{0,ℓ} + a_{3,ℓ} - 1` (`P_ℓ` for even `ℓ`, `Q_ℓ` for odd `ℓ` in the paper).

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2 (`integers-2025-A101-thm-2`). -/
public theorem_wanted sixSquaresDedekindMoment_ge_four (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (hD : discr K < 0) (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    ∃ P : Polynomial ℝ, P.natDegree = dedekindSixSquaresA0 ℓ + dedekindSixSquaresA3 ℓ - 1 ∧
      ∀ ε : ℝ, 0 < ε →
        (fun x => sixSquaresDedekindMoment K ℓ x - x ^ 3 * P.eval (Real.log x)) =O[Filter.atTop]
          fun x => x ^ (3 - 2 / (3 : ℝ) ^ ℓ + ε)

end

end MetaMathlibExt
