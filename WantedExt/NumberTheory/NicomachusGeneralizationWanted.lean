/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A balanced three or more-term generalization of Nicomachus' identity

Statements from Seon-Hong Kim and Kenneth B. Stolarsky,
"A Balanced Three or More-term Generalization of Nicomachus'
Identity", *INTEGERS* 26 (2026), Article A98
(<https://math.colgate.edu/~integers/aa98/aa98.pdf>).

Here `Tₘ = m(m+1)/2` is the `m`-th triangular number.  Theorem 1
gives two polynomial identities (7) and (8).  In (7) the summand of
`P_{m,o}` is `(4j + 1 + jx)·((j+1)(j-2) + j²x)`; this grouping,
ambiguous in plain-text extraction of the paper, is the one
satisfying (7) (verified by exact rational computation).
`P_{m,e}` in (8) is defined in the paper by substituting `-m - 1`
for `m` in the polynomial expansion of `P_{m,o}`; the expansion
used here is the Faulhaber expansion
`P_{m,o}(x) = Σ_p c_p(x) S_p(m)` with
`(c₀, c₁, c₂, c₃) = (-2, -9 - 2x, -3, 4 + 5x + x²)` and
`S_p(m) = Σ_{j=0}^m j^p`, which agrees with the defining sum for
natural `m` (again verified by exact rational computation).

The numbers `α_k` of Equation (12) are the continued-fraction
convergents `[1; 6, 3, …, 6, 3]` with `2k - 2` partial quotients
after the semicolon, so `α₁ = 1`; they are defined here by the
equivalent recurrence (13) from the paper,
`α_{k+1} = (15 + 7α_k)/(13 + 6α_k)`.

The integers `u_k` are the coefficients in Proposition 1: `u_k` is
the coefficient of `x^{k-1}` in
`(1 + 502x + x²)/((1 - x)(1 - 398x + x²))`, defined here directly
as a formal power series coefficient over `ℚ`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

/-- The `m`-th triangular number `Tₘ = m(m+1)/2`, as a real. -/
noncomputable def nicomachusTriangular (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1) / 2

/-- `L_{m,o}(x) = Σ_{j=1}^m (2j-1)³ + x³ + Σ_{j=2}^m ((2j-2)+(j-1)x)³`. -/
def nicomachusLOdd (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 2 m, ((2 * (j : ℝ) - 2) + ((j : ℝ) - 1) * x) ^ 3

/-- `R_{m,o}(x) = (T_{2m-1} + (1 + T_{m-1})x)²`. -/
noncomputable def nicomachusROdd (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m - 1) +
    (1 + nicomachusTriangular (m - 1)) * x) ^ 2

/-- `P_{m,o}(x) = Σ_{j=0}^m (4j + 1 + jx)·((j+1)(j-2) + j²x)`. -/
def nicomachusPOdd (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 0 m,
    (4 * (j : ℝ) + 1 + (j : ℝ) * x) *
      (((j : ℝ) + 1) * ((j : ℝ) - 2) + (j : ℝ) ^ 2 * x)

/-- `L_{m,e}(x) = Σ_{j=1}^m (2j-1)³ + x³ + Σ_{j=1}^m (2j + jx)³`. -/
def nicomachusLEven (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) + (j : ℝ) * x) ^ 3

/-- `R_{m,e}(x) = (T_{2m} + (1 + T_m)x)²`. -/
noncomputable def nicomachusREven (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m) +
    (1 + nicomachusTriangular m) * x) ^ 2

/-- The polynomial expansion of `P_{m,o}(x)` in `m`, obtained from
the defining sum by the Faulhaber formulas for `Σ_{j=0}^m j^p`,
`p ≤ 3`; it agrees with `nicomachusPOdd` at natural `m`. -/
noncomputable def nicomachusPClosed (m x : ℝ) : ℝ :=
  (-2) * (m + 1) + (-9 - 2 * x) * (m * (m + 1) / 2) +
    (-3) * (m * (m + 1) * (2 * m + 1) / 6) +
      (4 + 5 * x + x ^ 2) * (m * (m + 1) / 2) ^ 2

/-- `P_{m,e}(x)`, defined in the paper by substituting `-m - 1`
for `m` in the polynomial expansion of `P_{m,o}(x)`. -/
noncomputable def nicomachusPEven (m : ℕ) (x : ℝ) : ℝ :=
  nicomachusPClosed (-(m : ℝ) - 1) x

/-- The numbers `α_k` of Equation (12): the continued-fraction
convergents `[1; 6, 3, …, 6, 3]` with `2k - 2` partial quotients
after the semicolon.  Defined by the paper's recurrence (13),
with `α₁ = 1`; the value at `0` is a dummy. -/
def nicomachusAlpha : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (k + 2) => (15 + 7 * nicomachusAlpha (k + 1)) /
      (13 + 6 * nicomachusAlpha (k + 1))

/-- The integers `u_k` of Proposition 1: `u_k` is the coefficient
of `x^{k-1}` in the power series expansion of
`(1 + 502x + x²)/((1 - x)(1 - 398x + x²))`. -/
noncomputable def nicomachusU (k : ℕ) : ℚ :=
  PowerSeries.coeff (k - 1)
    ((1 + 502 * PowerSeries.X + PowerSeries.X ^ 2) *
      ((1 - PowerSeries.X) *
        (1 - 398 * PowerSeries.X + PowerSeries.X ^ 2))⁻¹)

/-- **Theorem 1, odd case**: `L_{m+1,o}(x) - R_{m+1,o}(x) =
x·P_{m,o}(x) - x² + x³` for `m ≥ 2` (Equation (7)).

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 1. -/
theorem_wanted nicomachusLOdd_sub_ROdd_succ_eq (m : ℕ) (hm : 2 ≤ m)
    (x : ℝ) :
    nicomachusLOdd (m + 1) x - nicomachusROdd (m + 1) x =
      x * nicomachusPOdd m x - x ^ 2 + x ^ 3

/-- **Theorem 1, even case**: `L_{m,e}(x) - R_{m,e}(x) =
x·P_{m,e}(x) - x² + x³` for `m ≥ 2` (Equation (8)).

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 1. -/
theorem_wanted nicomachusLEven_sub_REven_eq (m : ℕ) (hm : 2 ≤ m)
    (x : ℝ) :
    nicomachusLEven m x - nicomachusREven m x =
      x * nicomachusPEven m x - x ^ 2 + x ^ 3

/-- **Proposition 1, closed form (14)**:
`u_k = (5(10 - 3√11)^{2k-1} + 5(10 + 3√11)^{2k-1} - 56)/44`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem_wanted nicomachusU_eq_closedForm (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU k : ℝ) =
      (5 * (10 - 3 * Real.sqrt 11) ^ (2 * k - 1) +
        5 * (10 + 3 * Real.sqrt 11) ^ (2 * k - 1) - 56) / 44

/-- **Proposition 1, recurrence (15)**:
`u_{k+1} = 252 + 199u_k + 30√((3 + 2u_k)(23 + 22u_k))`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem_wanted nicomachusU_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU (k + 1) : ℝ) =
      252 + 199 * (nicomachusU k : ℝ) +
        30 * Real.sqrt ((3 + 2 * (nicomachusU k : ℝ)) *
          (23 + 22 * (nicomachusU k : ℝ)))

/-- **Proposition 2 (16)**:
`α_k = (-1 + √(11 - 10/(3 + 2u_k)))/2` for `k ≥ 1`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 2. -/
theorem_wanted nicomachusAlpha_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusAlpha k : ℝ) =
      (-1 + Real.sqrt (11 - 10 / (3 + 2 * (nicomachusU k : ℝ)))) / 2

/-- **Theorem 2 (18)**: with `(a, b, c) = (1, α_k, -(1 + α_k))`
and `(d, e, f) = (-a, -c, -b)` as in (17),
`Σ_{j=1}^m (a + bj + cj²)(d + ej + fj²)
= T_{m-1}·((1 + m)(2 - 3m²)/(3(3 + 2u_k)) + (3 + 2m)T_{m-1})`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 2. -/
theorem_wanted sum_quadratic_mul_quadratic_eq (k : ℕ) (hk : 1 ≤ k)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
      (1 + (nicomachusAlpha k : ℝ) * (j : ℝ) -
          (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) ^ 2) *
        (-1 + (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) -
          (nicomachusAlpha k : ℝ) * (j : ℝ) ^ 2)) =
      nicomachusTriangular (m - 1) *
        (((1 + (m : ℝ)) * (2 - 3 * (m : ℝ) ^ 2) /
          (3 * (3 + 2 * (nicomachusU k : ℝ)))) +
            (3 + 2 * (m : ℝ)) * nicomachusTriangular (m - 1))

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
