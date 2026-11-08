/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fibonacci numbers via Dirichlet convolution

Statements from Emil Daniel Schwab, "Fibonacci
Numbers via Dirichlet Convolution and Lucas Numbers
via Unitary Convolution", *Journal of Integer
Sequences* 28 (2025), Article 25.1.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schwab/schwab3.html>).

`fibAB a b` and `lucasAB a b` are the paper's
`F^{a, b}` and `L^{a, b}` over `ℂ` (`F_0 = 0`,
`F_1 = 1`, `L_0 = 2`, `L_1 = a`, both with recurrence
`s_{n+2} = a s_{n+1} + b s_n`; at integer parameters
these are the Lucas sequences `U(a, -b)`, `V(a, -b)`).
Every identity below was verified numerically over
random complex parameters. In Theorem 10,
`Δ = a^2 + 4b`; parts (b), (c), (d) are the
Fibonacci `(1, 1)`, Pell `(2, 1)` and Jacobsthal
`(1, 2)` specializations.

Not stated (see the source audit table): Lemma 6
(the polynomials `H_m^{a, b}`), Theorem 3 (the
calligraphic convolution sequences, with a truncated
case distinction), Theorem 13 (the roots `α, β` are
not defined in the extraction) and Theorem 15
(quoted from Szakács).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

/-- The `(a, b)`-Fibonacci numbers over `ℂ`:
`F_0 = 0`, `F_1 = 1`, `F_{n+2} = a F_{n+1} + b F_n`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
def fibAB (a b : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * fibAB a b (n + 1) + b * fibAB a b n

/-- `F_0 = 0` for the `(a, b)`-Fibonacci numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem fibAB_zero (a b : ℂ) : fibAB a b 0 = 0 := rfl

/-- `F_1 = 1` for the `(a, b)`-Fibonacci numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem fibAB_one (a b : ℂ) : fibAB a b 1 = 1 := rfl

/-- The two-step recurrence for the `(a, b)`-Fibonacci numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
theorem fibAB_add_two (a b : ℂ) (n : ℕ) :
    fibAB a b (n + 2) = a * fibAB a b (n + 1) + b * fibAB a b n :=
  rfl

/-- The `(a, b)`-Lucas numbers over `ℂ`:
`L_0 = 2`, `L_1 = a`, `L_{n+2} = a L_{n+1} + b L_n`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
def lucasAB (a b : ℂ) : ℕ → ℂ
  | 0 => 2
  | 1 => a
  | n + 2 => a * lucasAB a b (n + 1) + b * lucasAB a b n

/-- `L_0 = 2` for the `(a, b)`-Lucas numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem lucasAB_zero (a b : ℂ) : lucasAB a b 0 = 2 := rfl

/-- `L_1 = a` for the `(a, b)`-Lucas numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem lucasAB_one (a b : ℂ) : lucasAB a b 1 = a := rfl

/-- The two-step recurrence for the `(a, b)`-Lucas numbers.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
theorem lucasAB_add_two (a b : ℂ) (n : ℕ) :
    lucasAB a b (n + 2) =
      a * lucasAB a b (n + 1) + b * lucasAB a b n :=
  rfl

/-- **Corollary 4**: for `(a, b)`-Fibonacci and
`(a, b)`-Lucas numbers, and `Δ = a^2 + 4b ≠ 0`,
`Δ F_{m+1} = L_{m+2} + b L_m`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 4. -/
theorem_wanted disc_mul_fibAB (a b : ℂ) (hΔ : a ^ 2 + 4 * b ≠ 0)
    (m : ℕ) :
    (a ^ 2 + 4 * b) * fibAB a b (m + 1) =
      lucasAB a b (m + 2) + b * lucasAB a b m

/-- **Corollary 11**:
`∑_{i=0}^n (-b)^(n-i) F_{2i} = F_n F_{n+1}`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 11. -/
theorem_wanted sum_neg_b_pow_fibAB_even_prod (a b : ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-b) ^ (n - i) * fibAB a b (2 * i) =
      fibAB a b n * fibAB a b (n + 1)

/-- **Theorem 5(a)**: for `b ≠ 0`,
(i) `∑_{i=0}^n (-b)^(n-i) L_{2i+1} = F_{2n+2}` and
(ii) `∑_{i=0}^n (-b)^(n-i) L_{2i} = F_{2n+1} + (-b)^n`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 5(a). -/
theorem_wanted sum_neg_b_pow_lucasAB (a b : ℂ) (hb : b ≠ 0)
    (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * i + 1) =
      fibAB a b (2 * n + 2)) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * i) =
      fibAB a b (2 * n + 1) + (-b) ^ n)

/-- **Theorem 5(b)**: for `b ≠ 0`,
(i) `∑_{i=0}^n (-b)^(n-i) L_{2(i+m)+1}
  = F_{2(n+m)+2} + (-1)^n b^(n+1) F_{2m}
  = F_{n+m+1} L_{n+m+1} + (-1)^n b^(n+1) F_m L_m` and,
for `m ≥ 1`,
(ii) `∑_{i=0}^n (-b)^(n-i) L_{2(i+m)}
  = F_{2(n+m)+1} + (-1)^n b^(n+1) F_{2m-1}
  = F_{n+m+1} L_{n+m} + (-1)^n b^(n+1) F_m L_{m-1}`.
(The middle `H`-forms of the paper are the same
equalities via its Lemma 6.)

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 5(b). -/
theorem_wanted sum_neg_b_pow_lucasAB_shift (a b : ℂ) (hb : b ≠ 0)
    (m n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * (i + m) + 1) =
      fibAB a b (2 * (n + m) + 2) +
        (-1) ^ n * b ^ (n + 1) * fibAB a b (2 * m) ∧
    ∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * lucasAB a b (2 * (i + m) + 1) =
      fibAB a b (n + m + 1) * lucasAB a b (n + m + 1) +
        (-1) ^ n * b ^ (n + 1) * fibAB a b m * lucasAB a b m) ∧
    (1 ≤ m →
      ∑ i ∈ Finset.range (n + 1),
          (-b) ^ (n - i) * lucasAB a b (2 * (i + m)) =
        fibAB a b (2 * (n + m) + 1) +
          (-1) ^ n * b ^ (n + 1) * fibAB a b (2 * m - 1) ∧
      ∑ i ∈ Finset.range (n + 1),
          (-b) ^ (n - i) * lucasAB a b (2 * (i + m)) =
        fibAB a b (n + m + 1) * lucasAB a b (n + m) +
          (-1) ^ n * b ^ (n + 1) * fibAB a b m * lucasAB a b (m - 1))

/-- **Theorem 10(a)**: if `Δ = a^2 + 4b ≠ 0` then
(i) `∑_{i=0}^n (-b)^(n-i) F_{2i}
  = (L_{2n+1} + (-1)^(n+1) a b^n) / Δ` and
(ii) `∑_{i=0}^n (-b)^(n-i) F_{2i+1}
  = (L_{2n+2} + (-1)^n 2 b^(n+1)) / Δ`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(a). -/
theorem_wanted sum_neg_b_pow_fibAB_disc (a b : ℂ)
    (hΔ : a ^ 2 + 4 * b ≠ 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-b) ^ (n - i) * fibAB a b (2 * i) =
      (lucasAB a b (2 * n + 1) + (-1) ^ (n + 1) * a * b ^ n) /
        (a ^ 2 + 4 * b)) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * fibAB a b (2 * i + 1) =
      (lucasAB a b (2 * n + 2) + (-1) ^ n * 2 * b ^ (n + 1)) /
        (a ^ 2 + 4 * b))

/-- **Theorem 10(b)**: the Fibonacci case `(a, b) = (1, 1)`:
`∑ (-1)^i F_{2i} = ((-1)^n L_{2n+1} - 1) / 5`,
`∑ (-1)^i L_{2i} = (-1)^n F_{2n+1} + 1`,
`∑ (-1)^i F_{2i+1} = ((-1)^n L_{2n+2} + 2) / 5`,
`∑ (-1)^i L_{2i+1} = (-1)^n F_{2n+2}`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(b). -/
theorem_wanted sum_neg_one_pow_fib (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * fibAB 1 1 (2 * i) =
      ((-1) ^ n * lucasAB 1 1 (2 * n + 1) - 1) / 5) ∧
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * lucasAB 1 1 (2 * i) =
      (-1) ^ n * fibAB 1 1 (2 * n + 1) + 1) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * fibAB 1 1 (2 * i + 1) =
      ((-1) ^ n * lucasAB 1 1 (2 * n + 2) + 2) / 5) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB 1 1 (2 * i + 1) =
      (-1) ^ n * fibAB 1 1 (2 * n + 2))

/-- **Theorem 10(c)**: the Pell case `(a, b) = (2, 1)`
(`P` and `Q` in the paper):
`∑ (-1)^i P_{2i} = ((-1)^n Q_{2n+1} - 2) / 8`,
`∑ (-1)^i Q_{2i} = (-1)^n P_{2n+1} + 1`,
`∑ (-1)^i P_{2i+1} = ((-1)^n Q_{2n+2} + 2) / 8`,
`∑ (-1)^i Q_{2i+1} = (-1)^n P_{2n+2}`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(c). -/
theorem_wanted sum_neg_one_pow_pell (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * fibAB 2 1 (2 * i) =
      ((-1) ^ n * lucasAB 2 1 (2 * n + 1) - 2) / 8) ∧
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i) =
      (-1) ^ n * fibAB 2 1 (2 * n + 1) + 1) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * fibAB 2 1 (2 * i + 1) =
      ((-1) ^ n * lucasAB 2 1 (2 * n + 2) + 2) / 8) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i + 1) =
      (-1) ^ n * fibAB 2 1 (2 * n + 2))

/-- **Theorem 10(d)**: the Jacobsthal case
`(a, b) = (1, 2)` (`J` and `j` in the paper):
`∑ (-1)^i 2^(n-i) J_{2i} = ((-1)^n j_{2n+1} - 2^n) / 9`,
`∑ (-1)^i 2^(n-i) j_{2i} = (-1)^n J_{2n+1} + 2^n`,
`∑ (-1)^i 2^(n-i) J_{2i+1} = ((-1)^n j_{2n+2} + 2^(n+2)) / 9`,
`∑ (-1)^i 2^(n-i) j_{2i+1} = (-1)^n J_{2n+2}`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(d). -/
theorem_wanted sum_neg_one_pow_jacobsthal (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * fibAB 1 2 (2 * i) =
      ((-1) ^ n * lucasAB 1 2 (2 * n + 1) - 2 ^ n) / 9) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * lucasAB 1 2 (2 * i) =
      (-1) ^ n * fibAB 1 2 (2 * n + 1) + 2 ^ n) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * fibAB 1 2 (2 * i + 1) =
      ((-1) ^ n * lucasAB 1 2 (2 * n + 2) + 2 ^ (n + 2)) / 9) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * lucasAB 1 2 (2 * i + 1) =
      (-1) ^ n * fibAB 1 2 (2 * n + 2))

/-- **Corollary 9**: the `k`-Fibonacci case:
`∑_{i=0}^n (-1)^i L_{k, 2(i+m)}
  = (-1)^n F_{k, 2(n+m)+1} + F_{k, 2m-1}` (for
`m ≥ 1`; `F_{k, j}`, `L_{k, j}` are `fibAB k 1`,
`lucasAB k 1`).

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 9. -/
theorem_wanted sum_neg_one_pow_k_lucasAB (k : ℂ) (m n : ℕ)
    (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB k 1 (2 * (i + m)) =
      (-1) ^ n * fibAB k 1 (2 * (n + m) + 1) + fibAB k 1 (2 * m - 1)

/-- **Theorem 12**: for nonzero `c` with
`c^2 - a*c - b ≠ 0` and positive `n`,
`∑_{i=1}^n c^(n-i) F_i
  = (c^(n+1) - c F_{n+1} - b F_n) / (c^2 - a*c - b)`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 12. -/
theorem_wanted sum_c_pow_fibAB (a b c : ℂ) (hc : c ≠ 0)
    (hc2 : c ^ 2 - a * c - b ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, c ^ (n - i) * fibAB a b i =
      (c ^ (n + 1) - c * fibAB a b (n + 1) - b * fibAB a b n) /
        (c ^ 2 - a * c - b)

/-- **Corollary 14(a)**: if `b ≠ d` then
`∑_{i=1}^n L_{n-i}^{a,b} F_i^{a,d}
  = (L_{n+1}^{a,b} - L_{n+1}^{a,d}) / (b - d)
  = ∑_{i=1}^n L_{n-i}^{a,d} F_i^{a,b}`
(first equality in multiplied-out form).

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 14(a). -/
theorem_wanted convolution_lucasAB_fibAB (a b d : ℂ) (hbd : b ≠ d)
    (n : ℕ) :
    (b - d) * ∑ i ∈ Finset.Icc 1 n,
          lucasAB a b (n - i) * fibAB a d i =
        lucasAB a b (n + 1) - lucasAB a d (n + 1) ∧
      ∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i =
        ∑ i ∈ Finset.Icc 1 n, lucasAB a d (n - i) * fibAB a b i

/-- **Corollary 14(b)**: the specializations
(i) `∑_{i=1}^n L_{n-i} J_i = j_{n+1} - L_{n+1}
  = ∑_{i=1}^n j_{n-i} F_i` (Fibonacci/Jacobsthal),
(ii) `2 ∑_{i=1}^n P_i = (Q_{n+1} - 2) / 2
  = ∑_{i=1}^n i Q_{n-i}` (Pell), and
(iii) `∑_{i=1}^n L_{2(n-i)} (2^i - 1)
  = L_{2n+2} - 2^(n+1) - 1
  = ∑_{i=1}^n (2^(n-i) + 1) F_{2i}` (Fibonacci).

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 14(b). -/
theorem_wanted convolution_specializations (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, lucasAB 1 1 (n - i) * fibAB 1 2 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1) ∧
      ∑ i ∈ Finset.Icc 1 n, lucasAB 1 2 (n - i) * fibAB 1 1 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1)) ∧
    (2 * ∑ i ∈ Finset.Icc 1 n, fibAB 2 1 i =
        (lucasAB 2 1 (n + 1) - 2) / 2 ∧
      ∑ i ∈ Finset.Icc 1 n, (i : ℂ) * lucasAB 2 1 (n - i) =
        (lucasAB 2 1 (n + 1) - 2) / 2) ∧
    (∑ i ∈ Finset.Icc 1 n,
        lucasAB 1 1 (2 * (n - i)) * (2 ^ i - 1) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1 ∧
      ∑ i ∈ Finset.Icc 1 n, (2 ^ (n - i) + 1) * fibAB 1 1 (2 * i) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1)

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted
