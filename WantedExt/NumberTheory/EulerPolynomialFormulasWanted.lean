/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalizations of several explicit formulas for Euler polynomials

Statements from Nouara Mokhtari, Rachid Boumahdi, and
Farid Bencherif, "Generalizations of Several Explicit
Formulas for Euler Polynomials", *INTEGERS* 25 (2025),
Article A65
(<https://math.colgate.edu/~integers/vol25.html>).

The Euler polynomial `E_n(x)` is `eulerPoly n`, defined
through Bernoulli polynomials by
`E_n(x) = (2 / (n + 1)) (B_{n+1}(x) - 2^{n+1} B_{n+1}(x / 2))`.
The paper's generalized Stirling polynomial
`S(n, k, x) = (1 / k!) ∑_j (k choose j) (-1)^{k-j} (x + j)^n`
(Proposition 3.1) is `genStirlingPoly n k`. The
coefficients `α_k` of the paper's Lemma 2.2, the Taylor
coefficients of `(2 + 2z) / (2 + 2z + z^2)`, are
`eulerAlpha`, defined by the recurrence that generating
function imposes. The order-`α` Euler polynomials
`E_n^{(α)}(x)` (with generating function
`(2 / (e^t + 1))^α e^{xt}`) are `eulerPolyGen`, built
from the numbers `eulerNumGen α k = E_k^{(α)}(0)`, which
are defined by the coefficient recurrence of that
generating function's logarithmic derivative. All
formulas below were pinned and verified by exact rational
computation (the extraction of this paper flattens most
displays; the ranges and coefficients stated here are the
unique readings consistent with the surviving fragments).

Lemmas 2.1, 2.3 and 2.4 use the composition operator
`S(D) = ∑_k s_k D^k` of a formal power series `S`, acting on
polynomials (`powerSeriesOp`); Lemma 2.2's closed form for
`α_k` and Theorem 4.4 were read from the journal PDF.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/-- The Euler polynomial `E_n(x)`, defined through
Bernoulli polynomials by
`E_n(x) = (2 / (n + 1)) (B_{n+1}(x) - 2^{n+1} B_{n+1}(x / 2))`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (Euler polynomials). -/
noncomputable def eulerPoly (n : ℕ) : ℚ[X] :=
  (2 / (n + 1 : ℚ)) • (Polynomial.bernoulli (n + 1) -
    (2 : ℚ) ^ (n + 1) •
      (Polynomial.bernoulli (n + 1)).comp (C (1 / 2) * X))

/-- The generalized Stirling polynomial
`S(n, k, x) = (1 / k!) ∑_{j=0}^k (k choose j) (-1)^{k-j} (x + j)^n`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1 (definition). -/
noncomputable def genStirlingPoly (n k : ℕ) : ℚ[X] :=
  (1 / (Nat.factorial k : ℚ)) •
    ∑ j ∈ Finset.range (k + 1),
      ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) •
        (X + C (j : ℚ)) ^ n

/-- The Taylor coefficients `α_k` of
`(2 + 2z) / (2 + 2z + z^2)`, defined by the recurrence
`2 α_{k+2} + 2 α_{k+1} + α_k = 0` with `α_0 = 1`,
`α_1 = 0`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Lemma 2.2 (generating function). -/
def eulerAlpha : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | k + 2 => -eulerAlpha (k + 1) - eulerAlpha k / 2

/-- Auxiliary fuel-bounded computation for
`eulerNumGen`: `eulerNumGenAux α fuel n` evaluates the
recurrence using values at indices at most `fuel`; it
agrees with the intended numbers whenever `n ≤ fuel`. -/
noncomputable def eulerNumGenAux (α : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | fuel + 1, n + 1 =>
      -α * eulerNumGenAux α fuel n + (α / 2) *
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℂ) * eulerNumGenAux α fuel k *
            (((eulerPoly (n - k)).eval (0 : ℚ) : ℚ) : ℂ)

/-- The order-`α` Euler numbers `E_k^{(α)}(0)`, defined
by `E_0^{(α)}(0) = 1` and
`E_{n+1}^{(α)}(0) = -α E_n^{(α)}(0) +
  (α / 2) ∑_{k=0}^n (n choose k) E_k^{(α)}(0) E_{n-k}(0)`,
the coefficient recurrence of the generating function
`(2 / (e^t + 1))^α` (computed here through the
fuel-bounded `eulerNumGenAux`).

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerNumGen (α : ℂ) (n : ℕ) : ℂ :=
  eulerNumGenAux α n n

/-- The order-`α` Euler polynomial
`E_n^{(α)}(x) = ∑_{k=0}^n (n choose k) E_k^{(α)}(0) x^{n-k}`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerPolyGen (α : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((Nat.choose n k : ℂ) * eulerNumGen α k) * X ^ (n - k)

/-- **Proposition 3.1**: for every `n`,
`2^n E_n((x + 1) / 2) = ∑_{k=0}^n k! α_k S(n, k, x)`,
where `α_k` are the coefficients of Lemma 2.2 and
`S(n, k, x)` is the generalized Stirling polynomial.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1. -/
theorem_wanted eulerPoly_half_eq_sum (n : ℕ) :
    (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2) * (X + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          genStirlingPoly n k

/-- **Proposition 3.2**: for every complex `α` and
`n ≥ 1`,
`E_n^{(α)}(x) = (x - α / 2) E_{n-1}^{(α)}(x) +
  (α / 2) ∑_{k=0}^{n-2} (n - 1 choose k) (-1)^{n-k}
  E_{n-1-k}(0) E_k^{(α)}(x)`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.2. -/
theorem_wanted eulerPolyGen_recurrence (α : ℂ) (n : ℕ)
    (hn : 1 ≤ n) :
    eulerPolyGen α n =
      (X - C (α / 2)) * eulerPolyGen α (n - 1) +
        C (α / 2) * ∑ k ∈ Finset.range (n - 1),
          C ((Nat.choose (n - 1) k : ℂ) * (-1) ^ (n - k) *
            (((eulerPoly (n - 1 - k)).eval (0 : ℚ) : ℚ) : ℂ)) *
            eulerPolyGen α k

/-- **Theorem 4.1**: for `m ≥ 2` and `n ≤ 2m + 1`,
`E_n(x) = ∑_{k=0}^m (-1)^k (m + 1 choose k + 1) / 2^k
  ∑_{j=0}^k (k choose j) (x + j - (k + 1) / 2)^n`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.1. -/
theorem_wanted eulerPoly_eq_binomial_average (m n : ℕ)
    (hm : 2 ≤ m) (hn : n ≤ 2 * m + 1) :
    eulerPoly n =
      ∑ k ∈ Finset.range (m + 1),
        ((-1) ^ k * (Nat.choose (m + 1) (k + 1) : ℚ) /
            (2 : ℚ) ^ k) •
          ∑ j ∈ Finset.range (k + 1),
            (Nat.choose k j : ℚ) •
              (X + C ((j : ℚ) - (k + 1 : ℚ) / 2)) ^ n

/-- **Theorem 4.2**: for every positive integer `n`,
`2^n E_n(x) = ∑_{k=0}^n k! α_k S(n, k, 2x - 1)`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.2. -/
theorem_wanted eulerPoly_eq_sum_genStirling (n : ℕ)
    (hn : 1 ≤ n) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          (genStirlingPoly n k).comp (C 2 * X - 1)

/-- **Theorem 4.3**: for every `n ≥ 0`,
`2^n E_n(x) = ∑_{ℓ=0}^n (-1)^ℓ / (ℓ + 1)
  ∑_{k=0}^{n-ℓ} ((k + ℓ + 1)! / 2^k) (ℓ + 1 choose k)
  S(n, k + ℓ, 2x - 1)`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.3. -/
theorem_wanted eulerPoly_eq_double_sum (n : ℕ) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ l ∈ Finset.range (n + 1),
        ((-1) ^ l / (l + 1 : ℚ)) •
          ∑ k ∈ Finset.range (n - l + 1),
            ((Nat.factorial (k + l + 1) : ℚ) / (2 : ℚ) ^ k *
                (Nat.choose (l + 1) k : ℚ)) •
              (genStirlingPoly n (k + l)).comp (C 2 * X - 1)

/-- The composition operator `S(D) = ∑_k s_k D^k` of a formal
power series `S = ∑_k s_k z^k`, applied to a polynomial `p`
(the sum is finite: `D^k p = 0` for `k > deg p`).

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Section 1 (composition operators). -/
noncomputable def powerSeriesOp {R : Type*} [CommRing R]
    (S : PowerSeries R) (p : R[X]) : R[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    PowerSeries.coeff k S • derivative^[k] p

/-- `S(D)(1) = S(0)`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Section 1 (composition operators). -/
theorem powerSeriesOp_one {R : Type*} [CommRing R]
    (S : PowerSeries R) :
    powerSeriesOp S 1 = C (PowerSeries.constantCoeff S) := by
  simp [powerSeriesOp, Polynomial.smul_eq_C_mul]

/-- **Lemma 2.1**: for the polynomial sequence
`A_n(x) = S(D)(xⁿ)` associated with a composition operator
`S(D)` and nonzero `λ`:
`A_{n+1}(x) - x A_n(x) = S'(D)(xⁿ)`,
`A_n(λx) = λⁿ S(D/λ)(xⁿ)` and
`(-1)ⁿ A_n(λ - x) = e^{-λD} S(-D)(xⁿ)`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.1. -/
theorem_wanted powerSeriesOp_appell_identities
    (S : PowerSeries ℂ) (lam : ℂ) (hlam : lam ≠ 0) (n : ℕ) :
    powerSeriesOp S (X ^ (n + 1)) - X * powerSeriesOp S (X ^ n) =
        powerSeriesOp (PowerSeries.derivative S) (X ^ n) ∧
      (powerSeriesOp S (X ^ n)).comp (C lam * X) =
        lam ^ n • powerSeriesOp (PowerSeries.rescale lam⁻¹ S) (X ^ n) ∧
      (-1 : ℂ) ^ n • (powerSeriesOp S (X ^ n)).comp (C lam - X) =
        powerSeriesOp
          (PowerSeries.rescale (-lam) (PowerSeries.exp ℂ) *
            PowerSeries.rescale (-1) S) (X ^ n)

/-- **Lemma 2.2**: `(2 + 2z) / (2 + 2z + z²) = ∑ α_k z^k`
with `α_k = ((k + 1) / 2^k) ∑_{ℓ=0}^k (-1)^ℓ (2^ℓ / (ℓ + 1))
(ℓ + 1 choose k - ℓ)`; the generating function is stated
multiplicatively.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.2. -/
theorem_wanted eulerAlpha_gf_and_closed_form :
    PowerSeries.mk eulerAlpha *
          (2 + 2 * PowerSeries.X + PowerSeries.X ^ 2) =
        2 + 2 * PowerSeries.X ∧
      ∀ k : ℕ, eulerAlpha k =
        (k + 1 : ℚ) / 2 ^ k *
          ∑ l ∈ Finset.range (k + 1),
            (-1) ^ l * 2 ^ l / (l + 1 : ℚ) *
              (Nat.choose (l + 1) (k - l) : ℚ)

/-- **Lemma 2.3** (corrected reading): with
`S(z) = 2e^z / (1 + e^{2z}) = e^z S_E(2z)`,
`2ⁿ E_n((x + 1)/2) = S(D)(xⁿ)`, and with `Δ = e^z - 1`,
`S = (2 + 2Δ)/(2 + 2Δ + Δ²) = ∑_k α_k Δ^k`. The paper prints
the denominator as `2 + e^{2D}`, which contradicts its own
`e^D S_E(2D)` and `2 + 2Δ + Δ²` (constant terms `2/3` versus
`1`); `1 + e^{2D}` is used.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.3. -/
theorem_wanted eulerPoly_half_appell :
    let S : PowerSeries ℚ := (2 * PowerSeries.exp ℚ) *
      (1 + PowerSeries.exp ℚ ^ 2)⁻¹
    let Δ : PowerSeries ℚ := PowerSeries.exp ℚ - 1
    (∀ n : ℕ, (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2) * (X + 1)) =
        powerSeriesOp S (X ^ n)) ∧
      S * (2 + 2 * Δ + Δ ^ 2) = 2 + 2 * Δ ∧
      S = (PowerSeries.mk eulerAlpha).subst Δ

/-- **Lemma 2.4**: `S(D) M_x - M_x S(D) = S'(D)` on
polynomials, `M_x` being multiplication by `x`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.4. -/
theorem_wanted powerSeriesOp_mul_X_sub {R : Type*} [CommRing R]
    (S : PowerSeries R) (p : R[X]) :
    powerSeriesOp S (X * p) - X * powerSeriesOp S p =
      powerSeriesOp (PowerSeries.derivative S) p

/-- **Theorem 4.4**: for every complex `α` and
`m ≥ ⌊n/2⌋`, `E_n^{(α)}(x) = ∑_{k=0}^m ((-1)^k / 2^{n+k})
(α + k - 1 choose k) ∑_{j=0}^{2k} (-1)^j (2k choose j)
(2x - α - k + j)ⁿ`, with
`(α + k - 1 choose k) = α(α + 1)⋯(α + k - 1)/k!`.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", INTEGERS 25 (2025), Article A65, Theorem 4.4. -/
theorem_wanted eulerPolyGen_eq_sum (α : ℂ) (n m : ℕ)
    (hm : n / 2 ≤ m) :
    eulerPolyGen α n =
      ∑ k ∈ Finset.range (m + 1),
        C ((-1) ^ k / (2 : ℂ) ^ (n + k) *
            ((ascPochhammer ℂ k).eval α / (Nat.factorial k : ℂ))) *
          ∑ j ∈ Finset.range (2 * k + 1),
            C ((-1) ^ j * (Nat.choose (2 * k) j : ℂ)) *
              (C 2 * X + C ((j : ℂ) - α - k)) ^ n

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
