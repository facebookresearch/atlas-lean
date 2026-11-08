/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Euclidean algorithm as a sequence of modular inverse
switching formulas

Statements from Spiros Konstantogiannis, "The Euclidean Algorithm
as a Sequence of Modular Inverse Switching Formulas", *INTEGERS*
24 (2024), Article A29
(<https://math.colgate.edu/~integers/y29/y29.pdf>,
DOI 10.5281/zenodo.10821707).

The paper's `a⁻¹ mod n` denotes an integer inverse of `a` modulo
`n`; congruences below are `Int.ModEq`. The *least absolute
inverse* of `a` modulo `n` is the unique inverse lying in the
complete system of least absolute residues (paper §3);
`IsLeastAbsInverse` packages this as the inverse congruence
together with the half-open bounds `-n < 2x ≤ n`. For odd `n`
this is `|x| ≤ (n-1)/2`; for even `n` the paper lists both
endpoint choices `±n/2` as complete systems, and the bounds
here resolve the ambiguity to `+n/2`, which is also what the
Euclidean recurrence produces (its `s_{N+1} = 1` at a final
modulus `2`).

Section 3 of the paper applies the Euclidean algorithm to the
coprime pair `r₀ = m/gcd(m,n)`, `r₁ = n/gcd(m,n)` (with
`m > n > 1` and neither dividing the other), obtains remainders
`r₀ > r₁ > ⋯ > r_{n+1} = 1` with
`r_{i-1} = q_i r_i + r_{i+1}` (Equation (4)), and defines
inverses `s_j = r_j⁻¹` (the inverse of `r_j` modulo `r_{j-1}`)
through the switching relations
`s_{i+1} r_{i-1} + s_i r_i = 1` (Equation (5)) with
`s_{n+1} = 1` (Equation (6)); the pair of Bézout coefficients
provided by the Euclidean algorithm for `(m, n)` is then
`(s₂, s₁)`. Rather than formalizing the algorithm itself, the
sequence statements below take this data as hypotheses, bundled
in `IsEuclidSwitchSeq` (note the paper's sequence length is
called `n`, here `N` to avoid clashing with the second input
integer).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

/-- `x` is the paper's *least absolute inverse* of `a` modulo
the positive integer `n`: an inverse of `a` modulo `n` in the
half-open least-absolute-residue interval `-n/2 < x ≤ n/2`,
i.e. `-n < 2x ≤ n` (for even `n` the endpoint is `+n/2`, not
`-n/2`; see the module header). -/
def IsLeastAbsInverse (x a : ℤ) (n : ℕ) : Prop :=
  x * a ≡ 1 [ZMOD (n : ℤ)] ∧ -(n : ℤ) < 2 * x ∧ 2 * x ≤ (n : ℤ)

/-- The Euclidean-remainder and inverse data of §3 of the paper:
`r₀ > r₁ > ⋯ > r_{N+1} = 1` positive, the division relations
`r_{i-1} = q_i r_i + r_{i+1}` with positive quotients
(Equation (4)), the switching relations
`s_{i+1} r_{i-1} + s_i r_i = 1` (Equation (5)), and
`s_{N+1} = 1` (Equation (6)). -/
def IsEuclidSwitchSeq (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) : Prop :=
  0 < N ∧
    (∀ i : ℕ, i ≤ N + 1 → 0 < r i) ∧
    (∀ i : ℕ, i ≤ N → r (i + 1) < r i) ∧
    r (N + 1) = 1 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ N → ∃ q : ℕ, 0 < q ∧
      r (i - 1) = q * r i + r (i + 1)) ∧
    s (N + 1) = 1 ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ N →
      s (i + 1) * (r (i - 1) : ℤ) + s i * (r i : ℤ) = 1

/-- **Lemma 1**: if `m, n` are coprime positive integers and
`(x, y)` is a pair of Bézout coefficients for `(m, n)`, i.e.
`xm + yn = 1`, then `x` is an inverse of `m` modulo `n` and `y`
is an inverse of `n` modulo `m`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 1. -/
theorem_wanted bezout_coeffs_are_inverses
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (x y : ℤ) (h : x * (m : ℤ) + y * (n : ℤ) = 1) :
    x * (m : ℤ) ≡ 1 [ZMOD (n : ℤ)] ∧
      y * (n : ℤ) ≡ 1 [ZMOD (m : ℤ)]

/-- **Lemma 2** (modular inverse switching): if `m, n` are
positive integers and both `m` and the integer `t` are coprime
to `n`, then `m` differs from `t` by a multiple of `n` if and
only if there are integer representatives `x` of `t⁻¹ mod n`
and `y` of `n⁻¹ mod m` with `xm + yn = 1` (Equation (3), with
the paper's inverse notation read through representatives).

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 2. -/
theorem_wanted exists_eq_mul_add_iff_switching
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℤ)
    (hmn : Nat.Coprime m n) (htn : Nat.Coprime t.natAbs n) :
    (∃ k : ℤ, (m : ℤ) = k * (n : ℤ) + t) ↔
      ∃ x y : ℤ, x * t ≡ 1 [ZMOD (n : ℤ)] ∧
        y * (n : ℤ) ≡ 1 [ZMOD (m : ℤ)] ∧
        x * (m : ℤ) + y * (n : ℤ) = 1

/-- **Lemma 3**: if for some `j ∈ {1, …, N}` the inverse
`s_{j+1}` is the least absolute inverse of `r_{j+1}` modulo
`r_j`, then `s_j` is the least absolute inverse of `r_j` modulo
`r_{j-1}`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 3. -/
theorem_wanted isLeastAbsInverse_succ_imp
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ N)
    (h : IsLeastAbsInverse (s (j + 1)) (r (j + 1) : ℤ) (r j)) :
    IsLeastAbsInverse (s j) (r j : ℤ) (r (j - 1))

/-- **Corollary 1**: for every `i = 1, …, N+1`, the inverse
`s_i` is the least absolute inverse of `r_i` modulo `r_{i-1}`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Corollary 1. -/
theorem_wanted isLeastAbsInverse_all
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N) :
    ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsLeastAbsInverse (s i) (r i : ℤ) (r (i - 1))

/-- **Lemma 4**: the pair `(s₂, s₁)` of Bézout coefficients
provided by the Euclidean algorithm for `(m, n)` (where
`r₀ = m/gcd(m,n)`, `r₁ = n/gcd(m,n)`) satisfies
`s₂ m + s₁ n = gcd(m, n)`, the coefficient `s₂` of `m` is the
least absolute inverse of `m/gcd(m,n)` modulo `n/gcd(m,n)`, and
the coefficient `s₁` of `n` is the least absolute inverse of
`n/gcd(m,n)` modulo `m/gcd(m,n)`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 4. -/
theorem_wanted euclid_bezout_coeffs_leastAbsInverse
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n) :
    s 2 * (m : ℤ) + s 1 * (n : ℤ) = (Nat.gcd m n : ℤ) ∧
      IsLeastAbsInverse (s 2) ((m / Nat.gcd m n : ℕ) : ℤ)
        (n / Nat.gcd m n) ∧
      IsLeastAbsInverse (s 1) ((n / Nat.gcd m n : ℕ) : ℤ)
        (m / Nat.gcd m n)

/-- **Lemma 5**: the pair `(s₂, s₁)` of Bézout coefficients
provided by the Euclidean algorithm for `(m, n)` has each
coefficient least in absolute value among all Bézout pairs.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 5. -/
theorem_wanted euclid_bezout_coeffs_abs_le
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n)
    (x y : ℤ) (hxy : x * (m : ℤ) + y * (n : ℤ) = (Nat.gcd m n : ℤ)) :
    |s 2| ≤ |x| ∧ |s 1| ≤ |y|

/-- **Corollary 2** (Rankin): the pair `(s₂, s₁)` of Bézout
coefficients provided by the Euclidean algorithm for `(m, n)`
is, as a point in the plane, nearest to the origin among all
Bézout pairs (stated through squared distances).

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Corollary 2. -/
theorem_wanted euclid_bezout_coeffs_sq_add_le
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n)
    (x y : ℤ) (hxy : x * (m : ℤ) + y * (n : ℤ) = (Nat.gcd m n : ℤ)) :
    s 2 ^ 2 + s 1 ^ 2 ≤ x ^ 2 + y ^ 2

/-- **Lemma 6**: if `r₀` and `r₁` are both odd, then
`|s₁| = (r₀ - 1)/2` and `|s₂| = (r₁ - 1)/2` hold simultaneously
if and only if `r₀ - r₁ = 2`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 6. -/
theorem_wanted abs_eq_halves_iff_sub_eq_two_of_odd
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Odd (r 0)) (h1 : Odd (r 1)) :
    (2 * |s 1| = (r 0 : ℤ) - 1 ∧ 2 * |s 2| = (r 1 : ℤ) - 1) ↔
      r 0 = r 1 + 2

/-- **Lemma 7**: if `r₀` is odd and `r₁` is even, then
`|s₁| = (r₀ - 1)/2` and `|s₂| = r₁/2` hold simultaneously if
and only if `r₁ = 2`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 7. -/
theorem_wanted abs_eq_halves_iff_eq_two_of_odd_even
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Odd (r 0)) (h1 : Even (r 1)) :
    (2 * |s 1| = (r 0 : ℤ) - 1 ∧ 2 * |s 2| = (r 1 : ℤ)) ↔
      r 1 = 2

/-- **Lemma 8**: if `r₀` is even and `r₁` is odd, then at least
one of the inequalities `|s₁| ≤ r₀/2` and `|s₂| ≤ (r₁ - 1)/2`
is strict.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 8. -/
theorem_wanted abs_lt_of_even_odd
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Even (r 0)) (h1 : Odd (r 1)) :
    2 * |s 1| < (r 0 : ℤ) ∨ 2 * |s 2| < (r 1 : ℤ) - 1

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
