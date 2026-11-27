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
public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.ModInverseSwitching
public import MathlibExt.NumberTheory.ModInverseSwitchingAbsEqHalvesIffSubEqTwoOfOdd
public import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe
public import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsSqAddLe

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

/-- **The Euclidean Bézout coefficients are least absolute inverses.** Let $m > n > 1$ be
integers, write $g = \gcd(m, n)$, and let $(r_i)$, $(s_i)$ and $N$ be Euclidean switching data
with $r_0 = m/g$ and $r_1 = n/g$. Then $s_2 m + s_1 n = g$, $s_2$ is the least absolute inverse
of $m/g$ modulo $n/g$, and $s_1$ is the least absolute inverse of $n/g$ modulo $m/g$.

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

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
