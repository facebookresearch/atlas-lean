/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ExtendedContinuant
public import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantEuler
public import MathlibExt.NumberTheory.ExtendedContinuantOddSilentTerms
public import MathlibExt.NumberTheory.ExtendedContinuantSilentTermsTableOneModSix
public import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantBennett

/-!
# Extended continuants and bi-infinite periodic continued fractions

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.

For a bi-infinite integer sequence `x : ℤ → ℤ`, `extendedContinuant x a b` is the paper's
extended continuant `K_a(x)_b^{a+b}` of order `a ∈ ℤ` on the consecutive terms starting at
index `b` (Definitions 3 and 4, right-adjusting recurrence): `K_{-2} = 0`, `K_{-1} = 1`, and
`K_a = x_{b+a} K_{a-1} + K_{a-2}` for every integer order `a`
(`extendedContinuant_recurrence`).

In Sections 4–6 a bi-infinite sequence `x` has raw rational convergents
`k_n = K_n(x)_0 / K_{n-1}(x)_1` (numerator and denominator kept separately); `c_i` and `d_i`
are the raw convergents `K_i(y)_0 / K_{i-1}(y)_1` and `K_i(z)_0 / K_{i-1}(z)_1` of the
eastbound SCF terms `y` of `α` and `z` of `ᾱ` (only indices `≥ 0` of `y`, `z` matter).
Strict equivalence of raw rationals is equality of numerators and of denominators. The
statements below keep only the strict-equivalence hypotheses on the convergents; the
periodicity and limit conditions of a BpCF (Definition 5) are not used by the paper's proofs
and are dropped, so each statement applies to every bi-infinite integer sequence.
The same applies to `MetaMathlibExt.oddSilent_terms`, which is in
`MathlibExt.NumberTheory.ExtendedContinuantOddSilentTerms`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bennett's continuant identity for nonnegative indices.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all nonnegative integers $k$, $\ell$, $m$, $n$,
$$(-1)^{k+\ell} K_{n-k-2}(x)_k K_{m-\ell-2}(x)_\ell +
(-1)^{\ell+m} K_{n-\ell-2}(x)_\ell K_{k-m-2}(x)_m +
(-1)^{m+k} K_{n-m-2}(x)_m K_{\ell-k-2}(x)_k = 0.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett, 1939). -/
public theorem_wanted extendedContinuant_bennett_nat (x : ℤ → ℤ) (k ℓ m n : ℕ) :
    ((k + ℓ : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - k - 2) k *
        extendedContinuant x ((m : ℤ) - ℓ - 2) ℓ +
      ((ℓ + m : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - ℓ - 2) ℓ *
        extendedContinuant x ((k : ℤ) - m - 2) m +
      ((m + k : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - m - 2) m *
        extendedContinuant x ((ℓ : ℤ) - k - 2) k = 0

/-- **Terms of a $1$-silent sequence.** Let $x, y, z : \mathbb{Z} \to \mathbb{Z}$ be bi-infinite
integer sequences and write $K_a(x)_b$ for the extended continuant of order $a$ with start index
$b$. Suppose that for every natural number $i$, $K_i(x)_0 = K_i(y)_0$,
$K_{i-1}(x)_1 = K_{i-1}(y)_1$, $K_{-i-2}(x)_0 = K_i(z)_0$ and $K_{-i-3}(x)_1 = K_{i-1}(z)_1$.
Then $x_n = y_n$ for every $n \ge 0$, $x_{-n} = -z_n$ for every $n \ge 1$, and $z_0 = 0$.

In the paper's terms the hypotheses say that the raw convergents $k_i = K_i(x)_0 / K_{i-1}(x)_1$
of $x$ are strictly equivalent (equal numerators and equal denominators) to the raw convergents
$c_i$ of $y$, and $k_{-i-2}$ to the raw convergents $d_i$ of $z$, for all $i \ge 0$. The
conclusion $z_0 = 0$ matches the paper's $0 < \bar\alpha < 1$ for the EA-generated SCF of the
irrational $\bar\alpha$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 5. -/
public theorem_wanted oneSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 2) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 3) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧ (∀ n : ℕ, 1 ≤ n → x (-(n : ℤ)) = -z n) ∧ z 0 = 0

/-- **The conjugate continued fraction is not purely periodic.** Let $P$, $Q$ and $D$ be integers
with $D > 0$ not a perfect square and $Q > 0$, and let $\bar\alpha = (P - \sqrt{D})/Q$. Then the
simple continued fraction $[a_0; a_1, a_2, \dots]$ of $\bar\alpha$, which is infinite because
$\bar\alpha$ is irrational, is not purely periodic: there is no integer $s \ge 1$ with
$a_{n+s} = a_n$ for all $n \ge 0$. Here $a_0 = \lfloor \bar\alpha \rfloor$ is included.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Lemma 3. -/
public theorem_wanted conjugate_continuedFraction_not_purelyPeriodic (P Q D : ℤ) (hD : 0 < D)
    (hsq : ¬ IsSquare D) (hQ : 0 < Q) :
    ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
      (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) (n + s)).map (·.b) =
        (GenContFract.IntFractPair.stream (((P : ℝ) - √(D : ℝ)) / Q) n).map (·.b)

end

end MetaMathlibExt
