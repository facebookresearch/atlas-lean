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

/-- **Bennett's continuant identity for all integer indices.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all integers $k$, $\ell$, $m$, $n$,
$$(-1)^{k+\ell} K_{n-k-2}(x)_k K_{m-\ell-2}(x)_\ell +
(-1)^{\ell+m} K_{n-\ell-2}(x)_\ell K_{k-m-2}(x)_m +
(-1)^{m+k} K_{n-m-2}(x)_m K_{\ell-k-2}(x)_k = 0.$$

This extends Bennett's identity from nonnegative to arbitrary integer indices.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 3. -/
public theorem_wanted extendedContinuant_bennett (x : ℤ → ℤ) (k ℓ m n : ℤ) :
    ((k + ℓ).negOnePow : ℤ) * extendedContinuant x (n - k - 2) k *
        extendedContinuant x (m - ℓ - 2) ℓ +
      ((ℓ + m).negOnePow : ℤ) * extendedContinuant x (n - ℓ - 2) ℓ *
        extendedContinuant x (k - m - 2) m +
      ((m + k).negOnePow : ℤ) * extendedContinuant x (n - m - 2) m *
        extendedContinuant x (ℓ - k - 2) k = 0

/-- **Euler's continuant identity for extended continuants.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all integers $h$, $k$, $\ell$, $m$,
$$K_{\ell+m}(x)_h K_{k-1}(x)_{\ell+h+1} - K_{m-1}(x)_{\ell+h+1} K_{k+\ell}(x)_h =
(-1)^k K_{m-k-2}(x)_{k+\ell+h+2} K_{\ell-1}(x)_h.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 1. -/
public theorem_wanted extendedContinuant_euler (x : ℤ → ℤ) (h k ℓ m : ℤ) :
    extendedContinuant x (ℓ + m) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
        extendedContinuant x (m - 1) (ℓ + h + 1) * extendedContinuant x (k + ℓ) h =
      (k.negOnePow : ℤ) * extendedContinuant x (m - k - 2) (k + ℓ + h + 2) *
        extendedContinuant x (ℓ - 1) h

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

/-- **Terms of 3-silent sequences.** Let $x, y, z : \mathbb{Z} \to \mathbb{Z}$ be bi-infinite
integer sequences, and write $K_a(x)_b$ for the extended continuant of $x$ of order $a$ with start
index $b$. Suppose that for every natural number $i$ we have $K_i(x)_0 = K_i(y)_0$,
$K_{i-1}(x)_1 = K_{i-1}(y)_1$, $K_{-i-4}(x)_0 = K_i(z)_0$ and
$K_{-i-5}(x)_1 = K_{i-1}(z)_1$, and that $x_{-1} = 0$. Then $x_n = y_n$ for every $n \ge 0$, and
$x_{-n} = -z_{n-2}$ for every $n \ge 2$.

In the paper's terms, the hypotheses say that the raw convergents
$k_n = K_n(x)_0 / K_{n-1}(x)_1$ of $x$ satisfy $k_i \doteq c_i$ and $k_{-i-4} \doteq d_i$ for all
$i \ge 0$, where $c_i$ and $d_i$ are the corresponding raw convergents of $y$ and $z$ and $\doteq$
is equality of numerators and of denominators; the periodicity and limit conditions of a
bi-infinite periodic continued fraction are not assumed.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 6 and its proof (option 2, `x_{-1} = 0`). -/
public theorem_wanted threeSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 4) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 5) 1 = extendedContinuant z ((i : ℤ) - 1) 1)
    (hx : x (-1) = 0) :
    (∀ n : ℕ, x n = y n) ∧ ∀ n : ℕ, 2 ≤ n → x (-(n : ℤ)) = -z ((n : ℤ) - 2)

/-- **Terms of a $\sigma$-silent sequence for odd $\sigma \ge 5$.** Let $\sigma \ge 5$ be an odd
integer, let $x, y, z : \mathbb{Z} \to \mathbb{Z}$ be bi-infinite integer sequences, and write
$K_a(x)_b$ for the extended continuant of order $a$ with start index $b$. Suppose that for every
natural number $i$, $K_i(x)_0 = K_i(y)_0$, $K_{i-1}(x)_1 = K_{i-1}(y)_1$,
$K_{-i-\sigma-1}(x)_0 = K_i(z)_0$ and $K_{-i-\sigma-2}(x)_1 = K_{i-1}(z)_1$. Then $x_n = y_n$ for
every $n \ge 0$,
$x_{-\sigma+2} x_{-\sigma+1} = -1 + K_{\sigma-6}(x)_{-\sigma+4} + z_0 K_{\sigma-5}(x)_{-\sigma+4}$,
$x_{-\sigma+1} = -K_{\sigma-5}(x)_{-\sigma+3} - z_0 K_{\sigma-4}(x)_{-\sigma+3}$,
$x_{-\sigma} = -K_{\sigma-3}(x)_{-\sigma+2} - z_1$, and $x_{-n} = -z_{n-\sigma+1}$ for every integer
$n \ge \sigma + 1$.

The paper states the second formula as a quotient for $x_{-\sigma+2}$; here it is multiplied out.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 7. -/
public theorem_wanted oddSilent_terms (x y z : ℤ → ℤ) (σ : ℤ) (hσ : Odd σ) (h5 : 5 ≤ σ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧
      x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
        z 0 * extendedContinuant x (σ - 5) (-σ + 4) ∧
      x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
        z 0 * extendedContinuant x (σ - 4) (-σ + 3) ∧
      x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 ∧
      ∀ n : ℤ, σ + 1 ≤ n → x (-n) = -z (n - σ + 1)

/-- **Silent-term formulas on table (33), case $\sigma \equiv 1 \pmod 6$.** Let $\sigma \ge 7$ be
an integer with $\sigma \equiv 1 \pmod 6$, let $c_1 \ne c_2$ be integers, and let
$x : \mathbb{Z} \to \mathbb{Z}$ be a bi-infinite integer sequence with $x_{-3} = x_0 + c_1$,
$x_{-2} = 1$, $x_{-1} = -1$ and, for all integers $4 \le m \le \sigma - 3$, $x_{-m} = -1$ if
$m \equiv 1 \pmod 3$ and $x_{-m} = 1$ otherwise. Write $K_a(x)_b$ for the extended continuant of
order $a$ with start index $b$, and put $z_0 = x_0 + c_2$ and
$w = -K_{\sigma-5}(x)_{-\sigma+3} - z_0 K_{\sigma-4}(x)_{-\sigma+3}$. Then $w \ne 0$ and
$-1 + K_{\sigma-6}(x)_{-\sigma+4} + z_0 K_{\sigma-5}(x)_{-\sigma+4} = w$.

So formula (29) of Theorem 7, with $z_0 = x_0 + c_2$, gives $x_{-\sigma+1} = w \ne 0$ and
$x_{-\sigma+2} = 1$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 1 mod 6`). -/
public theorem_wanted silentTerms_table_one_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 1)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁) (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 1 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) - (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)
        ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        1 * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3))

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
