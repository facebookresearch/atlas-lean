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
public import MathlibExt.NumberTheory.ExtendedContinuantConjugateContinuedFractionNotPurelyPeriodic
public import MathlibExt.NumberTheory.ExtendedContinuantOneSilentTerms

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
`MathlibExt.NumberTheory.ExtendedContinuantOddSilentTerms`, and to
`MetaMathlibExt.oneSilent_terms`, which is proved in
`MathlibExt.NumberTheory.ExtendedContinuantOneSilentTerms`.
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

end

end MetaMathlibExt
