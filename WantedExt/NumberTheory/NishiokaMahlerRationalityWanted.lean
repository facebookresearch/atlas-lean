/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.KMahlerFunction

/-!
Nishioka's rationality-transcendence dichotomy for Mahler functions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nishioka's theorem: algebraic Mahler functions are rational.** Let $k$ be a natural number
and let $F \in \mathbb{C}[[z]]$ be a $k$-Mahler function. If $F$ is algebraic over
$\mathbb{C}[z]$, that is, $P(F) = 0$ for some nonzero polynomial $P$ with coefficients in
$\mathbb{C}[z]$, then $F$ is rational: there are polynomials $p, q \in \mathbb{C}[z]$ with $q \ne 0$
and $qF = p$ in $\mathbb{C}[[z]]$.

Source: Jason P. Bell, Michael Coons, and Eric Rowland, "The
Rational-Transcendental Dichotomy of Mahler Functions", Journal of Integer
Sequences 16 (2013), Article 13.2.10, Nishioka corollary lines 238–241,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Bell/bell2.tex>.
The corollary is attributed to Ku. Nishioka, "Mahler Functions and
Transcendence", Lecture Notes in Mathematics 1294, Theorem 5.1.7. -/
theorem_wanted nishioka_algebraic_kMahler_is_rational
    (k : ℕ) (F : PowerSeries ℂ)
    (hMahler : IsKMahlerFunction k F)
    (hAlgebraic : ∃ P : Polynomial (Polynomial ℂ), P ≠ 0 ∧
      Polynomial.eval₂ (algebraMap (Polynomial ℂ) (PowerSeries ℂ)) F P = 0) :
    ∃ p q : Polynomial ℂ, q ≠ 0 ∧
      Polynomial.toPowerSeries q * F = Polynomial.toPowerSeries p

end

end MetaMathlibExt
