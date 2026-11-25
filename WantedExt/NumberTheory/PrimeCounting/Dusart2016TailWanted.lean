/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-!
## Dusart 2016 tail theorem (conditional on a formal zero-free region)

With `R = 5.69693`, `X = √((log x)/R)` and `ε(x) = √(8/π)·X^{1/2}·e^{-X}`,
`max(|ϑ(x)-x|, |ψ(x)-x|) < x·ε(x)` for `X ≥ max(8.36, 8/R)`
(i.e. `x ≥ exp(R·max(8.36, 8/R)²)`), assuming the zero-free
region `Re s ≥ 1 - 1/(R log|Im s|)` for `|Im s| ≥ 2π`. There is no
`H` side condition and no correction factor. At `x = e^5000`
this yields the two ladder tails (`η_3 < 0.15`, `η_2 < 3e-5`).

Source: Pierre Dusart, *Estimates of ψ, θ for large values of x
without the Riemann hypothesis*, Math. Comp. 85 (2016), no. 298,
875–888, Theorem 1.1, DOI 10.1090/mcom/3005. The printed side
condition `max(8.36, 8R)` is a dropped slash for `max(8.36, 8/R)`,
as the proof (p. 884) and Lemma 3.4 both state.
-/

/-- **Dusart's bound for $\vartheta$ and $\psi$ from a zero-free region.** Let $R = 5.69693$, let
$\log$ be the natural logarithm, and let $\vartheta(x) = \sum_{p \le x} \log p$ (over primes $p$)
and $\psi(x) = \sum_{n \le x} \Lambda(n)$, with $\Lambda$ the von Mangoldt function, be
Chebyshev's functions. Suppose the Riemann zeta function has no zero $s$ with
$|\operatorname{Im} s| \ge 2\pi$ and
$\operatorname{Re} s \ge 1 - \frac{1}{R \log |\operatorname{Im} s|}$. Then for every real
number $x \ge \exp\bigl(R \max(8.36, 8/R)^2\bigr)$, writing $X = \sqrt{(\log x)/R}$,
$$\max\bigl(|\vartheta(x) - x|, |\psi(x) - x|\bigr) < x \sqrt{8/\pi}\, X^{1/2} e^{-X}.$$

Source: Pierre Dusart, *Estimates of ψ, θ for large values of x without the Riemann
hypothesis*, Math. Comp. 85 (2016), 875–888, Theorem 1.1. -/
public theorem_wanted dusart2016_tail_theorem
    (hzfr : ∀ s : ℂ, 2 * Real.pi ≤ |s.im| →
      1 - 1 / (5.69693 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : Real.exp (5.69693 * (max 8.36 (8 / 5.69693)) ^ 2) ≤ x) :
    max |Chebyshev.theta x - x| |Chebyshev.psi x - x|
      < x * Real.sqrt (8 / Real.pi)
        * Real.sqrt (Real.sqrt (Real.log x / 5.69693))
        * Real.exp (-(Real.sqrt (Real.log x / 5.69693)))

end MetaMathlibExt
