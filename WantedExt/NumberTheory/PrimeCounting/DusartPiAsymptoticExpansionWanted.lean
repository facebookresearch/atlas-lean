/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

namespace MetaMathlibExt

@[expose] public section

/-- **Dusart's asymptotic expansion of $\pi(x)$ with explicit error.** Let $\pi(x)$ be the number
of primes $p \le x$ and $\log$ the natural logarithm. For every real number $x \ge 4 \cdot 10^9$
there is a real number $E$ with $|E| \le \frac{7.32}{(\log x)^3}$ such that
$$\pi(x) = \frac{x}{\log x} \Bigl(1 + \frac{1}{\log x} + \frac{2}{(\log x)^2} + E\Bigr).$$

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.1. -/
theorem_wanted dusart_pi_asymptotic_expansion (x : ℝ) (hx : 4e9 ≤ x) :
    ∃ E, ((Nat.primeCounting ⌊x⌋₊ : ℝ)
      = x / Real.log x * (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E)
      ∧ |E| ≤ 7.32 / (Real.log x) ^ 3)

end

end MetaMathlibExt
