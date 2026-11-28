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

/-- **Dusart's shifted-logarithm upper bound for $\pi(x)$.** Let $\pi(x)$ be the number of primes
$p \le x$ and let $\log$ be the natural logarithm. For every real number $x > e^{1.112}$,
$\pi(x) \le \frac{x}{\log x - 1.112}$.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Corollary 5.3(b). -/
theorem_wanted dusart_pi_upper_shifted_log (x : ℝ) (hx : x > Real.exp 1.112) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (Real.log x - 1.112)

end

end MetaMathlibExt
