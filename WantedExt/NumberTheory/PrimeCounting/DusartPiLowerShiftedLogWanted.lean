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

/-- **Dusart's shifted-logarithm lower bound for $\pi(x)$.** Let $\pi(x)$ be the number of primes
$p \le x$ and let $\log$ be the natural logarithm. For every real number $x \ge 5393$,
$\pi(x) \ge \frac{x}{\log x - 1}$.

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Corollary 5.3(a). -/
theorem_wanted dusart_pi_lower_shifted_log (x : ℝ) (hx : 5393 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≥ x / (Real.log x - 1)

end

end MetaMathlibExt
