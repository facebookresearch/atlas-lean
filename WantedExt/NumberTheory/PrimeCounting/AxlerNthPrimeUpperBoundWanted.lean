/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Nth

namespace MetaMathlibExt

@[expose] public section

/-- **Axler's upper bound for the $n$th prime.** For every integer $n \ge 46254381$, the $n$th
prime $p_n$ (so that $p_1 = 2$) satisfies
$p_n < n \left(\log n + \log\log n - 1 + \frac{\log\log n - 2}{\log n} -
\frac{(\log\log n)^2 - 6 \log\log n + 10.667}{2 \log^2 n}\right)$.

Source: Christian Axler, "New Estimates for the nth Prime Number,"
Journal of Integer Sequences 22 (2019), Article 19.4.2, Theorem `thm101`,
equation (1.12), lines 160–166 of
https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex.
Context at lines 148–158 distinguishes this refinement from the weaker
earlier Dusart bound. -/
theorem_wanted axler_nth_prime_upper_bound (n : ℕ) (hn : 46254381 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) <
      (n : ℝ) * (Real.log (n : ℝ) + Real.log (Real.log (n : ℝ)) - 1 +
        (Real.log (Real.log (n : ℝ)) - 2) / Real.log (n : ℝ) -
        ((Real.log (Real.log (n : ℝ))) ^ 2 - 6 * Real.log (Real.log (n : ℝ)) +
          10.667) / (2 * (Real.log (n : ℝ)) ^ 2))

end

end MetaMathlibExt
