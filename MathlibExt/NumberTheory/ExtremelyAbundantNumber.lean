/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Extremely abundant number.** Let $\sigma(n)$ denote the sum of the positive divisors of $n$.
A natural number $n$ is extremely abundant if either $n = 10080$, or $n > 10080$ and
$\sigma(n) / (n \log \log n) > \sigma(m) / (m \log \log m)$ for every natural number $m$ with
$10080 \le m < n$, where $\log$ is the natural logarithm.

Source: concept `jis_term_5535518aa70e4c378d88a78e`, source
`jis_source_6854eacdc72e1e5a005b0055`, lines 200-219. -/
public def IsExtremelyAbundantNumber (n : Nat) : Prop :=
  n = 10080 ∨
    (10080 < n ∧
      ∀ m : Nat, 10080 ≤ m → m < n →
        ((ArithmeticFunction.sigma 1 n : Nat) : Real) /
            ((n : Real) * Real.log (Real.log (n : Real))) >
          ((ArithmeticFunction.sigma 1 m : Nat) : Real) /
            ((m : Real) * Real.log (Real.log (m : Real))))

end

end MetaMathlibExt
