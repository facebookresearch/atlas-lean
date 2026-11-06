/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

namespace MetaMathlibExt

/-- **Robin's criterion for the Riemann hypothesis.** The Riemann hypothesis holds if and only if
$\sigma(n) < e^{\gamma}\, n \log\log n$ for every natural number $n > 5040$, where $\sigma(n)$ is
the sum of the positive divisors of $n$, $\gamma$ is the Euler–Mascheroni constant, and
$\log$ is the natural logarithm.

Source: Sadegh Nazardonyavi and Semyon Yakubovich, "Extremely Abundant
Numbers and the Riemann Hypothesis", Journal of Integer Sequences 17
(2014), Article 14.2.8, abstract, lines 77–80, attributed there to Robin,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex>. -/
theorem_wanted robin_criterion_for_riemann_hypothesis :
    RiemannHypothesis ↔
      ∀ n : ℕ, 5040 < n →
        (ArithmeticFunction.sigma 1 n : ℝ) <
          Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

end MetaMathlibExt
