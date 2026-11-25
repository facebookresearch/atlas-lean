/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

namespace MetaMathlibExt

/--
**Explicit bounds for the summatory function of $\mu(n)/n$.** Let $\mu$ be the Möbius function.
For every real $x \ge 33$,
$$\Bigl| \sum_{1 \le n \le x} \frac{\mu(n)}{n} \Bigr| < \frac{0.19}{\log x},$$
and for every real $x > 1$,
$$\Bigl| \sum_{1 \le n \le x} \frac{\mu(n)}{n} \Bigr| < \frac{546}{(\log x)^2}.$$

These bounds improve the estimates $0.2185/\log x$ and $726/(\log x)^2$ of the source's
equation (e4).

Source: Olivier Bordellès,
"Some Explicit Estimates for the Möbius Function,"
Journal of Integer Sequences 18 (2015), Article 15.11.1,
Theorem (label t1), items (a) and (b), lines 118–127,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Bordelles2/bordelles21.tex
-/
public theorem_wanted summatory_moebius_div_bound :
    (∀ x : ℝ, 33 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| <
        (0.19 : ℝ) / Real.log x) ∧
    (∀ x : ℝ, 1 < x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| <
        546 / (Real.log x) ^ 2)

end MetaMathlibExt
