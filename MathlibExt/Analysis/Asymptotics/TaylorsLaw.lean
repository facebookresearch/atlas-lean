/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Asymptotics.TaylorInitialMean
public import MathlibExt.Analysis.Asymptotics.TaylorInitialSampleVariance
public import MathlibExt.Analysis.Asymptotics.TaylorAdmissibleSequence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Taylor's law, asymptotic form.** A sequence $a : \mathbb{N} \to \mathbb{N}$, indexed from
$1$ (its value at $0$ is ignored), satisfies Taylor's law asymptotically when it is admissible
for Taylor's law and, writing $m(a, n)$ and $v(a, n)$ for its initial-segment mean and
initial-segment sample variance, there are real numbers $c > 0$ and $b$ such that
$v(a, n) / m(a, n)^b \to c$ as $n \to \infty$.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>:
the collection `𝒜` of admissible sequences with the mean `eq:mean` and
variance `eq:varexpanded` definitions (lines 113–125), and the asymptotic
power-law definition `eq:TLpower` (lines 152–156). -/
def SatisfiesTaylorsLawAsymptotically (a : ℕ → ℕ) : Prop :=
  IsTaylorAdmissibleSequence a ∧ ∃ c b : ℝ, 0 < c ∧
    Filter.Tendsto
      (fun n : ℕ => initialSegmentSampleVariance a n /
        Real.rpow (initialSegmentMean a n) b)
      Filter.atTop (nhds c)

end

end MetaMathlibExt
