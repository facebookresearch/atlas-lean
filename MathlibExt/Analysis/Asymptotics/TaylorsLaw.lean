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

/-- Taylor's variance-to-mean power law, asymptotic form, for integer sequences.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>:
the collection `𝒜` of admissible sequences with the mean `eq:mean` and
variance `eq:varexpanded` definitions (lines 113–125), and the asymptotic
power-law definition `eq:TLpower` (lines 152–156).

The sequence is indexed from `1` (the value at `0` is ignored). Admissibility
uses the canonical `IsTaylorAdmissibleSequence` predicate. Mean and variance reuse the canonical
`initialSegmentMean` / `initialSegmentSampleVariance` APIs. The law holds iff
`variance(a, n) / mean(a, n) ^ b` tends to a constant `c > 0` as `n → ∞`,
with `b` any finite real. -/
def SatisfiesTaylorsLawAsymptotically (a : ℕ → ℕ) : Prop :=
  IsTaylorAdmissibleSequence a ∧ ∃ c b : ℝ, 0 < c ∧
    Filter.Tendsto
      (fun n : ℕ => initialSegmentSampleVariance a n /
        Real.rpow (initialSegmentMean a n) b)
      Filter.atTop (nhds c)

end

end MetaMathlibExt
