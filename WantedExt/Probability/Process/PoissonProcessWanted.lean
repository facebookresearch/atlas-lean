/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.PoissonProcess

/-!
# Wanted: exponential interarrivals give a Poisson process

`MathlibExt.Probability.Process.PoissonProcess` proves that the counting process `N` of i.i.d.
rate-`r` exponential interarrival times starts at `0` and is nondecreasing almost surely, and that
each `N t` has the Poisson law of mean `r t`. The remaining part of the classical construction
theorem is that `N` has independent increments and that `N t - N s` has the Poisson law of mean
`r (t - s)`; the proof needs the memorylessness (renewal) argument or the joint density of the
arrival times.

## References

* J. F. C. Kingman, *Poisson Processes*, Oxford University Press (1993), ch. 4.
* S. Karlin, H. M. Taylor, *A First Course in Stochastic Processes*, 2nd ed., Academic Press
  (1975), ch. 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.PoissonProcess
open scoped NNReal

namespace MathlibExt.Probability.PoissonProcessWanted

/-- The counting process of i.i.d. rate-`r` exponential interarrivals is a Poisson process of
rate `r`: its increments over consecutive intervals are independent and `N t - N s` has the
Poisson law of mean `r (t - s)` (Kingman 1993, ch. 4; Karlin–Taylor 1975, ch. 4). -/
public theorem_wanted isPoissonProcess_count {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) :
    IsPoissonProcess (count T) r P

end MathlibExt.Probability.PoissonProcessWanted
