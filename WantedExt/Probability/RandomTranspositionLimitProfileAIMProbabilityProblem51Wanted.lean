/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The cutoff profile of random transpositions (AimPL Markov chain mixing times, Problem 5.3)

AimPL, Markov chain mixing times, Problem 5.3 (N. Berestycki): can we obtain the cutoff profile for
the uniform random transposition walk on `S_n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import WantedExt.Probability.SymmetricGroupRandomWalkShared

@[expose] public section

namespace MathlibExt.Probability.RandomTranspositionLimitProfileAIMProbabilityProblem51Wanted

/-!
Source: AimPL: Markov chain mixing times, Problem 5.3 (N. Berestycki),
http://aimpl.org/markovmixing/5/. UnsolvedMath record UM-20002609 (`AIM-PROBABILITY-0051`), dataset
ulamai/UnsolvedMath v1.8.0.

The walk is Diaconis and Shahshahani's random transposition shuffle as in Teyssier's paper: the
transposition `(i j)` of a uniform pair `(i, j) ∈ [n]²`, so the identity has probability `1/n` and
each transposition `2/n²`. The distance is measured from the identity, as Teyssier's `d_TV(P_n^{*t},
U_n)`. The total variation distance between two Poisson laws is `(1/2) ∑_k |P(Poiss(a) = k) -
P(Poiss(b) = k)|`, with Mathlib's `poissonMeasure`.
-/

open Filter Topology ProbabilityTheory MathlibExt.Probability.SymmetricGroupRandomWalkShared

/-- The step law of the random transposition shuffle on `n` cards: the transposition `(i j)` of a
uniform pair `(i, j) ∈ Fin n × Fin n`, so the identity has probability `1/n` and each
transposition probability `2/n²` (Diaconis-Shahshahani). -/
noncomputable def randomTranspositionStep (n : ℕ) : Equiv.Perm (Fin n) → ℝ :=
  pairStepLaw fun ij => Equiv.swap ij.1 ij.2

/-- The total variation distance `(1/2) ∑_k |P(Poiss(a) = k) - P(Poiss(b) = k)|` between two
Poisson laws. -/
noncomputable def poissonTVDist (a b : NNReal) : ℝ :=
  (1 / 2) * ∑' k : ℕ, |(poissonMeasure a).real {k} - (poissonMeasure b).real {k}|

/-- AimPL Markov chain mixing times, Problem 5.3, answered as a claim: the cutoff profile of the
random transposition shuffle is `c ↦ d_TV(Poiss(1 + e^{-2c}), Poiss(1))`, i.e. for every real
`c` the distance to uniformity at time `⌊(1/2) n log n + c n⌋` tends to it as `n → ∞`. -/
def randomTranspositionLimitProfile : Prop :=
  ∀ c : ℝ, Tendsto (fun n : ℕ => walkDistToUniform (randomTranspositionStep n)
      ⌊1 / 2 * n * Real.log n + c * n⌋₊) atTop
    (𝓝 (poissonTVDist (Real.toNNReal (1 + Real.exp (-2 * c))) 1))

/--
Resolved true: Teyssier proved that at time `⌊(1/2) n log n + c n⌋` the random transposition walk is
at total variation distance `d_TV(Poiss(1 + e^{-2c}), Poiss(1)) + o(1)` from uniform, for every real
`c`. Source: AimPL: Markov chain mixing times, Problem 5.3 (N. Berestycki),
http://aimpl.org/markovmixing/5/; resolution: L. Teyssier, Limit profile for random transpositions,
Ann. Probab. 48 (2020), no. 5, 2323-2343, arXiv:1905.08514, Theorem 1.1: for P_n(Id) = 1/n, P_n(τ) =
2/n² for transpositions and every c ∈ ℝ, d_TV(P_n^{*⌊(1/2) n log n + c n⌋}, U_n) → d_TV(Poiss(1 +
e^{-2c}), Poiss(1)); the introduction states that this answers Berestycki's question at the 2016 AIM
workshop (aimpl.org/markovmixing/5), https://doi.org/10.1214/20-AOP1424.
-/
public theorem_wanted randomTranspositionLimitProfile_holds : randomTranspositionLimitProfile

end MathlibExt.Probability.RandomTranspositionLimitProfileAIMProbabilityProblem51Wanted
