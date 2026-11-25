/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.Sampling.SimulatedAnnealing

/-!
# Hajek's simulated-annealing characterization: wanted

Hajek's theorem characterizes when finite-state simulated annealing with a
logarithmic cooling schedule converges in probability to the global minima.
Source: Bruce Hajek, "Optimization by simulated annealing: a necessary and
sufficient condition for convergence", in *Adaptive Statistical Procedures
and Related Topics*, IMS Lecture Notes--Monograph Series, vol. 8 (1986),
pp. 417--427, DOI `10.1214/lnms/1215540316`; see the abstract on p. 417, the
standing assumptions on p. 419, and the Remarks on p. 423. This is not the
later journal version, "Cooling schedules for optimal annealing",
Mathematics of Operations Research 13(2) (1988), pp. 311--329.
The annealing law, Gibbs facts, depth apparatus and schedule properties used
in the statement are in
`CSLibExt.MachineLearning.Sampling.SimulatedAnnealing`; the
time-inhomogeneous convergence characterization itself is deferred here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling.SimulatedAnnealing

open Filter Topology

/-- **Hajek's theorem** (IMS Lecture Notes--Monograph Series, vol. 8 (1986),
pp. 417, 419, 423): for a strongly irreducible, weakly reversible finite
landscape, simulated annealing from `x₀` under the logarithmic schedule
`T k = c / log (k + 1)` converges in probability to the global minima iff
`dStar R V ≤ c`, for `0 < c`. -/
theorem_wanted hajek_iff {S : Type*} [Fintype S] [DecidableEq S]
    (R : S → PMF S) (V : S → ℝ)
    (hSI : StronglyIrreducible R V) (hWR : WeaklyReversible R V)
    {c : ℝ} (hc : 0 < c) (x₀ : S) :
    Tendsto (fun k => (annealLaw R V (fun k : ℕ => c / Real.log ((k : ℝ) + 1)) x₀ k).toOuterMeasure
        (globalMinSet V)) atTop (𝓝 1) ↔ (dStar R V).toReal ≤ c

end Cslib.MachineLearning.Sampling.SimulatedAnnealing
