/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.PoissonPointProcess

/-!
# Wanted: the restriction theorem for Poisson point processes

The process-level restriction theorem for the finite-intensity Poisson point process of
`MathlibExt.Probability.Process.PoissonPointProcess`: the restrictions of the process to pairwise
disjoint measurable sets are independent Poisson point processes with the restricted
intensities. The proved file contains the count-level consequence `map_apply_pi`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press (2017), Thm. 5.2.
-/

@[expose] public section

open Function MeasureTheory

namespace MathlibExt.Probability.PoissonPointProcess

/-- **Restriction theorem.** The restrictions `η|_{A i}` of a Poisson point process with finite
intensity `μ` to pairwise disjoint measurable sets `A i` are independent Poisson point processes
with intensities `μ|_{A i}` (Last–Penrose Thm. 5.2). -/
theorem_wanted map_restrict_pi {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) :
    (poissonPointProcess μ).map (fun η i => η.restrict (A i)) =
      Measure.pi fun i => poissonPointProcess (μ.restrict (A i))

end MathlibExt.Probability.PoissonPointProcess
