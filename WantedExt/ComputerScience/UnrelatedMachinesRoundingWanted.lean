/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! # The Lenstra–Shmoys–Tardos rounding theorem

Scheduling on unrelated parallel machines: job `j` takes time `p i j` on machine `i`, and a
schedule assigns every job to one machine. Lenstra, Shmoys and Tardos relax the decision
problem "is there a schedule in which machine `i` finishes by `d i` and every job is run on a
machine where it takes at most `t`?" to a linear program over fractional assignments `x i j`.
Their rounding theorem says that a feasible fractional solution can be rounded to an integral
schedule that overshoots every deadline by at most `t`; in the proof, a vertex of the LP has
a pseudoforest as support, which can be rounded by a matching. With `d i = t = T` this gives
the classical `2`-approximation for minimising the makespan (their Theorem 2).

This file records the existence statement of the rounding theorem; the polynomial-time
rounding and the approximation algorithm are not stated.

## References

* J. K. Lenstra, D. B. Shmoys and É. Tardos, "Approximation algorithms for scheduling
  unrelated parallel machines", Math. Programming 46 (1990), 259–271, Theorems 1 and 2.
* D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge
  University Press, 2011, §11.1.
-/

namespace MathlibExt.ComputerScience.UnrelatedMachinesRoundingWanted

open Finset

/-- **Lenstra–Shmoys–Tardos rounding theorem.** Let `p i j ∈ ℕ` be the processing time of job
`j` on machine `i`, and let `d i ∈ ℕ` (deadlines) and `t ∈ ℕ`. Suppose a fractional assignment
`x ≥ 0` uses only pairs with `p i j ≤ t`, assigns every job in total once
(`∑ᵢ x i j = 1`), and keeps every machine within its deadline (`∑ⱼ p i j x i j ≤ d i`). Then
there is an assignment `σ` of jobs to machines that uses only pairs with `p (σ j) j ≤ t` and
in which every machine `i` has load at most `d i + t`.

Source: J. K. Lenstra, D. B. Shmoys and É. Tardos, "Approximation algorithms for scheduling
unrelated parallel machines", Math. Programming 46 (1990), 259–271, Theorem 1 (rounding
theorem; there, any vertex of the LP can be so rounded, in polynomial time). -/
theorem_wanted exists_assignment_load_le {M J : Type*} [Fintype M] [Fintype J] [DecidableEq M]
    (p : M → J → ℕ) (d : M → ℕ) (t : ℕ) (x : M → J → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    (hsupp : ∀ i j, t < p i j → x i j = 0) (hjob : ∀ j, ∑ i, x i j = 1)
    (hload : ∀ i, ∑ j, (p i j : ℝ) * x i j ≤ d i) :
    ∃ σ : J → M, (∀ j, p (σ j) j ≤ t) ∧ ∀ i, ∑ j with σ j = i, p i j ≤ d i + t

end MathlibExt.ComputerScience.UnrelatedMachinesRoundingWanted
