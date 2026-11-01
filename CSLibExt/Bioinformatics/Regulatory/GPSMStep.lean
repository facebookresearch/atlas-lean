/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
import Mathlib.Algebra.BigOperators.Field

/-!
# The GPS M-step with a negative Dirichlet prior and component elimination

GPS (Guo et al. 2010) models ChIP-Seq reads as a mixture over candidate binding events `j`
with mixing probabilities `π`, and places the sparse *negative Dirichlet* prior
`p(π) ∝ ∏ j, π j ^ (-α)` on `π` (following Figueiredo and Jain 2002). With `N j` the expected
number of reads assigned to event `j` in the E-step, the M-step maximizes the expected complete-data
log penalized likelihood `∑ j, (N j - α) log (π j)` on the simplex, and events with `N j ≤ α` are
*eliminated* (`π j := 0`, the model is restructured without them). The resulting update is
`π j = max (N j - α) 0 / ∑ k, max (N k - α) 0` (`mStep`), the component-annihilation update of
Figueiredo and Jain (2002) that GPS adopts.

On the whole simplex the penalized objective is not a well-posed maximization when some
`N j < α` (the term `(N j - α) log (π j)` grows without bound as `π j → 0`); this is why GPS
eliminates such events. We therefore prove two exact statements:

* `penalizedQ_le_mStep`: when every event survives (`α < N j` for all `j`), `mStep` maximizes the
  penalized objective over all positive probability vectors (the M-step of the restructured
  model).
* `truncatedQ_le_mStep`: in general, `mStep` maximizes the *truncated* objective
  `∑ j, max (N j - α) 0 * log (π j)` over all positive probability vectors. This
  characterization of the elimination rule is derived here; neither paper states it.

## Main results

* `mStep_eq_zero_iff`, `mStep_pos_iff`: an event is eliminated iff `N j ≤ α`.
* `sum_mStep`: the update is a probability vector when some event survives.
* `mStep_zero`: with `α = 0` the update is the ordinary mixture M-step `N j / ∑ N`.
* `truncatedQ_le_mStep`, `penalizedQ_le_mStep`.

## References

* Y. Guo, G. Papachristoudis, R. C. Altshuler, G. K. Gerber, T. S. Jaakkola, D. K. Gifford,
  S. Mahony, *Discovering homotypic binding events at high spatial resolution*,
  Bioinformatics 26 (2010), 3028–3034, Sections 2.2–2.3.
* M. A. T. Figueiredo and A. K. Jain, *Unsupervised learning of finite mixture models*,
  IEEE Trans. Pattern Anal. Mach. Intell. 24 (2002), 381–396.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Regulatory.GPS

open Real Finset
open Cslib.MachineLearning.LatentVariable.BernoulliMixture (sum_mul_log_le_sum_mul_log_div)

variable {ι : Type*}

/-- The surviving weight `max (N j - α) 0` of event `j`, for expected read counts `N` and
sparseness parameter `α`. -/
noncomputable def survivorWeight (α : ℝ) (N : ι → ℝ) (j : ι) : ℝ := max (N j - α) 0

/-- **The GPS M-step with component elimination**:
`π j = max (N j - α) 0 / ∑ k, max (N k - α) 0`. -/
noncomputable def mStep [Fintype ι] (α : ℝ) (N : ι → ℝ) (j : ι) : ℝ :=
  survivorWeight α N j / ∑ k, survivorWeight α N k

/-- The expected complete-data log penalized likelihood of GPS, up to an additive constant:
`∑ j, (N j - α) log (π j)` (the expected log-likelihood `∑ j, N j log (π j)` plus the log of the
negative Dirichlet prior). Meaningful for positive `π`. -/
noncomputable def penalizedQ [Fintype ι] (α : ℝ) (N π : ι → ℝ) : ℝ := ∑ j, (N j - α) * log (π j)

/-- The truncated objective `∑ j, max (N j - α) 0 * log (π j)`. -/
noncomputable def truncatedQ [Fintype ι] (α : ℝ) (N π : ι → ℝ) : ℝ :=
  ∑ j, survivorWeight α N j * log (π j)

/-- Surviving weights are nonnegative. -/
theorem survivorWeight_nonneg (α : ℝ) (N : ι → ℝ) (j : ι) : 0 ≤ survivorWeight α N j :=
  le_max_right _ _

variable [Fintype ι]

/-- The total surviving weight is positive iff some event has `α < N j`. -/
theorem sum_survivorWeight_pos {α : ℝ} {N : ι → ℝ} {j₀ : ι} (h : α < N j₀) :
    0 < ∑ k, survivorWeight α N k :=
  lt_of_lt_of_le (lt_max_of_lt_left (sub_pos.2 h))
    (single_le_sum (fun k _ => survivorWeight_nonneg α N k) (mem_univ j₀))

/-- The update is nonnegative. -/
theorem mStep_nonneg (α : ℝ) (N : ι → ℝ) (j : ι) : 0 ≤ mStep α N j :=
  div_nonneg (survivorWeight_nonneg α N j) (sum_nonneg fun k _ => survivorWeight_nonneg α N k)

/-- The update sums to one when some event survives. -/
theorem sum_mStep {α : ℝ} {N : ι → ℝ} {j₀ : ι} (h : α < N j₀) : ∑ j, mStep α N j = 1 := by
  simp only [mStep]
  rw [← sum_div, div_self (sum_survivorWeight_pos h).ne']

/-- **Elimination**: when some event survives, event `j` gets probability zero iff
`N j ≤ α`. -/
theorem mStep_eq_zero_iff {α : ℝ} {N : ι → ℝ} {j₀ : ι} (h : α < N j₀) (j : ι) :
    mStep α N j = 0 ↔ N j ≤ α := by
  rw [mStep, div_eq_zero_iff, or_iff_left (sum_survivorWeight_pos h).ne', survivorWeight,
    max_eq_right_iff, sub_nonpos]

/-- When some event survives, event `j` keeps positive probability iff `α < N j`. -/
theorem mStep_pos_iff {α : ℝ} {N : ι → ℝ} {j₀ : ι} (h : α < N j₀) (j : ι) :
    0 < mStep α N j ↔ α < N j := by
  rw [lt_iff_le_and_ne, ne_comm, Ne, mStep_eq_zero_iff h, not_le]
  exact ⟨fun h' => h'.2, fun h' => ⟨mStep_nonneg α N j, h'⟩⟩

/-- With `α = 0` and nonnegative counts the update is the ordinary mixture M-step
`N j / ∑ N`. -/
theorem mStep_zero {N : ι → ℝ} (hN : ∀ j, 0 ≤ N j) (j : ι) :
    mStep 0 N j = N j / ∑ k, N k := by
  simp only [mStep, survivorWeight, sub_zero, max_eq_left (hN _)]

/-- **The update maximizes the truncated objective** over the positive probability vectors
(derived characterization of the elimination rule). -/
theorem truncatedQ_le_mStep {α : ℝ} {N : ι → ℝ} {j₀ : ι} (h : α < N j₀) {π : ι → ℝ}
    (hπ : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1) :
    truncatedQ α N π ≤ truncatedQ α N (mStep α N) :=
  sum_mul_log_le_sum_mul_log_div (fun j => survivorWeight_nonneg α N j)
    (sum_survivorWeight_pos h) hπ hsum

/-- When every event survives, the penalized and truncated objectives agree. -/
theorem truncatedQ_eq_penalizedQ {α : ℝ} {N : ι → ℝ} (h : ∀ j, α < N j) (π : ι → ℝ) :
    truncatedQ α N π = penalizedQ α N π := by
  simp only [truncatedQ, penalizedQ, survivorWeight, max_eq_left (sub_pos.2 (h _)).le]

/-- When every event survives, the update is `(N j - α) / ∑ k, (N k - α)`. -/
theorem mStep_of_forall_lt {α : ℝ} {N : ι → ℝ} (h : ∀ j, α < N j) (j : ι) :
    mStep α N j = (N j - α) / ∑ k, (N k - α) := by
  simp only [mStep, survivorWeight, max_eq_left (sub_pos.2 (h _)).le]

/-- **The M-step of the restructured model**: when every remaining event survives
(`α < N j` for all `j`), the update maximizes the GPS expected complete-data log penalized
likelihood over the positive probability vectors. -/
theorem penalizedQ_le_mStep [Nonempty ι] {α : ℝ} {N : ι → ℝ} (h : ∀ j, α < N j) {π : ι → ℝ}
    (hπ : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1) :
    penalizedQ α N π ≤ penalizedQ α N (mStep α N) := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  rw [← truncatedQ_eq_penalizedQ h, ← truncatedQ_eq_penalizedQ h]
  exact truncatedQ_le_mStep (h j₀) hπ hsum

end Cslib.Bioinformatics.Regulatory.GPS
