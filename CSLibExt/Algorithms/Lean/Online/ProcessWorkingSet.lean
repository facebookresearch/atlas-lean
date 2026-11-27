/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Set.Card

/-!
# The working set of a process

A trace gives the pages referenced by one process at each instant of its own execution time.
An ideal working-set policy keeps precisely the pages in `workingSet`, not a fixed number of
pages in order of recency. In particular, a page can expire without another page being touched.

P. J. Denning, “The Working Set Model for Program Behavior”, *Communications of the ACM* 11(5)
(1968), §3, p. 326, Figure 2 and equation (1), defines the window with the open interval
$(t-\tau,t)$ and counts its distinct pages. Here the window is $(t-\tau,t]$: a reference at the
observation instant counts if the width is positive. A reference exactly a window-width old is
excluded at every width.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.Paging

open scoped NNReal

variable {Page : Type*}

/-- The working set of one process at process time $t$ and width $\tau \ge 0$ consists of the
pages it referenced at some instant $s$ in $(t-\tau,t]$. The set `refs s` of pages touched at $s$
may be empty or infinite. Times are nonnegative, but the left endpoint is computed in the reals,
so time zero is included when $t<\tau$. This is the resident set of the ideal working-set policy.
Denning (1968), §3, p. 326, Figure 2, uses the open interval $(t-\tau,t)$ instead. -/
def workingSet (refs : ℝ≥0 → Set Page) (t τ : ℝ≥0) : Set Page :=
  {p | ∃ s : ℝ≥0, (s : ℝ) ∈ Set.Ioc ((t : ℝ) - τ) t ∧ p ∈ refs s}

/-- The working-set size counts distinct pages referenced by one process in $(t-\tau,t]$, for
nonnegative process time $t$ and width $\tau$. Repeated references to a page count once.
The result is an extended natural number: it is the ordinary count for a finite set of such
pages and infinity if infinitely many distinct pages were referenced in the window. -/
noncomputable def workingSetSize (refs : ℝ≥0 → Set Page) (t τ : ℝ≥0) : ℕ∞ :=
  (workingSet refs t τ).encard

/-- A page belongs to the working set at process time $t$ with width $\tau$ exactly when some
reference to that page occurred at a process time $s \le t$ of age $t-s<\tau$. No latest
reference or finiteness assumption is needed. -/
theorem mem_workingSet_iff {refs : ℝ≥0 → Set Page} {t τ : ℝ≥0} {p : Page} :
    p ∈ workingSet refs t τ ↔ ∃ s ≤ t, p ∈ refs s ∧ t - s < τ := by
  constructor
  · rintro ⟨s, ⟨hleft, hright⟩, hp⟩
    refine ⟨s, hright, hp, ?_⟩
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub hright]
    exact sub_lt_comm.mp hleft
  · rintro ⟨s, hst, hp, hage⟩
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub hst] at hage
    exact ⟨s, ⟨sub_lt_comm.mp hage, hst⟩, hp⟩

/-- A zero-width window has no resident pages at any process time, even if the process makes
references at that very instant. -/
@[simp] theorem workingSet_zero (refs : ℝ≥0 → Set Page) (t : ℝ≥0) :
    workingSet refs t 0 = ∅ := by
  ext p
  simp [workingSet]

/-- Suppose $s$ is the greatest process time at or before $t$ when page $p$ was referenced:
there was a reference at $s \le t$ and none to $p$ in $(s,t]$. Then the ideal working-set
policy of width $\tau$ has $p$ resident at $t$ if and only if $t-s<\tau$. In particular the
page is absent at equality, even if the process made no intervening references to other pages. -/
theorem mem_workingSet_iff_of_isGreatest {refs : ℝ≥0 → Set Page} {p : Page} {s t τ : ℝ≥0}
    (hlast : IsGreatest {u | u ≤ t ∧ p ∈ refs u} s) :
    p ∈ workingSet refs t τ ↔ t - s < τ := by
  rw [mem_workingSet_iff]
  constructor
  · rintro ⟨u, hut, hpu, hu⟩
    exact (tsub_le_tsub_left (hlast.2 ⟨hut, hpu⟩) t).trans_lt hu
  · exact fun h => ⟨s, hlast.1.1, hlast.1.2, h⟩

end Cslib.Algorithms.Lean.Online.Paging
