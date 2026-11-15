/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Card

/-!
# Marking paging algorithm

State is a cache with a marked subset. Hits mark the page;
a fault clears all marks when every cached page is marked
(a new phase), then inserts and marks the page, evicting an
unmarked page when full. The `2H_k` competitiveness
accounting is not included here.
-/

@[expose] public section

/-- Marking paging algorithm, pair-state form (core of
ALG-25a). State: `(cache, marked)`. On a hit, mark the page.
On a fault: if every cached page is marked, clear all marks
(new phase); then insert the page (evicting
`evict cache marked`, required to be an unmarked cached page,
when the cache is full), and mark it. -/
def markStep (k : ℕ) (evict : Finset ℕ → Finset ℕ → ℕ)
    (s : Finset ℕ × Finset ℕ) (p : ℕ) : Finset ℕ × Finset ℕ :=
  if p ∈ s.1 then
    (s.1, insert p s.2)
  else
    let base : Finset ℕ × Finset ℕ :=
      if s.2 = s.1 then (s.1, ∅) else s
    if base.1.card < k then
      (insert p base.1, insert p base.2)
    else
      (insert p (base.1.erase (evict base.1 base.2)), insert p base.2)

/-- On a hit, the marked set grows by exactly the page. -/
theorem markStep_hit {k : ℕ} (evict : Finset ℕ → Finset ℕ → ℕ)
    (s : Finset ℕ × Finset ℕ) (p : ℕ) (hp : p ∈ s.1) :
    (markStep k evict s p).2 = insert p s.2 := by
  simp [markStep, hp]

/-- On a fault starting a new phase (all cached pages
marked), the marked set afterwards is exactly `{p}`. -/
theorem markStep_fault_new_phase {k : ℕ}
    (evict : Finset ℕ → Finset ℕ → ℕ)
    (s : Finset ℕ × Finset ℕ) (p : ℕ)
    (hp : p ∉ s.1) (hphase : s.2 = s.1) :
    (markStep k evict s p).2 = {p} := by
  simp [markStep, hp, hphase]
  split_ifs <;> rfl

/-- On any fault, the page is cached and marked afterwards. -/
theorem markStep_fault_mem {k : ℕ}
    (evict : Finset ℕ → Finset ℕ → ℕ)
    (s : Finset ℕ × Finset ℕ) (p : ℕ) (hp : p ∉ s.1) :
    p ∈ (markStep k evict s p).1 ∧ p ∈ (markStep k evict s p).2 := by
  simp [markStep, hp]
  split_ifs <;> simp

/-- Within a phase (no reset), marked only grows, so a page
that faults once cannot fault again until a reset: if `p`
faulted into state `s'` (so `p ∈ s'.marked`) and `p` is
requested again while the marked set has only grown and `p`
was never evicted, it is a hit. Stated as: marked monotone
along hit steps. -/
theorem markStep_marked_mono_hit {k : ℕ}
    (evict : Finset ℕ → Finset ℕ → ℕ)
    (s : Finset ℕ × Finset ℕ) (p : ℕ) (hp : p ∈ s.1) :
    s.2 ⊆ (markStep k evict s p).2 := by
  simp [markStep, hp]

end
