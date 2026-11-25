/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: Muse Code powered by Meta Muse Spark
-/
module

public import MathlibExt.Analysis.Complex.Subharmonic.AngularSublevel
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Finite radial slits in the unit disk

`RadialSlitData n` is a family of `n` closed real intervals with
`0 ≤ inner(i) ≤ outer(i) ≤ 1`. The radius set is their union, the complex
slit is that union on the real axis, and the slit domain is the open unit
disk with the slit removed. Overlapping and degenerate intervals are allowed.
When `n=0` the union is empty and the domain is the full unit disk.

The radius and slit sets are compact and closed, the radius set lies in
`[0,1]`, and the slit lies in the closed unit disk. The remaining domain is
open and nonempty: the negative real point `-1/2` avoids every possible slit.
The distinguished one-interval family gives exactly the entire slit `[0,1]`
on the real axis.
-/

@[expose] public section

namespace Complex

/-- A finite family of closed intervals with endpoints satisfying `0 ≤ inner(i) ≤ outer(i) ≤ 1`;
overlaps, zero-length intervals and an empty family are permitted. -/
structure RadialSlitData (n : ℕ) where
  inner : Fin n → ℝ
  outer : Fin n → ℝ
  inner_nonneg : ∀ i, 0 ≤ inner i
  inner_le_outer : ∀ i, inner i ≤ outer i
  outer_le_one : ∀ i, outer i ≤ 1

namespace RadialSlitData

variable {n : ℕ} (E : RadialSlitData n)

/-- The union of the closed radius intervals in `[0,1]`.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed. -/
def radiusSet : Set ℝ :=
  ⋃ i, Set.Icc (E.inner i) (E.outer i)

/-- The radius union embedded on the real axis in the complex plane.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed. -/
def slitSet : Set ℂ :=
  E.radiusSet ×ℂ ({0} : Set ℝ)

/-- The open unit disk after removing the closed real-axis slit.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed. -/
noncomputable def slitDomain : Set ℂ :=
  Metric.ball 0 1 \ E.slitSet

/-- Radius-set membership means membership in at least one of the finite closed intervals.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_radiusSet {r : ℝ} :
    r ∈ E.radiusSet ↔ ∃ i, r ∈ Set.Icc (E.inner i) (E.outer i)
``` -/
theorem mem_radiusSet {r : ℝ} :
    r ∈ E.radiusSet ↔ ∃ i, r ∈ Set.Icc (E.inner i) (E.outer i) := by
  unfold radiusSet
  exact Set.mem_iUnion

/-- A complex point lies on the slit exactly when its imaginary part is zero and its real part
belongs to the radius union.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_slitSet {z : ℂ} :
    z ∈ E.slitSet ↔ z.re ∈ E.radiusSet ∧ z.im = 0
``` -/
theorem mem_slitSet {z : ℂ} :
    z ∈ E.slitSet ↔ z.re ∈ E.radiusSet ∧ z.im = 0 := by
  unfold slitSet
  rw [Complex.mem_reProdIm]
  simp only [Set.mem_singleton_iff]

/-- A real-axis point lies on the slit exactly when its real coordinate belongs to the radius set.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem ofReal_mem_slitSet {r : ℝ} :
    (r : ℂ) ∈ E.slitSet ↔ r ∈ E.radiusSet
``` -/
theorem ofReal_mem_slitSet {r : ℝ} :
    (r : ℂ) ∈ E.slitSet ↔ r ∈ E.radiusSet := by
  rw [mem_slitSet]
  simp

/-- The slit-domain points have norm below one and do not lie on the slit.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem mem_slitDomain {z : ℂ} :
    z ∈ E.slitDomain ↔ ‖z‖ < 1 ∧ z ∉ E.slitSet
``` -/
theorem mem_slitDomain {z : ℂ} :
    z ∈ E.slitDomain ↔ ‖z‖ < 1 ∧ z ∉ E.slitSet := by
  simp only [slitDomain, Set.mem_sdiff, Metric.mem_ball, dist_zero_right]

/-- The finite union of closed bounded radius intervals is compact.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem isCompact_radiusSet : IsCompact E.radiusSet
``` -/
theorem isCompact_radiusSet : IsCompact E.radiusSet := by
  unfold radiusSet
  exact isCompact_iUnion fun _ => isCompact_Icc

/-- The finite radius union is closed.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem isClosed_radiusSet : IsClosed E.radiusSet
``` -/
theorem isClosed_radiusSet : IsClosed E.radiusSet :=
  E.isCompact_radiusSet.isClosed

/-- Every selected radius lies in the closed interval `[0,1]`.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem radiusSet_subset_Icc : E.radiusSet ⊆ Set.Icc 0 1
``` -/
theorem radiusSet_subset_Icc : E.radiusSet ⊆ Set.Icc 0 1 := by
  intro r hr
  rw [E.mem_radiusSet] at hr
  obtain ⟨i, hi⟩ := hr
  rw [Set.mem_Icc] at hi
  exact ⟨le_trans (E.inner_nonneg i) hi.1, le_trans hi.2 (E.outer_le_one i)⟩

/-- The finite real-axis slit is compact in the complex plane.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem isCompact_slitSet : IsCompact E.slitSet
``` -/
theorem isCompact_slitSet : IsCompact E.slitSet :=
  E.isCompact_radiusSet.reProdIm isCompact_singleton

/-- The finite real-axis slit is closed in the complex plane.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem isClosed_slitSet : IsClosed E.slitSet
``` -/
theorem isClosed_slitSet : IsClosed E.slitSet :=
  E.isCompact_slitSet.isClosed

/-- The slit lies in the closed unit disk.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitSet_subset_closedBall : E.slitSet ⊆ Metric.closedBall 0 1
``` -/
theorem slitSet_subset_closedBall : E.slitSet ⊆ Metric.closedBall 0 1 := by
  intro z hz
  rw [E.mem_slitSet] at hz
  have hmem := E.radiusSet_subset_Icc hz.1
  rw [Set.mem_Icc] at hmem
  have hrw : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl hz.2
  rw [Metric.mem_closedBall, dist_zero_right, hrw, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hmem.1]
  exact hmem.2

/-- Removing the closed slit from the open unit disk gives an open domain.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem isOpen_slitDomain : IsOpen E.slitDomain
``` -/
theorem isOpen_slitDomain : IsOpen E.slitDomain :=
  Metric.isOpen_ball.sdiff E.isClosed_slitSet

/-- The slit domain lies in the open unit disk.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitDomain_subset_ball : E.slitDomain ⊆ Metric.ball 0 1
``` -/
theorem slitDomain_subset_ball : E.slitDomain ⊆ Metric.ball 0 1 :=
  Set.sdiff_subset

/-- The negative real point `-1/2` belongs to the slit domain, so it is nonempty for every finite
slit family.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitDomain_nonempty : E.slitDomain.Nonempty
``` -/
theorem slitDomain_nonempty : E.slitDomain.Nonempty := by
  have heq : (-1/2 : ℂ) = ((-1/2 : ℝ) : ℂ) := by push_cast; ring
  refine ⟨-1/2, ?_⟩
  rw [E.mem_slitDomain]
  refine ⟨?_, ?_⟩
  · rw [heq, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  · intro h
    rw [E.mem_slitSet] at h
    have hsub := E.radiusSet_subset_Icc h.1
    rw [Set.mem_Icc, heq, Complex.ofReal_re] at hsub
    norm_num at hsub

/-- The one-interval slit family with inner endpoint zero and outer endpoint one. -/
def unitInterval : RadialSlitData 1 where
  inner := fun _ => 0
  outer := fun _ => 1
  inner_nonneg := fun _ => le_refl 0
  inner_le_outer := fun _ => zero_le_one
  outer_le_one := fun _ => le_refl 1

/-- The distinguished one-interval radius set is exactly `[0,1]`.

```lean
theorem unitInterval_radiusSet :
    unitInterval.radiusSet = Set.Icc 0 1
``` -/
theorem unitInterval_radiusSet :
    unitInterval.radiusSet = Set.Icc 0 1 := by
  ext r
  simp only [mem_radiusSet, Set.mem_Icc]
  constructor
  · rintro ⟨i, hlo, hhi⟩
    have e1 : unitInterval.inner i = 0 := rfl
    have e2 : unitInterval.outer i = 1 := rfl
    rw [e1] at hlo
    rw [e2] at hhi
    exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨0, hlo, hhi⟩

/-- The distinguished slit is exactly the complex real-axis segment `[0,1]`.

```lean
theorem unitInterval_slitSet :
    unitInterval.slitSet = Set.Icc 0 1 ×ℂ ({0} : Set ℝ)
``` -/
theorem unitInterval_slitSet :
    unitInterval.slitSet = Set.Icc 0 1 ×ℂ ({0} : Set ℝ) := by
  unfold slitSet
  rw [unitInterval_radiusSet]

end RadialSlitData

end Complex
