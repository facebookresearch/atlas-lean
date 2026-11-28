/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic

/-!
# `L²`-medoids of a finite sample

For a finite sample `T 0, …, T (s - 1)` of points of a type `X`, possibly with repetitions, and a
distance `d : X → X → ℝ`, the `L²`-medoid set is the set of sampled points that minimise the sum
of squared distances to the sample, and the mean squared distance from a point to the sample
measures the dispersion around it. Kim, Rosenberg and Palacios (2020, Eqs. 5–7) use them as
measures of center and dispersion for samples of ranked tree shapes. Nothing is assumed of `d`.

## Main definitions and results

* `l2MedoidSet d T`: the `L²`-medoid set of the sample `T`.
* `meanSquaredDistance d T x`: the mean squared distance from `x` to the sample.
* `l2MedoidSet_nonempty`: a nonempty sample has an `L²`-medoid.
* `meanSquaredDistance_le_of_mem_l2MedoidSet`: an `L²`-medoid has the least mean squared distance
  to the sample among the sampled points.

## References

* J. Kim, N. A. Rosenberg and J. A. Palacios, *Distance metrics for ranked evolutionary trees*,
  Proc. Natl. Acad. Sci. USA 117 (2020), 28876–28886, Eqs. 5–7.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Statistics.Medoid

variable {X : Type*}

/-- The **`L²`-medoid set** of a finite sample `T 0, …, T (s - 1)`, possibly with repetitions,
for a distance `d` (Kim, Rosenberg and Palacios 2020, Eqs. 5 and 7): the sampled points that
minimise the sum of squared distances to the sample, used as a measure of center. -/
def l2MedoidSet (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) : Set X :=
  {x | (∃ k, T k = x) ∧ ∀ k, ∑ j, d x (T j) ^ 2 ≤ ∑ j, d (T k) (T j) ^ 2}

/-- The mean squared distance from a point `x` to a finite sample, used with an `L²`-medoid `x`
as a measure of dispersion (Kim, Rosenberg and Palacios 2020, Eq. 6). -/
noncomputable def meanSquaredDistance (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) (x : X) : ℝ :=
  (∑ j, d x (T j) ^ 2) / s

/-- A nonempty finite sample has an `L²`-medoid. -/
theorem l2MedoidSet_nonempty (d : X → X → ℝ) {s : ℕ} (T : Fin s → X) (hs : 0 < s) :
    (l2MedoidSet d T).Nonempty := by
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image univ (fun k => ∑ j, d (T k) (T j) ^ 2)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hs⟩⟩)
  exact ⟨T k, ⟨k, rfl⟩, fun k' => hk k' (Finset.mem_univ _)⟩

/-- An `L²`-medoid has the least mean squared distance to the sample among the sampled points. -/
theorem meanSquaredDistance_le_of_mem_l2MedoidSet (d : X → X → ℝ) {s : ℕ} (T : Fin s → X)
    {x : X} (hx : x ∈ l2MedoidSet d T) (k : Fin s) :
    meanSquaredDistance d T x ≤ meanSquaredDistance d T (T k) :=
  div_le_div_of_nonneg_right (hx.2 k) (Nat.cast_nonneg s)

end MathlibExt.Probability.Statistics.Medoid
