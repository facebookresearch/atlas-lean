/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lloyd's algorithm for `k`-means never increases the cost

The `k`-means objective (`cost`) of points `x i` in a real inner product space, indexed by any
finite type, an assignment `a i` of points to clusters, and centers `c j` is
`∑ ‖x i - c (a i)‖²`. Lloyd's algorithm (Lloyd, *Least squares quantization in PCM*, IEEE Trans.
Inform. Theory 28, 1982; Hastie, Tibshirani and Friedman, *The Elements of Statistical Learning*,
Chapter 14) alternates two steps: move each center to the centroid of its cluster (`centers`), and
reassign each point to a nearest center (`Nearest`).

Main results:

* `sum_sq_eq`: `∑ ‖x i - c‖² = ∑ ‖x i - μ‖² + |s| ‖μ - c‖²` for the centroid `μ` of the points in
  `s`; so the centroid minimizes the sum of squared distances (`sum_sq_centroid_le`).
* `cost_centers_le` (update step) and `cost_nearest_le` (assignment step): neither step increases
  the cost; `cost_lloyd_le`: one round does not either.
* `IsRun.antitone`: **the cost is non-increasing along every run of Lloyd's algorithm**;
  `exists_run`: runs exist from any start when `k > 0`.

No claim is made here about the number of rounds or about reaching a global optimum (Lloyd's
algorithm can stop at a local one).

## Relation to `FormalizedTextbooks`

This generalizes `FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/Ch22.lean`
from two clusters of real numbers to `k` clusters in any real inner product space, and Ch22
derives its results from this module. Its `kmeans_centroid_decomp` is the case `E = ℝ` of
`sum_sq_eq`. Its `kmeans_lloyd_mono` (one Lloyd round on two clusters, the reassignment written as
a `min` over the two new centroids) is the case `k = 2`, `E = ℝ` of `cost_lloyd_le`, with the
points indexed by the disjoint union `s₁ ⊕ s₂` of the two clusters.

## Cost model

No running-time model: the subject is the objective value, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.KMeans

open Finset RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} {k : ℕ}

/-- The centroid of the points in `s` (the zero vector if `s` is empty). -/
noncomputable def centroid (x : ι → E) (s : Finset ι) : E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, x i

/-- **The centroid minimizes the sum of squared distances**: for every point `c`,
`∑ ‖x i - c‖² = ∑ ‖x i - μ‖² + |s| ‖μ - c‖²` with `μ` the centroid. -/
theorem sum_sq_eq (x : ι → E) (s : Finset ι) (c : E) :
    ∑ i ∈ s, ‖x i - c‖ ^ 2 =
      ∑ i ∈ s, ‖x i - centroid x s‖ ^ 2 + s.card * ‖centroid x s - c‖ ^ 2 := by
  set μ := centroid x s with hμ
  have hsplit : ∀ i, ‖x i - c‖ ^ 2 =
      ‖x i - μ‖ ^ 2 + 2 * ⟪x i - μ, μ - c⟫ + ‖μ - c‖ ^ 2 := fun i => by
    rw [← norm_add_sq_real, sub_add_sub_cancel]
  simp only [hsplit, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, ← sum_inner]
  have hzero : ∑ i ∈ s, (x i - μ) = 0 := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · rw [sum_sub_distrib, sum_const, hμ, centroid, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      have : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
      rw [mul_inv_cancel₀ this, one_smul, sub_self]
  rw [hzero, inner_zero_left, mul_zero, add_zero]

theorem sum_sq_centroid_le (x : ι → E) (s : Finset ι) (c : E) :
    ∑ i ∈ s, ‖x i - centroid x s‖ ^ 2 ≤ ∑ i ∈ s, ‖x i - c‖ ^ 2 := by
  rw [sum_sq_eq x s c]
  have : 0 ≤ (s.card : ℝ) * ‖centroid x s - c‖ ^ 2 := by positivity
  linarith

/-- `a` assigns every point to a nearest center. -/
def Nearest (x : ι → E) (c : Fin k → E) (a : ι → Fin k) : Prop :=
  ∀ i j, ‖x i - c (a i)‖ ≤ ‖x i - c j‖

omit [InnerProductSpace ℝ E] in
/-- With at least one center, a nearest-center assignment exists. -/
theorem exists_nearest (x : ι → E) (c : Fin k → E) (hk : 0 < k) : ∃ a, Nearest x c a := by
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  choose a _ ha using fun i => exists_min_image univ (fun j => ‖x i - c j‖) hne
  exact ⟨a, fun i j => ha i j (mem_univ j)⟩

/-! ## The cost and the two steps of Lloyd's algorithm

The points are indexed by any finite type `ι` (for example `Fin n`). -/

variable [Fintype ι]

/-- The `k`-means cost of assigning point `i` to cluster `a i` with centers `c`: the sum of squared
distances to the assigned centers. -/
def cost (x : ι → E) (a : ι → Fin k) (c : Fin k → E) : ℝ := ∑ i, ‖x i - c (a i)‖ ^ 2

omit [InnerProductSpace ℝ E] in
/-- The cost, cluster by cluster. -/
theorem cost_eq_sum_clusters (x : ι → E) (a : ι → Fin k) (c : Fin k → E) :
    cost x a c = ∑ j, ∑ i ∈ univ.filter (fun i => a i = j), ‖x i - c j‖ ^ 2 := by
  rw [cost, ← Finset.sum_fiberwise univ a]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i hi => ?_
  rw [(mem_filter.1 hi).2]

/-- The update step: move each center to the centroid of its cluster (an empty cluster's center
moves to `0`, which does not affect the cost). -/
noncomputable def centers (x : ι → E) (a : ι → Fin k) : Fin k → E :=
  fun j => centroid x (univ.filter fun i => a i = j)

/-- **The update step never increases the cost**: for a fixed assignment, the centroids are the
best centers. -/
theorem cost_centers_le (x : ι → E) (a : ι → Fin k) (c : Fin k → E) :
    cost x a (centers x a) ≤ cost x a c := by
  rw [cost_eq_sum_clusters, cost_eq_sum_clusters]
  exact sum_le_sum fun j _ => sum_sq_centroid_le x _ (c j)

omit [InnerProductSpace ℝ E] in
/-- **The assignment step never increases the cost**: for fixed centers, nearest-center
assignment is optimal. -/
theorem cost_nearest_le {x : ι → E} {c : Fin k → E} {a' : ι → Fin k}
    (h : Nearest x c a') (a : ι → Fin k) : cost x a' c ≤ cost x a c := by
  refine sum_le_sum fun i _ => ?_
  have := h i (a i)
  have h0 := norm_nonneg (x i - c (a' i))
  nlinarith

/-- **One round of Lloyd's algorithm never increases the cost**: recompute the centers, then
reassign every point to a nearest new center. -/
theorem cost_lloyd_le {x : ι → E} {a a' : ι → Fin k} (c : Fin k → E)
    (h : Nearest x (centers x a) a') : cost x a' (centers x a) ≤ cost x a c :=
  (cost_nearest_le h a).trans (cost_centers_le x a c)

/-- A run of Lloyd's algorithm: assignments `as t` and centers `cs t`, where each round moves the
centers to the centroids of the previous assignment and reassigns every point to a nearest new
center. -/
def IsRun (x : ι → E) (as : ℕ → ι → Fin k) (cs : ℕ → Fin k → E) : Prop :=
  ∀ t, cs (t + 1) = centers x (as t) ∧ Nearest x (cs (t + 1)) (as (t + 1))

/-- **The cost never increases along a run of Lloyd's algorithm.** -/
theorem IsRun.antitone {x : ι → E} {as : ℕ → ι → Fin k} {cs : ℕ → Fin k → E}
    (h : IsRun x as cs) : Antitone fun t => cost x (as t) (cs t) := by
  refine antitone_nat_of_succ_le fun t => ?_
  obtain ⟨hc, ha⟩ := h t
  rw [hc] at ha ⊢
  exact cost_lloyd_le (cs t) ha

/-- With at least one center, every starting assignment and centers extend to a run. -/
theorem exists_run (x : ι → E) (hk : 0 < k) (a₀ : ι → Fin k) (c₀ : Fin k → E) :
    ∃ as cs, as 0 = a₀ ∧ cs 0 = c₀ ∧ IsRun x as cs := by
  choose step hstep using fun a : ι → Fin k => exists_nearest x (centers x a) hk
  let as : ℕ → ι → Fin k := fun t => Nat.rec a₀ (fun _ a => step a) t
  let cs : ℕ → Fin k → E := fun t => Nat.rec c₀ (fun t _ => centers x (as t)) t
  exact ⟨as, cs, rfl, rfl, fun t => ⟨rfl, hstep (as t)⟩⟩

end Cslib.MachineLearning.KMeans
