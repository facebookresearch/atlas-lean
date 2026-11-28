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
* `IsRun.exists_cost_const`: **the cost along every run is eventually constant**: the minimum
  among costs actually attained persists from its attaining time.

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

/-- **Centroid.** Let $x_i$ be points in a real inner product space and $s$ a finite set of
indices. The centroid of the points indexed by $s$ is $\frac{1}{|s|} \sum_{i \in s} x_i$; when $s$
is empty it is the zero vector. -/
noncomputable def centroid (x : ι → E) (s : Finset ι) : E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, x i

/-- **Sum of squared distances about the centroid.** Let $x_i$ ($i \in \iota$) be points in a
real inner product space $E$, let $s$ be a finite set of indices, and let $\mu$ be the centroid of
the points $x_i$ with $i \in s$. Then for every point $c \in E$,
$$
\sum_{i \in s} \|x_i - c\|^2 = \sum_{i \in s} \|x_i - \mu\|^2 + |s| \, \|\mu - c\|^2.
$$

Consequently the centroid minimizes the sum of squared distances to the points $x_i$, $i \in s$. -/
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

/-- The centroid of the empty finset is the zero vector. -/
theorem centroid_empty (x : ι → E) : centroid x ∅ = 0 := by
  simp [centroid]

/-- **Nearest-center assignment.** Given points $x_i$ ($i \in \iota$) in a normed additive
commutative group $E$ and centers $c_0, \dots, c_{k-1} \in E$, an assignment
$a : \iota \to \{0, \dots, k-1\}$ assigns every point to a nearest center when
$\|x_i - c_{a(i)}\| \le \|x_i - c_j\|$ for every index $i \in \iota$ and every $j < k$. -/
def Nearest (x : ι → E) (c : Fin k → E) (a : ι → Fin k) : Prop :=
  ∀ i j, ‖x i - c (a i)‖ ≤ ‖x i - c j‖

omit [InnerProductSpace ℝ E] in
/-- **Nearest-center assignments exist.** For any points $x_i$ in a normed additive commutative
group and any centers $c_0, \dots, c_{k-1}$ with $k \ge 1$, there is an assignment that sends
every point to a nearest center. -/
theorem exists_nearest (x : ι → E) (c : Fin k → E) (hk : 0 < k) : ∃ a, Nearest x c a := by
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  choose a _ ha using fun i => exists_min_image univ (fun j => ‖x i - c j‖) hne
  exact ⟨a, fun i j => ha i j (mem_univ j)⟩

/-! ## The cost and the two steps of Lloyd's algorithm

The points are indexed by any finite type `ι` (for example `Fin n`). -/

variable [Fintype ι]

/-- **The k-means cost.** For points $x_i$ ($i \in \iota$, a finite type) in a normed additive
commutative group, an assignment $a$ of each point $i$ to a cluster $a(i) \in \{0, \dots, k-1\}$
and centers $c_0, \dots, c_{k-1}$, the $k$-means cost is
$\sum_{i \in \iota} \lVert x_i - c_{a(i)} \rVert^2$, the sum of the squared distances from the
points to their assigned centers. -/
def cost (x : ι → E) (a : ι → Fin k) (c : Fin k → E) : ℝ := ∑ i, ‖x i - c (a i)‖ ^ 2

omit [InnerProductSpace ℝ E] in
/-- **The cost as a sum over clusters.** For points $x_i$ ($i \in \iota$, a finite type) in a
normed additive commutative group, an assignment $a$ of each point $i$ to a cluster
$a(i) \in \{0, \dots, k-1\}$ and centers $c_0, \dots, c_{k-1}$, the $k$-means cost equals
$\sum_{j} \sum_{i : a(i) = j} \lVert x_i - c_j \rVert^2$: for each cluster $j$, add up the squared
distances from the points assigned to $j$ to its center $c_j$. -/
theorem cost_eq_sum_clusters (x : ι → E) (a : ι → Fin k) (c : Fin k → E) :
    cost x a c = ∑ j, ∑ i ∈ univ.filter (fun i => a i = j), ‖x i - c j‖ ^ 2 := by
  rw [cost, ← Finset.sum_fiberwise univ a]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i hi => ?_
  rw [(mem_filter.1 hi).2]

omit [InnerProductSpace ℝ E] in
/-- Centers at unassigned clusters do not affect the cost. -/
theorem cost_congr_centers (x : ι → E) (a : ι → Fin k) (c c' : Fin k → E)
    (h : ∀ i, c (a i) = c' (a i)) : cost x a c = cost x a c' := by
  unfold cost
  apply sum_congr rfl
  intro i _
  rw [h i]

/-- **The centroid update step.** Let $x_i$ ($i \in \iota$, a finite type) be points in a real
inner product space and let $a$ assign each point $i$ to a cluster $a(i) \in \{0, \dots, k-1\}$.
The updated centers send each cluster $j$ to the centroid of the points $x_i$ with $a(i) = j$.
A cluster with no points gets the center $0$, which does not affect the $k$-means cost of $a$. -/
noncomputable def centers (x : ι → E) (a : ι → Fin k) : Fin k → E :=
  fun j => centroid x (univ.filter fun i => a i = j)

/-- If no point is assigned to cluster `j`, the updated center is the zero vector. -/
theorem centers_eq_zero_of_forall_ne (x : ι → E) (a : ι → Fin k) (j : Fin k)
    (h : ∀ i, a i ≠ j) : centers x a j = 0 := by
  have hfilter : (univ.filter fun i => a i = j) = ∅ :=
    filter_false_of_mem fun i _ hi => h i hi
  change centroid x (univ.filter fun i => a i = j) = 0
  rw [hfilter]
  exact centroid_empty x

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

/-- **Run of Lloyd's algorithm.** Let $x_i$ ($i \in \iota$, a finite index set) be points in a
real inner product space $E$. Sequences of assignments $a_t : \iota \to \{0, \dots, k-1\}$ and of
centers $c_t : \{0, \dots, k-1\} \to E$, indexed by $t \in \mathbb{N}$, form a run of Lloyd's
algorithm when for every $t$: for each $j < k$ the center $c_{t+1}(j)$ is the centroid of the
cluster $\{i : a_t(i) = j\}$ (the zero vector if this cluster is empty), and $a_{t+1}$ assigns
every point to a nearest center of $c_{t+1}$. The initial assignment $a_0$ and centers $c_0$ are
arbitrary. -/
def IsRun (x : ι → E) (as : ℕ → ι → Fin k) (cs : ℕ → Fin k → E) : Prop :=
  ∀ t, cs (t + 1) = centers x (as t) ∧ Nearest x (cs (t + 1)) (as (t + 1))

/-- **The cost never increases along a run of Lloyd's algorithm.** -/
theorem IsRun.antitone {x : ι → E} {as : ℕ → ι → Fin k} {cs : ℕ → Fin k → E}
    (h : IsRun x as cs) : Antitone fun t => cost x (as t) (cs t) := by
  refine antitone_nat_of_succ_le fun t => ?_
  obtain ⟨hc, ha⟩ := h t
  rw [hc] at ha ⊢
  exact cost_lloyd_le (cs t) ha

/-- **Runs of Lloyd's algorithm exist.** Let $x_i$ ($i \in \iota$, a finite type) be points in a
real inner product space and let $k \ge 1$. Every starting assignment $a_0$ of the points to
clusters $0, \dots, k-1$ and every choice of starting centers $c_0$ extend to a run of Lloyd's
algorithm: there are assignments $a_t$ and centers $c_t$ for $t \in \mathbb{N}$, equal to $a_0$
and $c_0$ at $t = 0$, that form a run. -/
theorem exists_run (x : ι → E) (hk : 0 < k) (a₀ : ι → Fin k) (c₀ : Fin k → E) :
    ∃ as cs, as 0 = a₀ ∧ cs 0 = c₀ ∧ IsRun x as cs := by
  choose step hstep using fun a : ι → Fin k => exists_nearest x (centers x a) hk
  let as : ℕ → ι → Fin k := fun t => Nat.rec a₀ (fun _ a => step a) t
  let cs : ℕ → Fin k → E := fun t => Nat.rec c₀ (fun t _ => centers x (as t)) t
  exact ⟨as, cs, rfl, rfl, fun t => ⟨rfl, hstep (as t)⟩⟩

/-- **The cost along every run is eventually constant.** From step one on, the centers are
determined by the previous assignment, so the initial cost together with the finite image of
the cost over ordered pairs of assignments is a finite set containing every cost of this run.
The costs actually attained by the run therefore have a minimum; from a time attaining that
attained minimum, `IsRun.antitone` keeps every later cost equal to it. This is the minimum
among costs actually attained, not the minimum of the full assignment-pair image, which the
run need not attain. -/
theorem IsRun.exists_cost_const {x : ι → E} {as : ℕ → ι → Fin k} {cs : ℕ → Fin k → E}
    (h : IsRun x as cs) : ∃ T, ∀ t, T ≤ t → cost x (as t) (cs t) = cost x (as T) (cs T) := by
  classical
  have hanti : Antitone fun t => cost x (as t) (cs t) := h.antitone
  have hsucc : ∀ n, cost x (as (n + 1)) (cs (n + 1)) =
      cost x (as (n + 1)) (centers x (as n)) := by
    intro n
    obtain ⟨hc, -⟩ := h n
    rw [hc]
  set img : Finset ℝ := Finset.univ.image
    fun p : (ι → Fin k) × (ι → Fin k) => cost x p.2 (centers x p.1) with himg
  set s : Finset ℝ := insert (cost x (as 0) (cs 0)) img with hs
  have hmem : ∀ t, cost x (as t) (cs t) ∈ s := by
    intro t
    refine match t with | 0 => ?_ | n + 1 => ?_
    · rw [hs]
      exact Finset.mem_insert_self _ _
    · rw [hs, hsucc n]
      refine Finset.mem_insert_of_mem ?_
      rw [himg]
      exact Finset.mem_image.mpr ⟨(as n, as (n + 1)), Finset.mem_univ _, rfl⟩
  set s' : Finset ℝ := s.filter (fun r => ∃ t, cost x (as t) (cs t) = r) with hs'
  have hne : s'.Nonempty := by
    refine ⟨cost x (as 0) (cs 0), ?_⟩
    rw [hs']
    exact Finset.mem_filter.mpr ⟨hmem 0, 0, rfl⟩
  obtain ⟨m, hms, hmin⟩ := Finset.exists_min_image s' id hne
  rw [hs', Finset.mem_filter] at hms
  obtain ⟨T, hT⟩ := hms.2
  refine ⟨T, fun t ht => le_antisymm (hanti ht) ?_⟩
  rw [hT]
  have hmem' : cost x (as t) (cs t) ∈ s' := by
    rw [hs']
    exact Finset.mem_filter.mpr ⟨hmem t, t, rfl⟩
  exact hmin _ hmem'

end Cslib.MachineLearning.KMeans
