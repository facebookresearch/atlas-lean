/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.FiniteTransport
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Individual fairness and the earthmover bound

Individual fairness in the sense of Dwork, Hardt, Pitassi, Reingold and
Zemel, "Fairness through awareness", *Proceedings of the 3rd Innovations
in Theoretical Computer Science Conference* (ITCS 2012), 214–226
(arXiv:1104.3913): a randomized classifier is fair when it is Lipschitz
from the task metric on individuals to total variation distance on
outcome distributions.

Correspondence with the paper:

* `IsDist` (`MathlibExt.Probability.FiniteTransport.IsDist`) is a
  probability vector, and `IsLipschitzFair` is the paper's
  `(D, d)`-Lipschitz condition of Definition 2.1 with the outcome
  distance `D` taken to be total variation distance
  (`MathlibExt.Probability.MarkovMixing.tvDist`); in particular every
  classifier row must be a probability distribution on a finite outcome
  set.
* `isLipschitzFair_convexCombo` is the convexity of the set of
  classifiers that are Lipschitz for one task metric `d`, the set behind
  the paper's linear program (Figure 1 and Lemma 2.1); the
  linear-programming formulation itself is not formalized here.
* The outcome distribution of a classifier `M` on a population `S` is
  the vector-matrix product `S ᵥ* Matrix.of M` (Mathlib's
  `Matrix.vecMul`), with entries `∑ x, S x * M x o`.
* `earthmover` (`MathlibExt.Probability.FiniteTransport.earthmover`, on
  probability-distribution subtypes) is the infimum of transport costs
  over all couplings (`IsCoupling`, `transportCost`). The paper's
  earthmover distance (Definition 3.3) takes a nonnegative distance
  function as its cost; the finite-transport API accepts any real-valued
  cost, so a signed cost can make the value negative (its tests compute
  the value `-1` for one), and for a nonnegative cost it is the paper's
  earthmover distance.
* `tvDist_vecMul_le_earthmover` is the per-classifier form of the
  paper's earthmover bound: for one classifier on a finite outcome set
  that is Lipschitz-fair with respect to a task metric `d`, the total
  variation distance between the induced outcome distributions on two
  populations over a finite set of individuals (its
  statistical-parity gap in the sense of Definition 3.1) is at most their
  earthmover distance for the same `d`. In the paper
  this bound for a fixed classifier follows by combining Lemma 3.1 with
  Theorem 3.3, whose statement bounds the worst-case bias
  `bias_{Dtv, d}` of Definition 3.2, the maximum over all
  `(D, d)`-Lipschitz binary classifiers. Neither that maximum nor
  Theorem 3.3's equality case for metrics bounded by `1` is formalized
  here.

The auxiliary `bias S T f`
(`MathlibExt.Probability.FiniteTransport.bias`) is the absolute
difference of the weighted sums of a single real-valued score `f` under
two weight vectors; it is an expectation gap between two populations
when both weight vectors are nonnegative and sum to one. For
`1`-Lipschitz scores and probability distributions `S` and `T`,
`bias_le_earthmover` bounds that gap by the earthmover value. It is
neither the fixed-classifier statistical-parity gap of
Definition 3.1 (a total variation distance between induced outcome
distributions, bounded in `tvDist_vecMul_le_earthmover`) nor the
worst-case `bias_{D, d}` of Definition 3.2.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace Cslib.MachineLearning.IndividualFairness

@[expose] public section

noncomputable section

open MathlibExt.Probability.FiniteTransport
open MathlibExt.Probability.MarkovMixing (tvDist)

/-- **Individual fairness as a Lipschitz condition.** For a task metric `d : V → V → ℝ`
(any real-valued function) and a randomized classifier `M : V → O → ℝ` with finitely many
outcomes, `IsLipschitzFair d M` holds when every row `M x` is a probability distribution
on the outcomes (nonnegative entries summing to `1`) and the total variation distance
between the outcome distributions of any two individuals is at most their task-metric
distance: `tvDist (M x) (M y) ≤ d x y` for all `x, y`. -/
def IsLipschitzFair {V O : Type*} [Fintype O] (d : V → V → ℝ)
    (M : V → O → ℝ) : Prop :=
  (∀ x, IsDist (M x)) ∧
    ∀ x y, tvDist (M x) (M y) ≤ d x y

/-- **Constant classifiers are individually fair.** For a task metric `d` with
`0 ≤ d x y` for all `x, y` and a probability distribution `r` on a finite outcome set
(nonnegative entries summing to `1`), the classifier giving every individual the outcome
distribution `r` is individually fair with respect to `d`. -/
theorem isLipschitzFair_const {V O : Type*} [Fintype O] {d : V → V → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (r : O → ℝ) (hr : IsDist r) :
    IsLipschitzFair d (fun _ => r) := by
  refine ⟨fun _ => hr, ?_⟩
  intro x y
  change tvDist r r ≤ d x y
  rw [MathlibExt.Probability.MarkovMixing.tvDist_self]
  exact hd x y

/-- **Fair classifiers are close outcome by outcome.** For a classifier `M` on a finite
outcome set that is individually fair with respect to a task metric `d` (every row a
probability distribution and `tvDist (M x) (M y) ≤ d x y`), the probabilities of each
outcome `o` satisfy `|M x o - M y o| ≤ d x y`. -/
theorem abs_outcome_sub_le_of_fair {V O : Type*} [Fintype O]
    {d : V → V → ℝ} {M : V → O → ℝ} (hM : IsLipschitzFair d M)
    (x y : V) (o : O) :
    |M x o - M y o| ≤ d x y := by
  obtain ⟨_, hMx_sum⟩ := hM.1 x
  obtain ⟨_, hMy_sum⟩ := hM.1 y
  have hsum : ∑ i, M x i = ∑ i, M y i := by rw [hMx_sum, hMy_sum]
  have h := abs_event_sub_le_tvDist (M x) (M y) hsum {o}
  rw [Finset.sum_singleton, Finset.sum_singleton] at h
  exact h.trans (hM.2 x y)

/-- **Lipschitz randomized classifiers form a convex set.** For classifiers `M` and `M'` on a
finite outcome set that are individually fair with respect to the same task metric `d` and a
weight `a` with `0 ≤ a ≤ 1`, the mixture with outcome probabilities
`a * M x o + (1 - a) * M' x o` is individually fair with respect to `d`. -/
theorem isLipschitzFair_convexCombo {V O : Type*} [Fintype O]
    {d : V → V → ℝ} {M M' : V → O → ℝ} (hM : IsLipschitzFair d M)
    (hM' : IsLipschitzFair d M') {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    IsLipschitzFair d (fun x o => a * M x o + (1 - a) * M' x o) := by
  have ha1 : 0 ≤ 1 - a := by linarith
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨hMnn, hMsum⟩ := hM.1 x
    obtain ⟨hMnn', hMsum'⟩ := hM'.1 x
    refine ⟨fun o => add_nonneg (mul_nonneg ha (hMnn o))
      (mul_nonneg ha1 (hMnn' o)), ?_⟩
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hMsum,
      hMsum']
    ring
  intro x y
  change tvDist (fun o => a * M x o + (1 - a) * M' x o)
      (fun o => a * M y o + (1 - a) * M' y o) ≤ d x y
  unfold tvDist
  change (1 / 2 : ℝ) * ∑ o, |(a * M x o + (1 - a) * M' x o)
      - (a * M y o + (1 - a) * M' y o)| ≤ d x y
  have hpt : ∀ o : O, |(a * M x o + (1 - a) * M' x o)
      - (a * M y o + (1 - a) * M' y o)|
      ≤ a * |M x o - M y o| + (1 - a) * |M' x o - M' y o| := by
    intro o
    have e : (a * M x o + (1 - a) * M' x o)
        - (a * M y o + (1 - a) * M' y o)
        = a * (M x o - M y o) + (1 - a) * (M' x o - M' y o) := by
      rw [add_sub_add_comm, ← mul_sub, ← mul_sub]
    rw [e]
    calc |a * (M x o - M y o) + (1 - a) * (M' x o - M' y o)|
        ≤ |a * (M x o - M y o)| + |(1 - a) * (M' x o - M' y o)| :=
          abs_add_le _ _
      _ = a * |M x o - M y o| + (1 - a) * |M' x o - M' y o| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg ha1]
  have hsum : (∑ o, |(a * M x o + (1 - a) * M' x o)
      - (a * M y o + (1 - a) * M' y o)|)
      ≤ ∑ o, (a * |M x o - M y o| + (1 - a) * |M' x o - M' y o|) :=
    Finset.sum_le_sum (fun o _ => hpt o)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h1 : tvDist (M x) (M y) ≤ d x y := hM.2 x y
  have h2 : tvDist (M' x) (M' y) ≤ d x y := hM'.2 x y
  unfold tvDist at h1 h2
  have hmul : (1 / 2 : ℝ) * (∑ o, |(a * M x o + (1 - a) * M' x o)
      - (a * M y o + (1 - a) * M' y o)|)
      ≤ (1 / 2) * (a * ∑ o, |M x o - M y o|
        + (1 - a) * ∑ o, |M' x o - M' y o|) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hdecomp : (1 / 2 : ℝ) * (a * ∑ o, |M x o - M y o|
      + (1 - a) * ∑ o, |M' x o - M' y o|)
      = a * ((1 / 2) * ∑ o, |M x o - M y o|)
        + (1 - a) * ((1 / 2) * ∑ o, |M' x o - M' y o|) := by
    ring
  rw [hdecomp] at hmul
  have hle1 : a * ((1 / 2) * ∑ o, |M x o - M y o|) ≤ a * d x y :=
    mul_le_mul_of_nonneg_left h1 ha
  have hle2 : (1 - a) * ((1 / 2) * ∑ o, |M' x o - M' y o|)
      ≤ (1 - a) * d x y :=
    mul_le_mul_of_nonneg_left h2 ha1
  have hfin : a * d x y + (1 - a) * d x y = d x y := by ring
  calc (1 / 2 : ℝ) * (∑ o, |(a * M x o + (1 - a) * M' x o)
      - (a * M y o + (1 - a) * M' y o)|)
      ≤ a * ((1 / 2) * ∑ o, |M x o - M y o|)
        + (1 - a) * ((1 / 2) * ∑ o, |M' x o - M' y o|) := hmul
    _ ≤ a * d x y + (1 - a) * d x y := add_le_add hle1 hle2
    _ = d x y := hfin

/-- **Classifier-level transport bound.** Let `M` be a classifier on a finite outcome set that
is individually fair with respect to a task metric `d`, `S T : V → ℝ` weight vectors on a
finite set of individuals, not necessarily probability distributions, and `π` a coupling of
them (nonnegative entries, row sums `S`, column sums `T`). Then the total variation distance
between the outcome vectors `S ᵥ* Matrix.of M` and `T ᵥ* Matrix.of M`, with entries
`∑ x, S x * M x o` and `∑ x, T x * M x o`, is at most `transportCost d π`, the cost of `π` for
the same `d`. -/
theorem tvDist_vecMul_le_transportCost {V O : Type*} [Fintype V]
    [Fintype O] {d : V → V → ℝ} {M : V → O → ℝ} {S T : V → ℝ}
    {π : V → V → ℝ} (hM : IsLipschitzFair d M) (hπ : IsCoupling S T π) :
    tvDist (S ᵥ* Matrix.of M) (T ᵥ* Matrix.of M) ≤ transportCost d π := by
  obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ := hπ
  have hdiff : ∀ o : O, (S ᵥ* Matrix.of M) o - (T ᵥ* Matrix.of M) o
      = ∑ x, ∑ y, π x y * (M x o - M y o) := by
    intro o
    have hS : (S ᵥ* Matrix.of M) o = ∑ x, ∑ y, π x y * M x o := by
      rw [Matrix.vecMul_apply_eq_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      change S x * M x o = ∑ y, π x y * M x o
      rw [← hπ_row x, Finset.sum_mul]
    have hT : (T ᵥ* Matrix.of M) o = ∑ x, ∑ y, π x y * M y o := by
      rw [Matrix.vecMul_apply_eq_sum]
      calc (∑ y, T y * Matrix.of M y o)
          = ∑ y, ∑ x, π x y * M y o := by
            refine Finset.sum_congr rfl fun y _ => ?_
            change T y * M y o = ∑ x, π x y * M y o
            rw [← hπ_col y, Finset.sum_mul]
        _ = ∑ x, ∑ y, π x y * M y o := Finset.sum_comm
    rw [hS, hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => (mul_sub ..).symm
  have hpt : ∀ o : O, |(S ᵥ* Matrix.of M) o - (T ᵥ* Matrix.of M) o|
      ≤ ∑ x, ∑ y, π x y * |M x o - M y o| := by
    intro o
    rw [hdiff o]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun x _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun y _ => ?_
    rw [abs_mul, abs_of_nonneg (hπ_nonneg x y)]
  have hsum : (∑ o, |(S ᵥ* Matrix.of M) o - (T ᵥ* Matrix.of M) o|)
      ≤ ∑ o, ∑ x, ∑ y, π x y * |M x o - M y o| :=
    Finset.sum_le_sum fun o _ => hpt o
  have hswap : (∑ o, ∑ x, ∑ y, π x y * |M x o - M y o|)
      = ∑ x, ∑ y, ∑ o, π x y * |M x o - M y o| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have hfactor : ∀ x y : V, (∑ o, π x y * |M x o - M y o|)
      = π x y * ∑ o, |M x o - M y o| :=
    fun x y => (Finset.mul_sum ..).symm
  unfold tvDist transportCost
  calc (1 / 2) * ∑ o, |(S ᵥ* Matrix.of M) o - (T ᵥ* Matrix.of M) o|
      ≤ (1 / 2) * ∑ o, ∑ x, ∑ y, π x y * |M x o - M y o| :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ∑ x, ∑ y, π x y * ((1 / 2) * ∑ o, |M x o - M y o|) := by
        rw [hswap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfactor x y]
        ring
    _ ≤ ∑ x, ∑ y, π x y * d x y := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_left (hM.2 x y) (hπ_nonneg x y)

/-- **Classifier-level earthmover bound.** For a classifier `M` on a finite outcome set that is
individually fair with respect to a task metric `d` and probability distributions `S` and `T`
on a finite set of individuals (nonnegative entries summing to `1`), the total variation
distance between the induced outcome distributions `S ᵥ* Matrix.of M` and `T ᵥ* Matrix.of M`,
with entries `∑ x, S x * M x o` and `∑ x, T x * M x o`, is at most `earthmover d S T`, the
earthmover value of `S` and `T` for the same `d`. -/
theorem tvDist_vecMul_le_earthmover {V O : Type*} [Fintype V]
    [Fintype O] {d : V → V → ℝ} {M : V → O → ℝ} {S T : V → ℝ}
    (hM : IsLipschitzFair d M) (hS : IsDist S) (hT : IsDist T) :
    tvDist (S ᵥ* Matrix.of M) (T ᵥ* Matrix.of M) ≤ earthmover d ⟨S, hS⟩ ⟨T, hT⟩ :=
  le_earthmover (fun _π hπ => tvDist_vecMul_le_transportCost hM hπ)

end

end

end Cslib.MachineLearning.IndividualFairness
