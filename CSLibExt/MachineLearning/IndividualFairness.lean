/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import MathlibExt.Probability.MarkovMixing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace Cslib.MachineLearning.IndividualFairness

@[expose] public section

noncomputable section

/-- A probability vector on a finite type: nonnegative entries summing to 1. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Individual fairness as a Lipschitz condition: the total variation
distance between the outcome distributions of any two individuals is at most
their task-metric distance. -/
def IsLipschitzFair {V O : Type*} [Fintype O] (d : V → V → ℝ)
    (M : V → O → ℝ) : Prop :=
  (∀ x, IsDist (M x)) ∧
    ∀ x y, MathlibExt.Probability.MarkovMixing.tvDist (M x) (M y) ≤ d x y

/-- A coupling of `S` and `T`: a nonnegative matrix with row sums `S` and
column sums `T`. -/
def IsCoupling {V : Type*} [Fintype V] (S T : V → ℝ) (π : V → V → ℝ) :
    Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = S x) ∧ (∀ y, ∑ x, π x y = T y)

/-- Transport cost of a matrix `π` under the ground distance `d`. -/
def transportCost {V : Type*} [Fintype V] (d : V → V → ℝ) (π : V → V → ℝ) :
    ℝ :=
  ∑ x, ∑ y, π x y * d x y

/-- Earthmover distance between `S` and `T`: the infimum of transport costs
over all couplings. -/
noncomputable def earthmover {V : Type*} [Fintype V] (d : V → V → ℝ)
    (S T : V → ℝ) : ℝ :=
  ⨅ π : {π // IsCoupling S T π}, transportCost d π

/-- Statistical-parity bias of an outcome score `f` between the
distributions `S` and `T`. -/
def bias {V : Type*} [Fintype V] (S T f : V → ℝ) : ℝ :=
  |∑ x, S x * f x - ∑ x, T x * f x|

/-- Total variation distance is nonnegative. -/
theorem tvDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ MathlibExt.Probability.MarkovMixing.tvDist p q := by
  unfold MathlibExt.Probability.MarkovMixing.tvDist
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- Total variation distance satisfies the triangle inequality. -/
theorem tvDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    MathlibExt.Probability.MarkovMixing.tvDist p r ≤ MathlibExt.Probability.MarkovMixing.tvDist p q + MathlibExt.Probability.MarkovMixing.tvDist q r := by
  unfold MathlibExt.Probability.MarkovMixing.tvDist
  have h : ∀ i : α, |p i - r i| ≤ |p i - q i| + |q i - r i| :=
    fun i => abs_sub_le _ _ _
  have hsum : ∑ i, |p i - r i| ≤ ∑ i, (|p i - q i| + |q i - r i|) :=
    Finset.sum_le_sum (fun i _ => h i)
  rw [Finset.sum_add_distrib] at hsum
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (1 / 2) * ∑ i, |p i - r i|
      ≤ (1 / 2) * (∑ i, |p i - q i| + ∑ i, |q i - r i|) :=
        mul_le_mul_of_nonneg_left hsum h12
    _ = (1 / 2) * ∑ i, |p i - q i| + (1 / 2) * ∑ i, |q i - r i| :=
        mul_add _ _ _

/-- On any event, the difference of accumulated mass is bounded by the total
variation distance, when both functions have equal total mass. -/
theorem abs_event_sub_le_tvDist {α : Type*} [Fintype α] (p q : α → ℝ)
    (hsum : ∑ i, p i = ∑ i, q i) (E : Finset α) :
    |∑ i ∈ E, p i - ∑ i ∈ E, q i| ≤ MathlibExt.Probability.MarkovMixing.tvDist p q := by
  classical
  have hsum0 : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have e1 : (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), |p i - q i|)
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), (p i - q i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact abs_of_pos hi
  have e2 : (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i), |p i - q i|)
      = -(∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i),
        (p i - q i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact abs_of_nonpos (le_of_not_gt hi)
  have hS : (∑ i, |p i - q i|)
      = (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), (p i - q i))
        - (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i),
          (p i - q i)) := by
    have h : (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), |p i - q i|)
        + (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i), |p i - q i|)
        = ∑ i, |p i - q i| :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [e1, e2] at h
    exact h.symm.trans (sub_eq_add_neg _ _).symm
  have h0 : (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), (p i - q i))
      + (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i), (p i - q i))
      = 0 := by
    have hsplit : (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i),
        (p i - q i))
        + (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i - q i), (p i - q i))
        = ∑ i, (p i - q i) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [hsum0] at hsplit
    exact hsplit
  have hkey : (∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i), (p i - q i))
      = MathlibExt.Probability.MarkovMixing.tvDist p q := by
    unfold MathlibExt.Probability.MarkovMixing.tvDist
    linarith [h0, hS]
  have hle : ∀ F : Finset α, ∑ i ∈ F, (p i - q i) ≤ MathlibExt.Probability.MarkovMixing.tvDist p q := by
    intro F
    have hsplitF : (∑ i ∈ F.filter (fun i => 0 < p i - q i), (p i - q i))
        + (∑ i ∈ F.filter (fun i => ¬ 0 < p i - q i), (p i - q i))
        = ∑ i ∈ F, (p i - q i) :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hnonpos : (∑ i ∈ F.filter (fun i => ¬ 0 < p i - q i), (p i - q i))
        ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      simp only [Finset.mem_filter] at hi
      exact le_of_not_gt hi.2
    have hsub : F.filter (fun i => 0 < p i - q i)
        ⊆ Finset.univ.filter (fun i => 0 < p i - q i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    have hmono : (∑ i ∈ F.filter (fun i => 0 < p i - q i), (p i - q i))
        ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < p i - q i),
          (p i - q i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact le_of_lt hi
    rw [hkey] at hmono
    calc ∑ i ∈ F, (p i - q i)
        = (∑ i ∈ F.filter (fun i => 0 < p i - q i), (p i - q i))
          + (∑ i ∈ F.filter (fun i => ¬ 0 < p i - q i), (p i - q i)) :=
          hsplitF.symm
      _ ≤ MathlibExt.Probability.MarkovMixing.tvDist p q + 0 := add_le_add hmono hnonpos
      _ = MathlibExt.Probability.MarkovMixing.tvDist p q := add_zero _
  have hE : (∑ i ∈ E, p i) - (∑ i ∈ E, q i) = ∑ i ∈ E, (p i - q i) := by
    rw [Finset.sum_sub_distrib]
  rw [hE]
  apply abs_le.mpr
  constructor
  · have hcompl : (∑ i ∈ Eᶜ, (p i - q i)) + (∑ i ∈ E, (p i - q i))
        = ∑ i, (p i - q i) :=
      Finset.sum_compl_add_sum _ _
    rw [hsum0] at hcompl
    have hleC := hle Eᶜ
    linarith [hcompl, hleC]
  · exact hle E

/-- Total variation distance between probability vectors is at most one. -/
theorem tvDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsDist p) (hq : IsDist q) :
    MathlibExt.Probability.MarkovMixing.tvDist p q ≤ 1 := by
  obtain ⟨hp_nonneg, hp_sum⟩ := hp
  obtain ⟨hq_nonneg, hq_sum⟩ := hq
  unfold MathlibExt.Probability.MarkovMixing.tvDist
  have hpt : ∀ i : α, |p i - q i| ≤ p i + q i := by
    intro i
    rw [abs_sub_le_iff]
    constructor <;> linarith [hp_nonneg i, hq_nonneg i]
  have hsum : ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) :=
    Finset.sum_le_sum (fun i _ => hpt i)
  rw [Finset.sum_add_distrib, hp_sum, hq_sum] at hsum
  linarith [hsum]

/-- Constant classifiers, giving every individual the same outcome
distribution, are individually fair for any nonnegative task metric. -/
theorem isLipschitzFair_const {V O : Type*} [Fintype O] {d : V → V → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (r : O → ℝ) (hr : IsDist r) :
    IsLipschitzFair d (fun _ => r) := by
  refine ⟨fun _ => hr, ?_⟩
  intro x y
  show MathlibExt.Probability.MarkovMixing.tvDist r r ≤ d x y
  rw [MathlibExt.Probability.MarkovMixing.tvDist_self]
  exact hd x y

/-- Fairness implies per-outcome closeness: for a fair classifier with
distribution rows, each outcome probability differs by at most the
task-metric distance. -/
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

/-- Convex combinations (mixtures) of individually fair classifiers are
individually fair. -/
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
  show MathlibExt.Probability.MarkovMixing.tvDist (fun o => a * M x o + (1 - a) * M' x o)
      (fun o => a * M y o + (1 - a) * M' y o) ≤ d x y
  unfold MathlibExt.Probability.MarkovMixing.tvDist
  show (1 / 2 : ℝ) * ∑ o, |(a * M x o + (1 - a) * M' x o)
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
  have h1 : MathlibExt.Probability.MarkovMixing.tvDist (M x) (M y) ≤ d x y := hM.2 x y
  have h2 : MathlibExt.Probability.MarkovMixing.tvDist (M' x) (M' y) ≤ d x y := hM'.2 x y
  unfold MathlibExt.Probability.MarkovMixing.tvDist at h1 h2
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

/-- Any two distributions admit a coupling, namely the independent
coupling with entries `S x * T y`. -/
theorem exists_coupling {V : Type*} [Fintype V] {S T : V → ℝ}
    (hS : IsDist S) (hT : IsDist T) :
    ∃ π : V → V → ℝ, IsCoupling S T π := by
  obtain ⟨hS_nonneg, hS_sum⟩ := hS
  obtain ⟨hT_nonneg, hT_sum⟩ := hT
  refine ⟨fun x y => S x * T y, ?_, ?_, ?_⟩
  · intro x y
    exact mul_nonneg (hS_nonneg x) (hT_nonneg y)
  · intro x
    show (∑ y, S x * T y) = S x
    rw [← Finset.mul_sum, hT_sum, mul_one]
  · intro y
    show (∑ x, S x * T y) = T y
    rw [← Finset.sum_mul, hS_sum, one_mul]

/-- The statistical-parity bias of a 1-Lipschitz score is bounded by the
transport cost of any coupling. -/
theorem bias_le_transportCost {V : Type*} [Fintype V] {d : V → V → ℝ}
    {S T f : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling S T π)
    (hf : ∀ x y, |f x - f y| ≤ d x y) :
    bias S T f ≤ transportCost d π := by
  classical
  obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ := hπ
  have hS : (∑ x, S x * f x) = ∑ x, ∑ y, π x y * f x := by
    apply Finset.sum_congr rfl
    intro x _
    show S x * f x = ∑ y, π x y * f x
    rw [← hπ_row x, Finset.sum_mul]
  have hT : (∑ y, T y * f y) = ∑ y, ∑ x, π x y * f y := by
    apply Finset.sum_congr rfl
    intro y _
    show T y * f y = ∑ x, π x y * f y
    rw [← hπ_col y, Finset.sum_mul]
  have hswap : (∑ y, ∑ x, π x y * f y) = ∑ x, ∑ y, π x y * f y :=
    Finset.sum_comm
  have hdiff : (∑ x, S x * f x) - (∑ x, T x * f x)
      = ∑ x, ∑ y, π x y * (f x - f y) := by
    rw [hS, hT, hswap, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    show (∑ y, π x y * f x) - (∑ y, π x y * f y)
      = ∑ y, π x y * (f x - f y)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    show π x y * f x - π x y * f y = π x y * (f x - f y)
    rw [mul_sub]
  have habs : ∀ (s : Finset V) (g : V → ℝ),
      |∑ x ∈ s, g x| ≤ ∑ x ∈ s, |g x| := by
    intro s g
    induction s using Finset.induction with
    | empty => simp
    | insert a s hnotmem ih =>
        rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
        exact (abs_add_le _ _).trans (add_le_add_right ih _)
  unfold bias transportCost
  rw [hdiff]
  calc |∑ x, ∑ y, π x y * (f x - f y)|
      ≤ ∑ x, |∑ y, π x y * (f x - f y)| := habs _ _
    _ ≤ ∑ x, ∑ y, |π x y * (f x - f y)| :=
        Finset.sum_le_sum (fun x _ => habs _ _)
    _ = ∑ x, ∑ y, π x y * |f x - f y| := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        show |π x y * (f x - f y)| = π x y * |f x - f y|
        rw [abs_mul, abs_of_nonneg (hπ_nonneg x y)]
    _ ≤ ∑ x, ∑ y, π x y * d x y := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hf x y) (hπ_nonneg x y)

/-- The bias bound against the earthmover distance: the bias is below every
coupling cost, hence below their infimum. -/
theorem bias_le_earthmover {V : Type*} [Fintype V]
    {d : V → V → ℝ} {S T f : V → ℝ} (hS : IsDist S) (hT : IsDist T)
    (hf : ∀ x y, |f x - f y| ≤ d x y) :
    bias S T f ≤ earthmover d S T := by
  obtain ⟨π, hπ⟩ := exists_coupling hS hT
  have hne : Nonempty {π // IsCoupling S T π} := ⟨⟨π, hπ⟩⟩
  show bias S T f ≤ ⨅ π : {π // IsCoupling S T π}, transportCost d π
  exact @le_ciInf _ _ _ hne _ _ (fun π' => bias_le_transportCost π'.2 hf)

/-- The outcome distribution induced by a classifier `M` on a population
distribution `S`: outcome `o` has mass `∑ x, S x * M x o`. -/
def inducedDist {V O : Type*} [Fintype V] (M : V → O → ℝ) (S : V → ℝ) :
    O → ℝ :=
  fun o => ∑ x, S x * M x o

/-- The induced outcome distribution is a probability vector when the
population and every classifier row are probability vectors. -/
theorem inducedDist_isDist {V O : Type*} [Fintype V] [Fintype O]
    {M : V → O → ℝ} {S : V → ℝ} (hS : IsDist S)
    (hrows : ∀ x, IsDist (M x)) :
    IsDist (inducedDist M S) := by
  obtain ⟨hS_nonneg, hS_sum⟩ := hS
  refine ⟨?_, ?_⟩
  · intro o
    unfold inducedDist
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hS_nonneg x) ((hrows x).1 o)
  · have hswap : (∑ o, inducedDist M S o) = ∑ x, ∑ o, S x * M x o :=
      Finset.sum_comm
    rw [hswap]
    calc (∑ x, ∑ o, S x * M x o)
        = ∑ x, S x * ∑ o, M x o := by
          refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
      _ = ∑ x, S x := by
          refine Finset.sum_congr rfl fun x _ => by rw [(hrows x).2, mul_one]
      _ = 1 := hS_sum

/-- Classifier-level transport bound: for every coupling, the total
variation distance between the induced outcome distributions is at most
that coupling's transport cost. -/
theorem tvDist_inducedDist_le_transportCost {V O : Type*} [Fintype V]
    [Fintype O] {d : V → V → ℝ} {M : V → O → ℝ} {S T : V → ℝ}
    {π : V → V → ℝ} (hM : IsLipschitzFair d M) (hπ : IsCoupling S T π) :
    MathlibExt.Probability.MarkovMixing.tvDist (inducedDist M S) (inducedDist M T) ≤ transportCost d π := by
  obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ := hπ
  have hdiff : ∀ o : O, inducedDist M S o - inducedDist M T o
      = ∑ x, ∑ y, π x y * (M x o - M y o) := by
    intro o
    have hS : inducedDist M S o = ∑ x, ∑ y, π x y * M x o := by
      unfold inducedDist
      refine Finset.sum_congr rfl fun x _ => ?_
      show S x * M x o = ∑ y, π x y * M x o
      rw [← hπ_row x, Finset.sum_mul]
    have hT : inducedDist M T o = ∑ x, ∑ y, π x y * M y o := by
      unfold inducedDist
      calc (∑ y, T y * M y o)
          = ∑ y, ∑ x, π x y * M y o := by
            refine Finset.sum_congr rfl fun y _ => ?_
            show T y * M y o = ∑ x, π x y * M y o
            rw [← hπ_col y, Finset.sum_mul]
        _ = ∑ x, ∑ y, π x y * M y o := Finset.sum_comm
    rw [hS, hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => (mul_sub ..).symm
  have hpt : ∀ o : O, |inducedDist M S o - inducedDist M T o|
      ≤ ∑ x, ∑ y, π x y * |M x o - M y o| := by
    intro o
    rw [hdiff o]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun x _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun y _ => ?_
    rw [abs_mul, abs_of_nonneg (hπ_nonneg x y)]
  have hsum : (∑ o, |inducedDist M S o - inducedDist M T o|)
      ≤ ∑ o, ∑ x, ∑ y, π x y * |M x o - M y o| :=
    Finset.sum_le_sum fun o _ => hpt o
  have hswap : (∑ o, ∑ x, ∑ y, π x y * |M x o - M y o|)
      = ∑ x, ∑ y, ∑ o, π x y * |M x o - M y o| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have hfactor : ∀ x y : V, (∑ o, π x y * |M x o - M y o|)
      = π x y * ∑ o, |M x o - M y o| :=
    fun x y => (Finset.mul_sum ..).symm
  unfold MathlibExt.Probability.MarkovMixing.tvDist transportCost
  calc (1 / 2) * ∑ o, |inducedDist M S o - inducedDist M T o|
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

/-- **Classifier-level earthmover bound.** For an individually fair
classifier, the total variation distance between the induced outcome
distributions on two populations is at most their earthmover distance. -/
theorem tvDist_inducedDist_le_earthmover {V O : Type*} [Fintype V]
    [Fintype O] {d : V → V → ℝ} {M : V → O → ℝ} {S T : V → ℝ}
    (hM : IsLipschitzFair d M) (hS : IsDist S) (hT : IsDist T) :
    MathlibExt.Probability.MarkovMixing.tvDist (inducedDist M S) (inducedDist M T) ≤ earthmover d S T := by
  obtain ⟨π, hπ⟩ := exists_coupling hS hT
  have hne : Nonempty {π // IsCoupling S T π} := ⟨⟨π, hπ⟩⟩
  show MathlibExt.Probability.MarkovMixing.tvDist (inducedDist M S) (inducedDist M T)
    ≤ ⨅ π : {π // IsCoupling S T π}, transportCost d π
  exact @le_ciInf _ _ _ hne _ _
    (fun π' => tvDist_inducedDist_le_transportCost hM π'.2)

end

end

end Cslib.MachineLearning.IndividualFairness
