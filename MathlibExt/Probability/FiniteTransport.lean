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
public import MathlibExt.Probability.FiniteDist
public import MathlibExt.Probability.MarkovMixing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite probability vectors, couplings and the earthmover value

Finite probability vectors as raw real-valued functions (the convention
of `MathlibExt.Probability.MarkovMixing.tvDist`), kernel pushforwards of
such vectors, couplings between two such vectors, transport cost, and
the earthmover (optimal-transport) value between two probability distributions, together
with the basic total-variation lemmas and the transport bound for the
expectation gap of a `1`-Lipschitz score.

`earthmover` takes its marginals in the subtype `{p // IsDist p}` of
probability vectors, so its defining infimum ranges over a nonempty set
of couplings (`exists_coupling`). The auxiliary `bias S T f` is the
expectation gap of a single real-valued score between the two
distributions `S` and `T`.

The ground cost `d` is unconstrained throughout, so for signed costs
the earthmover value can be negative and is not a distance; it is the
earthmover distance when `d` is a metric.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MathlibExt.Probability.FiniteTransport

@[expose] public section

noncomputable section

export MathlibExt.Probability.FiniteDist (IsDist)

/-- The distribution obtained by pushing a mass function `S` forward
along a kernel `M`: outcome `o` has mass `∑ x, S x * M x o`. -/
def inducedDist {V O : Type*} [Fintype V] (M : V → O → ℝ) (S : V → ℝ) :
    O → ℝ :=
  fun o => ∑ x, S x * M x o

/-- The pushforward of a probability vector along a row-stochastic
kernel is a probability vector. -/
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

/-- A coupling of `S` and `T`: a nonnegative matrix with row sums `S` and
column sums `T`. -/
def IsCoupling {V : Type*} [Fintype V] (S T : V → ℝ) (π : V → V → ℝ) :
    Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = S x) ∧ (∀ y, ∑ x, π x y = T y)

/-- Transport cost of a matrix `π` under the ground cost `d`. -/
def transportCost {V : Type*} [Fintype V] (d : V → V → ℝ) (π : V → V → ℝ) :
    ℝ :=
  ∑ x, ∑ y, π x y * d x y

/-- Earthmover (optimal-transport) value between two probability
distributions: the infimum of transport costs over all couplings. The
ground cost `d` is unconstrained, so for signed costs this value can be
negative and is not in general a distance; it is the earthmover
distance when `d` is a metric. The marginals range over the subtype of
probability vectors, so a coupling always exists (`exists_coupling`)
and the infimum is over a nonempty index set. -/
noncomputable def earthmover {V : Type*} [Fintype V] (d : V → V → ℝ)
    (S T : {p : V → ℝ // IsDist p}) : ℝ :=
  ⨅ π : {π // IsCoupling S.1 T.1 π}, transportCost d π

/-- Expectation gap of a real-valued score `f` between the distributions
`S` and `T`. -/
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

/-- Couplings of two probability distributions exist, as a nonempty
subtype (the index set of `earthmover`). -/
theorem nonempty_couplingSubtype {V : Type*} [Fintype V]
    (S T : {p : V → ℝ // IsDist p}) :
    Nonempty {π // IsCoupling S.1 T.1 π} := by
  obtain ⟨π, hπ⟩ := exists_coupling S.2 T.2
  exact ⟨⟨π, hπ⟩⟩

/-- Anything below every coupling cost is below the earthmover value. -/
theorem le_earthmover {V : Type*} [Fintype V] {d : V → V → ℝ}
    {S T : {p : V → ℝ // IsDist p}} {a : ℝ}
    (h : ∀ π, IsCoupling S.1 T.1 π → a ≤ transportCost d π) :
    a ≤ earthmover d S T := by
  have hne := nonempty_couplingSubtype S T
  unfold earthmover
  exact @le_ciInf _ _ _ hne _ _ (fun π' => h π'.1 π'.2)

/-- The earthmover value is at most the cost of any one coupling. -/
theorem earthmover_le_transportCost {V : Type*} [Fintype V] {d : V → V → ℝ}
    {S T : {p : V → ℝ // IsDist p}} {π : V → V → ℝ}
    (hπ : IsCoupling S.1 T.1 π) :
    earthmover d S T ≤ transportCost d π := by
  classical
  have hSle : ∀ x, S.1 x ≤ 1 := by
    intro x
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := S.1) (fun i _ => S.2.1 i) (Finset.mem_univ x)
    rwa [S.2.2] at h
  have hbdd : BddBelow (Set.range
      (fun π' : {π // IsCoupling S.1 T.1 π} => transportCost d π'.1)) := by
    refine ⟨-(∑ x, ∑ y, |d x y|), ?_⟩
    rintro - ⟨π', rfl⟩
    obtain ⟨hnn, hrow, -⟩ := π'.2
    have hle1 : ∀ x y, π'.1 x y ≤ 1 := by
      intro x y
      calc π'.1 x y ≤ ∑ y', π'.1 x y' :=
            Finset.single_le_sum (f := π'.1 x) (fun i _ => hnn x i)
              (Finset.mem_univ y)
        _ = S.1 x := hrow x
        _ ≤ 1 := hSle x
    unfold transportCost
    calc -(∑ x, ∑ y, |d x y|) = ∑ x, ∑ y, -|d x y| := by
          simp only [← Finset.sum_neg_distrib]
      _ ≤ ∑ x, ∑ y, π'.1 x y * d x y := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          have h1 : π'.1 x y * |d x y| ≤ |d x y| :=
            mul_le_of_le_one_left (abs_nonneg _) (hle1 x y)
          have h2 : -(π'.1 x y * d x y) ≤ π'.1 x y * |d x y| := by
            have h := neg_le_abs (π'.1 x y * d x y)
            rwa [abs_mul, abs_of_nonneg (hnn x y)] at h
          linarith
  unfold earthmover
  exact ciInf_le hbdd ⟨π, hπ⟩

/-- The expectation gap of a 1-Lipschitz score is bounded by the
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

/-- The score-gap bound against the earthmover value: the expectation
gap is below every coupling cost, hence below their infimum. -/
theorem bias_le_earthmover {V : Type*} [Fintype V]
    {d : V → V → ℝ} {S T : {p : V → ℝ // IsDist p}} {f : V → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ d x y) :
    bias S.1 T.1 f ≤ earthmover d S T :=
  le_earthmover (fun _π hπ => bias_le_transportCost hπ hf)

end

end

end MathlibExt.Probability.FiniteTransport
