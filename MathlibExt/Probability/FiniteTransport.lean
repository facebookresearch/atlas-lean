/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
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
of `MathlibExt.Probability.MarkovMixing.tvDist`), couplings between two
weight vectors, transport cost, and the earthmover (optimal-transport)
value between two probability distributions, together with the basic
total-variation lemmas, the probability-vector property of the
vector-matrix product `S ᵥ* Matrix.of M` (Mathlib's `Matrix.vecMul`:
the pushforward of `S` along the kernel `M`), and the transport bound
for the gap between the weighted sums of a `1`-Lipschitz score.

`earthmover` takes its marginals in the subtype `{p // IsDist p}` of
probability vectors, so its defining infimum ranges over a nonempty set
of couplings, which contains the independent coupling
(`isCoupling_mul`). The auxiliary `bias S T f` is the absolute
difference of the weighted sums of a single real-valued score under two
weight vectors `S` and `T`; it is an expectation gap when both weight
vectors are nonnegative and sum to one.

The ground cost `d` is unconstrained throughout, so for signed costs
the earthmover value can be negative and is not a distance; it is the
earthmover distance when `d` is a metric. This finite, real-valued
setting differs on purpose from the measure-theoretic one of
`MathlibExt.MeasureTheory.OptimalTransport.Wasserstein` (couplings of
probability measures on an extended metric space, costs `d(x, y) ^ p`
valued in `[0, ∞]`) and from the joint-`PMF` couplings of
`MathlibExt.Probability.TotalVariationCoupling`: here couplings are
real matrices with prescribed row and column sums, the ground cost is
any real function, and the coupling-level bounds hold for general
weight vectors.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace MathlibExt.Probability.FiniteTransport

@[expose] public section

noncomputable section

export MathlibExt.Probability.FiniteDist (IsDist)

open MathlibExt.Probability.MarkovMixing (tvDist)

/-- **Pushforward of a probability vector along a row-stochastic kernel.** If `S` is a
probability vector on a finite type `V` (nonnegative entries summing to `1`) and every row
`M x` of `M : V → O → ℝ` is a probability vector on a finite type `O`, then the
vector-matrix product `S ᵥ* Matrix.of M`, whose entry at `o` is `∑ x, S x * M x o`, is a
probability vector on `O`. -/
theorem isDist_vecMul {V O : Type*} [Fintype V] [Fintype O]
    {M : V → O → ℝ} {S : V → ℝ} (hS : IsDist S)
    (hrows : ∀ x, IsDist (M x)) :
    IsDist (S ᵥ* Matrix.of M) := by
  obtain ⟨hS_nonneg, hS_sum⟩ := hS
  refine ⟨?_, ?_⟩
  · intro o
    rw [Matrix.vecMul_apply_eq_sum]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hS_nonneg x) ((hrows x).1 o)
  · have hswap : (∑ o, (S ᵥ* Matrix.of M) o) = ∑ x, ∑ o, S x * M x o :=
      Finset.sum_comm
    rw [hswap]
    calc (∑ x, ∑ o, S x * M x o)
        = ∑ x, S x * ∑ o, M x o := by
          refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
      _ = ∑ x, S x := by
          refine Finset.sum_congr rfl fun x _ => by rw [(hrows x).2, mul_one]
      _ = 1 := hS_sum

/-- **Coupling of two weight vectors.** A matrix `π : V → V → ℝ` is a coupling of
`S T : V → ℝ` when its entries are nonnegative, its row sums are `S` and its column sums
are `T`: `0 ≤ π x y`, `∑ y, π x y = S x` and `∑ x, π x y = T y` for all `x, y`. The
weight vectors `S` and `T` need not be probability vectors. -/
def IsCoupling {V : Type*} [Fintype V] (S T : V → ℝ) (π : V → V → ℝ) :
    Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = S x) ∧ (∀ y, ∑ x, π x y = T y)

/-- **Transport cost of a plan.** For a ground cost `d : V → V → ℝ` and a matrix
`π : V → V → ℝ` on a finite type, the cost of the single plan `π` is
`∑ x, ∑ y, π x y * d x y`; the infimum of these costs over couplings is `earthmover`. -/
def transportCost {V : Type*} [Fintype V] (d : V → V → ℝ) (π : V → V → ℝ) :
    ℝ :=
  ∑ x, ∑ y, π x y * d x y

/-- **Earthmover value.** For probability distributions `S` and `T` on a finite type `V`
(nonnegative entries summing to `1`) and a ground cost `d : V → V → ℝ`, the earthmover
(optimal-transport) value is the infimum of `transportCost d π` over all couplings `π` of
`S` and `T`. The marginals range over the subtype of probability vectors, so a coupling
always exists (`isCoupling_mul`) and the infimum is over a nonempty index set. The ground
cost is unconstrained, so for signed costs the value can be negative and is not in general
a distance; it is the earthmover distance when `d` is a metric. -/
noncomputable def earthmover {V : Type*} [Fintype V] (d : V → V → ℝ)
    (S T : {p : V → ℝ // IsDist p}) : ℝ :=
  ⨅ π : {π // IsCoupling S.1 T.1 π}, transportCost d π

/-- **Expectation gap of a score.** For weight vectors `S T : V → ℝ` and a score
`f : V → ℝ` on a finite type, `bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|`, the
absolute difference of the weighted score sums. When `S` and `T` are probability
distributions (nonnegative entries summing to `1`) it is the gap between the expectations
of `f` under `S` and under `T`; for other weights it need not be an expectation gap. -/
def bias {V : Type*} [Fintype V] (S T f : V → ℝ) : ℝ :=
  |∑ x, S x * f x - ∑ x, T x * f x|

/-- **Total variation distance is nonnegative.** For any `p q : α → ℝ` on a finite type,
`0 ≤ tvDist p q`. -/
theorem tvDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ tvDist p q := by
  unfold tvDist
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- **Triangle inequality for total variation distance.** For any `p q r : α → ℝ` on a
finite type, `tvDist p r ≤ tvDist p q + tvDist q r`. -/
theorem tvDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    tvDist p r ≤ tvDist p q + tvDist q r := by
  unfold tvDist
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

/-- **Event masses differ by at most the total variation distance.** For `p q : α → ℝ` on
a finite type with equal total mass, `∑ i, p i = ∑ i, q i`, and any set `E` of points,
`|∑ i ∈ E, p i - ∑ i ∈ E, q i| ≤ tvDist p q`. -/
theorem abs_event_sub_le_tvDist {α : Type*} [Fintype α] (p q : α → ℝ)
    (hsum : ∑ i, p i = ∑ i, q i) (E : Finset α) :
    |∑ i ∈ E, p i - ∑ i ∈ E, q i| ≤ tvDist p q := by
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
      = tvDist p q := by
    unfold tvDist
    linarith [h0, hS]
  have hle : ∀ F : Finset α, ∑ i ∈ F, (p i - q i) ≤ tvDist p q := by
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
      _ ≤ tvDist p q + 0 := add_le_add hmono hnonpos
      _ = tvDist p q := add_zero _
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

/-- **Total variation distance between probability vectors is at most `1`.** For
probability vectors `p` and `q` on a finite type (nonnegative entries summing to `1`),
`tvDist p q ≤ 1`. -/
theorem tvDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsDist p) (hq : IsDist q) :
    tvDist p q ≤ 1 := by
  obtain ⟨hp_nonneg, hp_sum⟩ := hp
  obtain ⟨hq_nonneg, hq_sum⟩ := hq
  unfold tvDist
  have hpt : ∀ i : α, |p i - q i| ≤ p i + q i := by
    intro i
    rw [abs_sub_le_iff]
    constructor <;> linarith [hp_nonneg i, hq_nonneg i]
  have hsum : ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) :=
    Finset.sum_le_sum (fun i _ => hpt i)
  rw [Finset.sum_add_distrib, hp_sum, hq_sum] at hsum
  linarith [hsum]

/-- **Independent coupling.** For probability distributions `S` and `T` on a finite type
(nonnegative entries summing to `1`), the product matrix with entries `S x * T y` is a
coupling of `S` and `T`: its entries are nonnegative, its row sums are `S` and its column
sums are `T`. -/
theorem isCoupling_mul {V : Type*} [Fintype V] {S T : V → ℝ}
    (hS : IsDist S) (hT : IsDist T) :
    IsCoupling S T (fun x y => S x * T y) := by
  obtain ⟨hS_nonneg, hS_sum⟩ := hS
  obtain ⟨hT_nonneg, hT_sum⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact mul_nonneg (hS_nonneg x) (hT_nonneg y)
  · intro x
    change (∑ y, S x * T y) = S x
    rw [← Finset.mul_sum, hT_sum, mul_one]
  · intro y
    change (∑ x, S x * T y) = T y
    rw [← Finset.sum_mul, hS_sum, one_mul]

/-- **Couplings of probability distributions exist.** For probability distributions `S`
and `T` on a finite type (nonnegative entries summing to `1`), the type of couplings of
`S` and `T`, the index set of `earthmover`, is nonempty. -/
theorem nonempty_couplingSubtype {V : Type*} [Fintype V]
    (S T : {p : V → ℝ // IsDist p}) :
    Nonempty {π // IsCoupling S.1 T.1 π} :=
  ⟨⟨_, isCoupling_mul S.2 T.2⟩⟩

/-- **Lower bounds for the earthmover value.** Let `S` and `T` be probability
distributions on a finite type (nonnegative entries summing to `1`) and `d` a ground cost.
A real number `a` with `a ≤ transportCost d π` for every coupling `π` of `S` and `T`
satisfies `a ≤ earthmover d S T`. -/
theorem le_earthmover {V : Type*} [Fintype V] {d : V → V → ℝ}
    {S T : {p : V → ℝ // IsDist p}} {a : ℝ}
    (h : ∀ π, IsCoupling S.1 T.1 π → a ≤ transportCost d π) :
    a ≤ earthmover d S T := by
  have hne := nonempty_couplingSubtype S T
  unfold earthmover
  exact @le_ciInf _ _ _ hne _ _ (fun π' => h π'.1 π'.2)

/-- **The earthmover value is at most the cost of any coupling.** Let `S` and `T` be
probability distributions on a finite type (nonnegative entries summing to `1`), `d` a
ground cost and `π` a coupling of `S` and `T`. Then
`earthmover d S T ≤ transportCost d π`. -/
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

/-- **Score-gap bound for one coupling.** Let `S T : V → ℝ` be weight vectors on a finite
type, not necessarily probability distributions, and `π` a coupling of them (nonnegative
entries, row sums `S`, column sums `T`). For a score `f : V → ℝ` with
`|f x - f y| ≤ d x y` for all `x, y`, the gap
`bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|` is at most `transportCost d π`. -/
theorem bias_le_transportCost {V : Type*} [Fintype V] {d : V → V → ℝ}
    {S T f : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling S T π)
    (hf : ∀ x y, |f x - f y| ≤ d x y) :
    bias S T f ≤ transportCost d π := by
  obtain ⟨hπ_nonneg, hπ_row, hπ_col⟩ := hπ
  have hS : (∑ x, S x * f x) = ∑ x, ∑ y, π x y * f x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [← hπ_row x, Finset.sum_mul]
  have hT : (∑ y, T y * f y) = ∑ y, ∑ x, π x y * f y := by
    apply Finset.sum_congr rfl
    intro y _
    rw [← hπ_col y, Finset.sum_mul]
  have hswap : (∑ y, ∑ x, π x y * f y) = ∑ x, ∑ y, π x y * f y :=
    Finset.sum_comm
  have hdiff : (∑ x, S x * f x) - (∑ x, T x * f x)
      = ∑ x, ∑ y, π x y * (f x - f y) := by
    rw [hS, hT, hswap, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    change (∑ y, π x y * f x) - (∑ y, π x y * f y)
      = ∑ y, π x y * (f x - f y)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    change π x y * f x - π x y * f y = π x y * (f x - f y)
    rw [mul_sub]
  unfold bias transportCost
  rw [hdiff]
  calc |∑ x, ∑ y, π x y * (f x - f y)|
      ≤ ∑ x, |∑ y, π x y * (f x - f y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |π x y * (f x - f y)| :=
        Finset.sum_le_sum (fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x, ∑ y, π x y * |f x - f y| := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [abs_mul, abs_of_nonneg (hπ_nonneg x y)]
    _ ≤ ∑ x, ∑ y, π x y * d x y := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hf x y) (hπ_nonneg x y)

/-- **Score-gap bound by the earthmover value.** Let `S` and `T` be probability
distributions on a finite type `V` (nonnegative entries summing to `1`) and `f : V → ℝ` a
score with `|f x - f y| ≤ d x y` for all `x, y`. Then the gap between the expectations of
`f` under `S` and under `T`, `bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|`, is at most
`earthmover d S T`. -/
theorem bias_le_earthmover {V : Type*} [Fintype V]
    {d : V → V → ℝ} {S T : {p : V → ℝ // IsDist p}} {f : V → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ d x y) :
    bias S.1 T.1 f ≤ earthmover d S T :=
  le_earthmover (fun _π hπ => bias_le_transportCost hπ hf)

end

end

end MathlibExt.Probability.FiniteTransport
