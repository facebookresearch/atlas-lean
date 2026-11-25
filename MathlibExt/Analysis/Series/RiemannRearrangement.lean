/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace MathlibExt.Analysis.Series.RiemannRearrangementWanted

open BigOperators

/-- **Convergence of a series in order.** For a sequence $f : \mathbb{N} \to \mathbb{R}$ and
$a \in \mathbb{R}$, the series $\sum_n f(n)$ converges in order to $a$ when its partial sums
$\sum_{n=0}^{N-1} f(n)$ tend to $a$ as $N \to \infty$. -/
def OrderedHasSum (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a)

/-- **Convergence in order via partial sums.** For a sequence $f : \mathbb{N} \to \mathbb{R}$ and
$a \in \mathbb{R}$, the series $\sum_n f(n)$ converges in order to $a$ if and only if its partial
sums $\sum_{n=0}^{N-1} f(n)$ tend to $a$ as $N \to \infty$. -/
theorem orderedHasSum_iff (f : ℕ → ℝ) (a : ℝ) :
    OrderedHasSum f a ↔
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a) :=
  Iff.rfl

/-- **Terms of a convergent series tend to zero.** If $f : \mathbb{N} \to \mathbb{R}$ and the
series $\sum_n f(n)$ converges in order to some $s \in \mathbb{R}$, then $f(n) \to 0$ as
$n \to \infty$. -/
theorem orderedHasSum_tendsto_zero (f : ℕ → ℝ) (s : ℝ) (h : OrderedHasSum f s) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hsucc' : Filter.Tendsto (fun N => N + 1) (Filter.atTop : Filter ℕ) Filter.atTop :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr Filter.tendsto_id
  have hsucc : Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), f n) Filter.atTop (nhds s) :=
    h.comp hsucc'
  have hdiff : Filter.Tendsto
      (fun N => (∑ n ∈ Finset.range (N + 1), f n) - (∑ n ∈ Finset.range N, f n))
      Filter.atTop (nhds (s - s)) := hsucc.sub h
  simp only [sub_self] at hdiff
  have heq : (fun N => (∑ n ∈ Finset.range (N + 1), f n) - (∑ n ∈ Finset.range N, f n)) = f := by
    funext N
    rw [Finset.sum_range_succ]
    ring
  rwa [heq] at hdiff

private theorem max_neg_eq (x : ℝ) : max (-x) 0 = max x 0 - x := by
  by_cases h : 0 ≤ x
  · simp [max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]
  · push Not at h
    simp [max_eq_right (le_of_lt (by linarith : x < 0)), max_eq_left (by linarith : 0 ≤ -x)]

private theorem abs_eq_max_add (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  by_cases h : 0 ≤ x
  · simp [max_eq_left h, max_eq_right (by linarith : -x ≤ 0), abs_of_nonneg h]
  · push Not at h
    simp [max_eq_right (le_of_lt (by linarith : x < 0)), max_eq_left (by linarith : 0 ≤ -x),
      abs_of_neg (by linarith : x < 0)]

/-- Positive part diverges for a conditionally convergent series. -/
private theorem not_summable_pos_of (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    ¬ Summable (fun n => max (f n) 0) := by
  intro hpos
  have hpos_sum : OrderedHasSum (fun n => max (f n) 0) (∑' n, max (f n) 0) :=
    (hpos.hasSum).tendsto_sum_nat
  have hneg_eq : (fun n => max (-f n) 0) = (fun n => max (f n) 0 - f n) := by
    funext n
    exact max_neg_eq (f n)
  have hneg_sum : OrderedHasSum (fun n => max (-f n) 0) ((∑' n, max (f n) 0) - s) := by
    rw [hneg_eq]
    have hsub : Filter.Tendsto
        (fun N => (∑ n ∈ Finset.range N, max (f n) 0) - (∑ n ∈ Finset.range N, f n))
        Filter.atTop (nhds ((∑' n, max (f n) 0) - s)) := hpos_sum.sub hf
    have heq : (fun N => (∑ n ∈ Finset.range N, (max (f n) 0 - f n)))
        = (fun N => (∑ n ∈ Finset.range N, max (f n) 0) - (∑ n ∈ Finset.range N, f n)) := by
      funext N
      rw [Finset.sum_sub_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact hsub
  have habs_eq : (fun n => |f n|) = (fun n => max (f n) 0 + max (-f n) 0) := by
    funext n
    exact abs_eq_max_add (f n)
  have hnonneg_abs : ∀ n : ℕ, 0 ≤ |f n| := fun n => abs_nonneg _
  have habs_sum :
      OrderedHasSum (fun n => |f n|) ((∑' n, max (f n) 0) + ((∑' n, max (f n) 0) - s)) := by
    rw [habs_eq]
    have hadd : Filter.Tendsto
        (fun N => (∑ n ∈ Finset.range N, max (f n) 0) + (∑ n ∈ Finset.range N, max (-f n) 0))
        Filter.atTop (nhds ((∑' n, max (f n) 0) + ((∑' n, max (f n) 0) - s))) :=
      hpos_sum.add hneg_sum
    have heq : (fun N => (∑ n ∈ Finset.range N, (max (f n) 0 + max (-f n) 0)))
        = (fun N => (∑ n ∈ Finset.range N, max (f n) 0) +
            (∑ n ∈ Finset.range N, max (-f n) 0)) := by
      funext N
      rw [Finset.sum_add_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact hadd
  have habs_summable : Summable (fun n => |f n|) :=
    ((hasSum_iff_tendsto_nat_of_nonneg hnonneg_abs _).mpr habs_sum).summable
  exact hfa habs_summable

/-- Negative part diverges for a conditionally convergent series. -/
private theorem not_summable_neg_of (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    ¬ Summable (fun n => max (-f n) 0) := by
  have hneg_ordered : OrderedHasSum (fun n => -f n) (-s) := by
    have h : Filter.Tendsto (fun N => -(∑ n ∈ Finset.range N, f n)) Filter.atTop (nhds (-s)) :=
      hf.neg
    have heq : (fun N => ∑ n ∈ Finset.range N, (-f n))
        = (fun N => -(∑ n ∈ Finset.range N, f n)) := by
      funext N
      rw [Finset.sum_neg_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact h
  have habs_eq : (fun n => |(-f n)|) = (fun n => |f n|) := by
    funext n
    rw [abs_neg]
  have hfa' : ¬ Summable (fun n => |(-f n)|) := by
    rwa [habs_eq]
  have h := not_summable_pos_of (fun n => -f n) (-s) hneg_ordered hfa'
  simpa using h

/-- Nonnegative indices, enumerated in increasing order. Zeros are included here. -/
private noncomputable def posEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => 0 ≤ f n)

/-- Negative indices, enumerated in increasing order. -/
private noncomputable def negEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => f n < 0)

/-- Infinitely many nonnegative terms; otherwise the positive part would be summable. -/
private theorem posSet_infinite (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    (Set.ofPred fun n => 0 ≤ f n).Infinite := by
  have hpos : ¬ Summable (fun n => max (f n) 0) := not_summable_pos_of f s hf hfa
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hpos
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hlt
  push Not at hlt
  apply hn
  change max (f n) 0 = 0
  rw [max_eq_right (le_of_lt hlt)]

/-- Infinitely many negative terms; otherwise the negative part would be summable. -/
private theorem negSet_infinite (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    (Set.ofPred fun n => f n < 0).Infinite := by
  have hneg : ¬ Summable (fun n => max (-f n) 0) := not_summable_neg_of f s hf hfa
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hneg
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hlt
  push Not at hlt
  apply hn
  change max (-f n) 0 = 0
  rw [max_eq_right (neg_nonpos.mpr hlt)]

/-- The enumerated nonnegative terms still diverge to `+∞`: their partial sums form a
subsequence of the positive-part partial sums. -/
private theorem enum_pos_diverge (f : ℕ → ℝ)
    (htop : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (f n) 0)
      Filter.atTop Filter.atTop)
    (hP : (Set.ofPred fun n => 0 ≤ f n).Infinite) :
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop := by
  have hp : StrictMono (posEnum f) := Nat.nth_strictMono hP
  have hmem : ∀ i : ℕ, 0 ≤ f (posEnum f i) :=
    fun i => Nat.nth_mem_of_infinite hP i
  have hnth : ∀ n : ℕ, 0 ≤ f n →
      Nat.nth (fun n => 0 ≤ f n) (Nat.count (fun n => 0 ≤ f n) n) = n :=
    fun n hn => Nat.nth_count hn
  have key : ∀ N : ℕ, (∑ i ∈ Finset.range N, f (posEnum f i))
      = ∑ n ∈ Finset.range (posEnum f N), max (f n) 0 := by
    intro N
    have hsub : (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n)
        ⊆ Finset.range (posEnum f N) :=
      Finset.filter_subset _ _
    have hzero : ∀ x ∈ Finset.range (posEnum f N),
        x ∉ (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n) →
        max (f x) 0 = 0 := by
      intro x hxmem hx
      have hle : ¬ 0 ≤ f x := by
        simp only [Finset.mem_filter, not_and] at hx
        exact hx hxmem
      rw [max_eq_right (le_of_lt (lt_of_not_ge hle))]
    have heq : (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n)
        = (Finset.range N).image (posEnum f) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hPn⟩
        have hlt : Nat.count (fun n => 0 ≤ f n) n < N := by
          by_contra hcon
          push Not at hcon
          have h1 := hp.monotone hcon
          have h2 : posEnum f (Nat.count (fun n => 0 ≤ f n) n) = n := hnth n hPn
          omega
        refine ⟨Nat.count (fun n => 0 ≤ f n) n, hlt, ?_⟩
        show posEnum f _ = n
        simp only [posEnum]
        exact hnth n hPn
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hp hi, hmem i⟩
    calc (∑ i ∈ Finset.range N, f (posEnum f i))
        = ∑ i ∈ Finset.range N, max (f (posEnum f i)) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [max_eq_left (hmem i)]
      _ = ∑ n ∈ (Finset.range N).image (posEnum f), max (f n) 0 := by
          rw [Finset.sum_image (fun x _ y _ hxy => hp.injective hxy)]
      _ = ∑ n ∈ Finset.range (posEnum f N), max (f n) 0 := by
          rw [← heq]
          exact Finset.sum_subset hsub hzero
  have hcomp : (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      = (fun N => ∑ n ∈ Finset.range N, max (f n) 0) ∘ posEnum f :=
    funext key
  rw [hcomp]
  exact htop.comp hp.tendsto_atTop

/-- The enumerated negative terms (negated) still diverge to `+∞`. -/
private theorem enum_neg_diverge (f : ℕ → ℝ)
    (htop : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (-f n) 0)
      Filter.atTop Filter.atTop)
    (hQ : (Set.ofPred fun n => f n < 0).Infinite) :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop := by
  have hq : StrictMono (negEnum f) := Nat.nth_strictMono hQ
  have hmem : ∀ j : ℕ, 0 ≤ -f (negEnum f j) :=
    fun j => le_of_lt (neg_pos.mpr (Nat.nth_mem_of_infinite hQ j))
  have hmemQ : ∀ j : ℕ, f (negEnum f j) < 0 :=
    fun j => Nat.nth_mem_of_infinite hQ j
  have hnth : ∀ n : ℕ, f n < 0 →
      Nat.nth (fun n => f n < 0) (Nat.count (fun n => f n < 0) n) = n :=
    fun n hn => Nat.nth_count hn
  have key : ∀ N : ℕ, (∑ j ∈ Finset.range N, -f (negEnum f j))
      = ∑ n ∈ Finset.range (negEnum f N), max (-f n) 0 := by
    intro N
    have hsub : (Finset.range (negEnum f N)).filter (fun n => f n < 0)
        ⊆ Finset.range (negEnum f N) :=
      Finset.filter_subset _ _
    have hzero : ∀ x ∈ Finset.range (negEnum f N),
        x ∉ (Finset.range (negEnum f N)).filter (fun n => f n < 0) →
        max (-f x) 0 = 0 := by
      intro x hxmem hx
      have hle : ¬ f x < 0 := by
        simp only [Finset.mem_filter, not_and] at hx
        exact hx hxmem
      rw [max_eq_right (neg_nonpos.mpr (not_lt.mp hle))]
    have heq : (Finset.range (negEnum f N)).filter (fun n => f n < 0)
        = (Finset.range N).image (negEnum f) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hQn⟩
        have hlt : Nat.count (fun n => f n < 0) n < N := by
          by_contra hcon
          push Not at hcon
          have h1 := hq.monotone hcon
          have h2 : negEnum f (Nat.count (fun n => f n < 0) n) = n := hnth n hQn
          omega
        refine ⟨Nat.count (fun n => f n < 0) n, hlt, ?_⟩
        show negEnum f _ = n
        simp only [negEnum]
        exact hnth n hQn
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hq hj, hmemQ j⟩
    calc (∑ j ∈ Finset.range N, -f (negEnum f j))
        = ∑ j ∈ Finset.range N, max (-f (negEnum f j)) 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [max_eq_left (hmem j)]
      _ = ∑ n ∈ (Finset.range N).image (negEnum f), max (-f n) 0 := by
          rw [Finset.sum_image (fun x _ y _ hxy => hq.injective hxy)]
      _ = ∑ n ∈ Finset.range (negEnum f N), max (-f n) 0 := by
          rw [← heq]
          exact Finset.sum_subset hsub hzero
  have hcomp : (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      = (fun N => ∑ n ∈ Finset.range N, max (-f n) 0) ∘ negEnum f :=
    funext key
  rw [hcomp]
  exact htop.comp hq.tendsto_atTop

/-- One greedy step: take the next fresh nonnegative index if the partial sum is at
most `a`, otherwise the next fresh negative index. -/
private noncomputable def greedyStep (f : ℕ → ℝ) (a : ℝ) (t : ℕ × ℕ × ℝ) : ℕ × ℕ × ℝ :=
  if t.2.2 ≤ a then (t.1 + 1, t.2.1, t.2.2 + f (posEnum f t.1))
  else (t.1, t.2.1 + 1, t.2.2 + f (negEnum f t.2.1))

/-- Greedy state after `n` steps: consumed nonnegative count, consumed negative
count, and current partial sum. -/
private noncomputable def greedyState (f : ℕ → ℝ) (a : ℝ) : ℕ → ℕ × ℕ × ℝ
  | 0 => (0, 0, 0)
  | n + 1 => greedyStep f a (greedyState f a n)

/-- Number of nonnegative indices consumed after `n` steps. -/
private noncomputable def greedyPi (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  (greedyState f a n).1

/-- Number of negative indices consumed after `n` steps. -/
private noncomputable def greedyQj (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  (greedyState f a n).2.1

/-- Greedy partial sum after `n` steps. -/
private noncomputable def greedySum (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  (greedyState f a n).2.2

/-- Index chosen at step `n`. -/
private noncomputable def greedyIdx (f : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℕ :=
  if greedySum f a n ≤ a then posEnum f (greedyPi f a n)
  else negEnum f (greedyQj f a n)

private theorem greedyStep_pos (f : ℕ → ℝ) (a : ℝ) (t : ℕ × ℕ × ℝ) (h : t.2.2 ≤ a) :
    greedyStep f a t = (t.1 + 1, t.2.1, t.2.2 + f (posEnum f t.1)) := by
  unfold greedyStep
  rw [ite_eq_left h]

private theorem greedyStep_neg (f : ℕ → ℝ) (a : ℝ) (t : ℕ × ℕ × ℝ) (h : ¬ t.2.2 ≤ a) :
    greedyStep f a t = (t.1, t.2.1 + 1, t.2.2 + f (negEnum f t.2.1)) := by
  unfold greedyStep
  rw [ite_eq_right h]

private theorem greedyPi_succ_pos (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : greedySum f a n ≤ a) :
    greedyPi f a (n + 1) = greedyPi f a n + 1 := by
  simp only [greedyPi, greedyState]
  rw [greedyStep_pos f a _ h]

private theorem greedyPi_succ_neg (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : ¬ greedySum f a n ≤ a) :
    greedyPi f a (n + 1) = greedyPi f a n := by
  simp only [greedyPi, greedyState]
  rw [greedyStep_neg f a _ h]

private theorem greedyQj_succ_pos (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : greedySum f a n ≤ a) :
    greedyQj f a (n + 1) = greedyQj f a n := by
  simp only [greedyQj, greedyState]
  rw [greedyStep_pos f a _ h]

private theorem greedyQj_succ_neg (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : ¬ greedySum f a n ≤ a) :
    greedyQj f a (n + 1) = greedyQj f a n + 1 := by
  simp only [greedyQj, greedyState]
  rw [greedyStep_neg f a _ h]

private theorem greedySum_succ_pos (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : greedySum f a n ≤ a) :
    greedySum f a (n + 1) = greedySum f a n + f (posEnum f (greedyPi f a n)) := by
  simp only [greedySum, greedyPi, greedyState]
  rw [greedyStep_pos f a _ h]

private theorem greedySum_succ_neg (f : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (h : ¬ greedySum f a n ≤ a) :
    greedySum f a (n + 1) = greedySum f a n + f (negEnum f (greedyQj f a n)) := by
  simp only [greedySum, greedyQj, greedyState]
  rw [greedyStep_neg f a _ h]

private theorem greedyPi_mono_step (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    greedyPi f a n ≤ greedyPi f a (n + 1) := by
  by_cases h : greedySum f a n ≤ a
  · rw [greedyPi_succ_pos f a n h]
    exact Nat.le_succ _
  · rw [greedyPi_succ_neg f a n h]

private theorem greedyQj_mono_step (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    greedyQj f a n ≤ greedyQj f a (n + 1) := by
  by_cases h : greedySum f a n ≤ a
  · rw [greedyQj_succ_pos f a n h]
  · rw [greedyQj_succ_neg f a n h]
    exact Nat.le_succ _

private theorem greedyPi_monotone (f : ℕ → ℝ) (a : ℝ) : Monotone (greedyPi f a) :=
  monotone_nat_of_le_succ (greedyPi_mono_step f a)

private theorem greedyQj_monotone (f : ℕ → ℝ) (a : ℝ) : Monotone (greedyQj f a) :=
  monotone_nat_of_le_succ (greedyQj_mono_step f a)

private theorem greedyPi_le_succ (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    greedyPi f a (n + 1) ≤ greedyPi f a n + 1 := by
  by_cases h : greedySum f a n ≤ a
  · rw [greedyPi_succ_pos f a n h]
  · rw [greedyPi_succ_neg f a n h]
    exact Nat.le_succ _

private theorem greedyQj_le_succ (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    greedyQj f a (n + 1) ≤ greedyQj f a n + 1 := by
  by_cases h : greedySum f a n ≤ a
  · rw [greedyQj_succ_pos f a n h]
    exact Nat.le_succ _
  · rw [greedyQj_succ_neg f a n h]

private theorem greedyIdx_pos (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : greedySum f a n ≤ a) :
    greedyIdx f a n = posEnum f (greedyPi f a n) := by
  simp [greedyIdx, ite_eq_left h]

private theorem greedyIdx_neg (f : ℕ → ℝ) (a : ℝ) (n : ℕ) (h : ¬ greedySum f a n ≤ a) :
    greedyIdx f a n = negEnum f (greedyQj f a n) := by
  simp [greedyIdx, ite_eq_right h]

/-- The greedy partial sum equals the partial sum of the rearranged series. -/
private theorem greedy_sum_eq (f : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    greedySum f a n = ∑ m ∈ Finset.range n, f (greedyIdx f a m) := by
  induction n with
  | zero => simp [greedySum, greedyState]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : greedySum f a n ≤ a
    · have hs : greedySum f a (n + 1)
          = greedySum f a n + f (posEnum f (greedyPi f a n)) :=
        greedySum_succ_pos f a n h
      have he : greedyIdx f a n = posEnum f (greedyPi f a n) :=
        greedyIdx_pos f a n h
      rw [he, hs]
    · have hs : greedySum f a (n + 1)
          = greedySum f a n + f (negEnum f (greedyQj f a n)) :=
        greedySum_succ_neg f a n h
      have he : greedyIdx f a n = negEnum f (greedyQj f a n) :=
        greedyIdx_neg f a n h
      rw [he, hs]

/-- Positive steps occur arbitrarily far out: otherwise the tail would consist only of
negative steps and the partial sums would diverge to `-∞`, against the greedy rule. -/
private theorem greedy_posSteps_infinite (f : ℕ → ℝ) (a : ℝ)
    (hEneg : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop) :
    ∀ B : ℕ, ∃ n ≥ B, greedySum f a n ≤ a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  have hneg : ∀ n ≥ B, ¬ greedySum f a n ≤ a := fun n hn => not_le.mpr (hB n hn)
  have hqj : ∀ k : ℕ, greedyQj f a (B + k) = greedyQj f a B + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : B + (k + 1) = (B + k) + 1 := by omega
      rw [h1, greedyQj_succ_neg f a _ (hneg _ (by omega)), ih]
      omega
  have hS : ∀ k : ℕ, greedySum f a (B + k)
      = greedySum f a B
        + ∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a B + j)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : B + (k + 1) = (B + k) + 1 := by omega
      rw [h1, greedySum_succ_neg f a _ (hneg _ (by omega)), ih, hqj k,
        Finset.sum_range_succ]
      ring
  have hF : Filter.Tendsto (fun M => ∑ j ∈ Finset.range M, f (negEnum f j))
      Filter.atTop Filter.atBot := by
    have hFG : ∀ M : ℕ, (∑ j ∈ Finset.range M, f (negEnum f j))
        = -(∑ j ∈ Finset.range M, -f (negEnum f j)) := by
      intro M
      simp only [← Finset.sum_neg_distrib, neg_neg]
    have hfun : (fun M => ∑ j ∈ Finset.range M, f (negEnum f j))
        = fun M => -(∑ j ∈ Finset.range M, -f (negEnum f j)) := funext hFG
    rw [hfun]
    exact Filter.tendsto_neg_atTop_atBot.comp hEneg
  have htail_eq : ∀ k : ℕ,
      (∑ j ∈ Finset.range (greedyQj f a B + k), f (negEnum f j))
        = (∑ j ∈ Finset.range (greedyQj f a B), f (negEnum f j))
          + (∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a B + j))) :=
    fun k => Finset.sum_range_add _ _ _
  have hplus : Filter.Tendsto (fun k => greedyQj f a B + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b, fun k hk => by omega⟩
  have htail : Filter.Tendsto
      (fun k => ∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a B + j)))
      Filter.atTop Filter.atBot := by
    have hG : Filter.Tendsto
        (fun k => ∑ j ∈ Finset.range (greedyQj f a B + k), f (negEnum f j))
        Filter.atTop Filter.atBot := hF.comp hplus
    rw [Filter.tendsto_atBot] at hG ⊢
    intro b
    filter_upwards [hG ((∑ j ∈ Finset.range (greedyQj f a B), f (negEnum f j)) + b)]
      with k hk
    have hsplit := htail_eq k
    linarith
  have hSlim : Filter.Tendsto (fun k => greedySum f a (B + k))
      Filter.atTop Filter.atBot := by
    have hfun : (fun k => greedySum f a (B + k))
        = fun k => greedySum f a B
          + (∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a B + j))) :=
      funext hS
    rw [hfun]
    rw [Filter.tendsto_atBot] at htail ⊢
    intro b
    filter_upwards [htail (b - greedySum f a B)] with k hk
    linarith
  have hlt : ∀ᶠ k : ℕ in Filter.atTop, greedySum f a (B + k) < a :=
    hSlim.eventually (Filter.eventually_lt_atBot a)
  have hgt : ∀ᶠ k : ℕ in Filter.atTop, a < greedySum f a (B + k) := by
    rw [Filter.eventually_atTop]
    exact ⟨0, fun k _ => hB _ (by omega)⟩
  obtain ⟨k, hklt, hkgt⟩ := (hlt.and hgt).exists
  linarith

/-- Negative steps occur arbitrarily far out: otherwise the tail would consist only of
nonnegative steps and the partial sums would diverge to `+∞`, against the greedy rule. -/
private theorem greedy_negSteps_infinite (f : ℕ → ℝ) (a : ℝ)
    (hEpos : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop) :
    ∀ B : ℕ, ∃ n ≥ B, ¬ greedySum f a n ≤ a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  have hpi : ∀ k : ℕ, greedyPi f a (B + k) = greedyPi f a B + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : B + (k + 1) = (B + k) + 1 := by omega
      rw [h1, greedyPi_succ_pos f a _ (hB _ (by omega)), ih]
      omega
  have hS : ∀ k : ℕ, greedySum f a (B + k)
      = greedySum f a B
        + ∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a B + i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : B + (k + 1) = (B + k) + 1 := by omega
      rw [h1, greedySum_succ_pos f a _ (hB _ (by omega)), ih, hpi k,
        Finset.sum_range_succ]
      ring
  have htail_eq : ∀ k : ℕ,
      (∑ i ∈ Finset.range (greedyPi f a B + k), f (posEnum f i))
        = (∑ i ∈ Finset.range (greedyPi f a B), f (posEnum f i))
          + (∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a B + i))) :=
    fun k => Finset.sum_range_add _ _ _
  have hplus : Filter.Tendsto (fun k => greedyPi f a B + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b, fun k hk => by omega⟩
  have htail : Filter.Tendsto
      (fun k => ∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a B + i)))
      Filter.atTop Filter.atTop := by
    have hG : Filter.Tendsto
        (fun k => ∑ i ∈ Finset.range (greedyPi f a B + k), f (posEnum f i))
        Filter.atTop Filter.atTop := hEpos.comp hplus
    rw [Filter.tendsto_atTop] at hG ⊢
    intro b
    filter_upwards [hG ((∑ i ∈ Finset.range (greedyPi f a B), f (posEnum f i)) + b)]
      with k hk
    have hsplit := htail_eq k
    linarith
  have hSlim : Filter.Tendsto (fun k => greedySum f a (B + k))
      Filter.atTop Filter.atTop := by
    have hfun : (fun k => greedySum f a (B + k))
        = fun k => greedySum f a B
          + (∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a B + i))) :=
      funext hS
    rw [hfun]
    rw [Filter.tendsto_atTop] at htail ⊢
    intro b
    filter_upwards [htail (b - greedySum f a B)] with k hk
    linarith
  have hgt : ∀ᶠ k : ℕ in Filter.atTop, a < greedySum f a (B + k) :=
    hSlim.eventually (Filter.eventually_gt_atTop a)
  have hle : ∀ᶠ k : ℕ in Filter.atTop, greedySum f a (B + k) ≤ a := by
    rw [Filter.eventually_atTop]
    exact ⟨0, fun k _ => hB _ (by omega)⟩
  obtain ⟨k, hkgt, hkle⟩ := (hgt.and hle).exists
  linarith

/-- The nonnegative counter is unbounded: positive steps occur infinitely often, and each
one increments the counter. -/
private theorem greedyPi_tendsto (f : ℕ → ℝ) (a : ℝ)
    (hsteps : ∀ B : ℕ, ∃ n ≥ B, greedySum f a n ≤ a) :
    Filter.Tendsto (greedyPi f a) Filter.atTop Filter.atTop := by
  have hinf : (Set.ofPred fun n => greedySum f a n ≤ a).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨n, hnB, hnm⟩ := hsteps (B + 1)
    have hnmem : n ∈ Set.ofPred (fun n => greedySum f a n ≤ a) := hnm
    have hle : n ≤ B := hB hnmem
    omega
  have hnth_mem : ∀ j : ℕ,
      greedySum f a (Nat.nth (fun n => greedySum f a n ≤ a) j) ≤ a :=
    fun j => Nat.nth_mem_of_infinite hinf j
  have hnth_strict : StrictMono (Nat.nth (fun n => greedySum f a n ≤ a)) :=
    Nat.nth_strictMono hinf
  have hcount : ∀ j : ℕ,
      greedyPi f a (Nat.nth (fun n => greedySum f a n ≤ a) j + 1) ≥ j + 1 := by
    intro j
    induction j with
    | zero =>
      have hpos := greedyPi_succ_pos f a _ (hnth_mem 0)
      omega
    | succ j ih =>
      have hlt : Nat.nth (fun n => greedySum f a n ≤ a) j
          < Nat.nth (fun n => greedySum f a n ≤ a) (j + 1) :=
        hnth_strict (Nat.lt_succ_self j)
      have hle : Nat.nth (fun n => greedySum f a n ≤ a) j + 1
          ≤ Nat.nth (fun n => greedySum f a n ≤ a) (j + 1) := by omega
      have hpos := greedyPi_succ_pos f a _ (hnth_mem (j + 1))
      have hmono := (greedyPi_monotone f a) hle
      omega
  rw [Filter.tendsto_atTop]
  intro K
  rw [Filter.eventually_atTop]
  refine ⟨Nat.nth (fun n => greedySum f a n ≤ a) K + 1, fun n hn => ?_⟩
  have hK := hcount K
  have hmono := (greedyPi_monotone f a) hn
  omega

/-- The negative counter is unbounded. -/
private theorem greedyQj_tendsto (f : ℕ → ℝ) (a : ℝ)
    (hsteps : ∀ B : ℕ, ∃ n ≥ B, ¬ greedySum f a n ≤ a) :
    Filter.Tendsto (greedyQj f a) Filter.atTop Filter.atTop := by
  have hsteps' : ∀ B : ℕ, ∃ n ≥ B, a < greedySum f a n :=
    fun B => let ⟨n, hnB, hnm⟩ := hsteps B; ⟨n, hnB, not_le.mp hnm⟩
  have hinf : (Set.ofPred fun n => a < greedySum f a n).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨n, hnB, hnm⟩ := hsteps' (B + 1)
    have hnmem : n ∈ Set.ofPred (fun n => a < greedySum f a n) := hnm
    have hle : n ≤ B := hB hnmem
    omega
  have hnth_mem : ∀ j : ℕ,
      a < greedySum f a (Nat.nth (fun n => a < greedySum f a n) j) :=
    fun j => Nat.nth_mem_of_infinite hinf j
  have hnth_strict : StrictMono (Nat.nth (fun n => a < greedySum f a n)) :=
    Nat.nth_strictMono hinf
  have hcount : ∀ j : ℕ,
      greedyQj f a (Nat.nth (fun n => a < greedySum f a n) j + 1) ≥ j + 1 := by
    intro j
    induction j with
    | zero =>
      have hneg := greedyQj_succ_neg f a _ (not_le.mpr (hnth_mem 0))
      omega
    | succ j ih =>
      have hlt : Nat.nth (fun n => a < greedySum f a n) j
          < Nat.nth (fun n => a < greedySum f a n) (j + 1) :=
        hnth_strict (Nat.lt_succ_self j)
      have hle : Nat.nth (fun n => a < greedySum f a n) j + 1
          ≤ Nat.nth (fun n => a < greedySum f a n) (j + 1) := by omega
      have hneg := greedyQj_succ_neg f a _ (not_le.mpr (hnth_mem (j + 1)))
      have hmono := (greedyQj_monotone f a) hle
      omega
  rw [Filter.tendsto_atTop]
  intro K
  rw [Filter.eventually_atTop]
  refine ⟨Nat.nth (fun n => a < greedySum f a n) K + 1, fun n hn => ?_⟩
  have hK := hcount K
  have hmono := (greedyQj_monotone f a) hn
  omega

/-- If every step from `T` on is positive, the shifted partial sums diverge to `+∞`. -/
private theorem greedy_allPos_tail (f : ℕ → ℝ) (a : ℝ) (T : ℕ)
    (hall : ∀ m ≥ T, greedySum f a m ≤ a)
    (hEpos : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => greedySum f a (T + k)) Filter.atTop Filter.atTop := by
  have hpi : ∀ k : ℕ, greedyPi f a (T + k) = greedyPi f a T + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : T + (k + 1) = (T + k) + 1 := by omega
      rw [h1, greedyPi_succ_pos f a _ (hall _ (by omega)), ih]
      omega
  have hS : ∀ k : ℕ, greedySum f a (T + k)
      = greedySum f a T
        + ∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a T + i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : T + (k + 1) = (T + k) + 1 := by omega
      rw [h1, greedySum_succ_pos f a _ (hall _ (by omega)), ih, hpi k,
        Finset.sum_range_succ]
      ring
  have htail_eq : ∀ k : ℕ,
      (∑ i ∈ Finset.range (greedyPi f a T + k), f (posEnum f i))
        = (∑ i ∈ Finset.range (greedyPi f a T), f (posEnum f i))
          + (∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a T + i))) :=
    fun k => Finset.sum_range_add _ _ _
  have hplus : Filter.Tendsto (fun k => greedyPi f a T + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b, fun k hk => by omega⟩
  have htail : Filter.Tendsto
      (fun k => ∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a T + i)))
      Filter.atTop Filter.atTop := by
    have hG : Filter.Tendsto
        (fun k => ∑ i ∈ Finset.range (greedyPi f a T + k), f (posEnum f i))
        Filter.atTop Filter.atTop := hEpos.comp hplus
    rw [Filter.tendsto_atTop] at hG ⊢
    intro b
    filter_upwards [hG ((∑ i ∈ Finset.range (greedyPi f a T), f (posEnum f i)) + b)]
      with k hk
    have hsplit := htail_eq k
    linarith
  have hfun : (fun k => greedySum f a (T + k))
      = fun k => greedySum f a T
        + (∑ i ∈ Finset.range k, f (posEnum f (greedyPi f a T + i))) :=
    funext hS
  rw [hfun]
  rw [Filter.tendsto_atTop] at htail ⊢
  intro b
  filter_upwards [htail (b - greedySum f a T)] with k hk
  linarith

/-- If every step from `T` on is negative, the shifted partial sums diverge to `-∞`. -/
private theorem greedy_allNeg_tail (f : ℕ → ℝ) (a : ℝ) (T : ℕ)
    (hall : ∀ m ≥ T, ¬ greedySum f a m ≤ a)
    (hEneg : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => greedySum f a (T + k)) Filter.atTop Filter.atBot := by
  have hqj : ∀ k : ℕ, greedyQj f a (T + k) = greedyQj f a T + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : T + (k + 1) = (T + k) + 1 := by omega
      rw [h1, greedyQj_succ_neg f a _ (hall _ (by omega)), ih]
      omega
  have hS : ∀ k : ℕ, greedySum f a (T + k)
      = greedySum f a T
        + ∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a T + j)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : T + (k + 1) = (T + k) + 1 := by omega
      rw [h1, greedySum_succ_neg f a _ (hall _ (by omega)), ih, hqj k,
        Finset.sum_range_succ]
      ring
  have hF : Filter.Tendsto (fun M => ∑ j ∈ Finset.range M, f (negEnum f j))
      Filter.atTop Filter.atBot := by
    have hFG : ∀ M : ℕ, (∑ j ∈ Finset.range M, f (negEnum f j))
        = -(∑ j ∈ Finset.range M, -f (negEnum f j)) := by
      intro M
      simp only [← Finset.sum_neg_distrib, neg_neg]
    have hfun : (fun M => ∑ j ∈ Finset.range M, f (negEnum f j))
        = fun M => -(∑ j ∈ Finset.range M, -f (negEnum f j)) := funext hFG
    rw [hfun]
    exact Filter.tendsto_neg_atTop_atBot.comp hEneg
  have htail_eq : ∀ k : ℕ,
      (∑ j ∈ Finset.range (greedyQj f a T + k), f (negEnum f j))
        = (∑ j ∈ Finset.range (greedyQj f a T), f (negEnum f j))
          + (∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a T + j))) :=
    fun k => Finset.sum_range_add _ _ _
  have hplus : Filter.Tendsto (fun k => greedyQj f a T + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b, fun k hk => by omega⟩
  have htail : Filter.Tendsto
      (fun k => ∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a T + j)))
      Filter.atTop Filter.atBot := by
    have hG : Filter.Tendsto
        (fun k => ∑ j ∈ Finset.range (greedyQj f a T + k), f (negEnum f j))
        Filter.atTop Filter.atBot := hF.comp hplus
    rw [Filter.tendsto_atBot] at hG ⊢
    intro b
    filter_upwards [hG ((∑ j ∈ Finset.range (greedyQj f a T), f (negEnum f j)) + b)]
      with k hk
    have hsplit := htail_eq k
    linarith
  have hfun : (fun k => greedySum f a (T + k))
      = fun k => greedySum f a T
        + (∑ j ∈ Finset.range k, f (negEnum f (greedyQj f a T + j))) :=
    funext hS
  rw [hfun]
  rw [Filter.tendsto_atBot] at htail ⊢
  intro b
  filter_upwards [htail (b - greedySum f a T)] with k hk
  linarith

/-- The greedy index selection is injective: same-sign steps reuse no index (counters
strictly increase between same-sign steps), and the two enumerations are disjoint. -/
private theorem greedyIdx_injective (f : ℕ → ℝ) (a : ℝ)
    (hP : (Set.ofPred fun n => 0 ≤ f n).Infinite)
    (hQ : (Set.ofPred fun n => f n < 0).Infinite) :
    Function.Injective (greedyIdx f a) := by
  have hp : StrictMono (posEnum f) := Nat.nth_strictMono hP
  have hq : StrictMono (negEnum f) := Nat.nth_strictMono hQ
  have hmemP : ∀ i : ℕ, 0 ≤ f (posEnum f i) :=
    fun i => Nat.nth_mem_of_infinite hP i
  have hmemQ : ∀ j : ℕ, f (negEnum f j) < 0 :=
    fun j => Nat.nth_mem_of_infinite hQ j
  intro m1 m2 h
  by_cases h1 : greedySum f a m1 ≤ a <;> by_cases h2 : greedySum f a m2 ≤ a
  · rw [greedyIdx_pos f a m1 h1, greedyIdx_pos f a m2 h2] at h
    have hpi : greedyPi f a m1 = greedyPi f a m2 := hp.injective h
    rcases lt_trichotomy m1 m2 with hlt | heq | hgt
    · exfalso
      have hle : greedyPi f a (m1 + 1) ≤ greedyPi f a m2 :=
        (greedyPi_monotone f a) (by omega)
      have hstep := greedyPi_succ_pos f a m1 h1
      omega
    · exact heq
    · exfalso
      have hle : greedyPi f a (m2 + 1) ≤ greedyPi f a m1 :=
        (greedyPi_monotone f a) (by omega)
      have hstep := greedyPi_succ_pos f a m2 h2
      omega
  · rw [greedyIdx_pos f a m1 h1, greedyIdx_neg f a m2 h2] at h
    have h1' := hmemP (greedyPi f a m1)
    have h2' := hmemQ (greedyQj f a m2)
    rw [h] at h1'
    linarith
  · rw [greedyIdx_neg f a m1 h1, greedyIdx_pos f a m2 h2] at h
    have h1' := hmemQ (greedyQj f a m1)
    have h2' := hmemP (greedyPi f a m2)
    rw [h] at h1'
    linarith
  · rw [greedyIdx_neg f a m1 h1, greedyIdx_neg f a m2 h2] at h
    have hqj : greedyQj f a m1 = greedyQj f a m2 := hq.injective h
    rcases lt_trichotomy m1 m2 with hlt | heq | hgt
    · exfalso
      have hle : greedyQj f a (m1 + 1) ≤ greedyQj f a m2 :=
        (greedyQj_monotone f a) (by omega)
      have hstep := greedyQj_succ_neg f a m1 h1
      omega
    · exact heq
    · exfalso
      have hle : greedyQj f a (m2 + 1) ≤ greedyQj f a m1 :=
        (greedyQj_monotone f a) (by omega)
      have hstep := greedyQj_succ_neg f a m2 h2
      omega

/-- The greedy index selection is surjective: every nonnegative index is eventually taken
at a positive step (the counter hits every value), and symmetrically for negatives. -/
private theorem greedyIdx_surjective (f : ℕ → ℝ) (a : ℝ)
    (_hP : (Set.ofPred fun n => 0 ≤ f n).Infinite)
    (_hQ : (Set.ofPred fun n => f n < 0).Infinite)
    (hpi : Filter.Tendsto (greedyPi f a) Filter.atTop Filter.atTop)
    (hqj : Filter.Tendsto (greedyQj f a) Filter.atTop Filter.atTop) :
    Function.Surjective (greedyIdx f a) := by
  have hPnth : ∀ n : ℕ, 0 ≤ f n →
      Nat.nth (fun n => 0 ≤ f n) (Nat.count (fun n => 0 ≤ f n) n) = n :=
    fun n hn => Nat.nth_count hn
  have hQnth : ∀ n : ℕ, f n < 0 →
      Nat.nth (fun n => f n < 0) (Nat.count (fun n => f n < 0) n) = n :=
    fun n hn => Nat.nth_count hn
  have hpi0 : greedyPi f a 0 = 0 := by simp [greedyPi, greedyState]
  have hqj0 : greedyQj f a 0 = 0 := by simp [greedyQj, greedyState]
  intro n
  by_cases hPn : 0 ≤ f n
  · set i := Nat.count (fun n => 0 ≤ f n) n with hi_def
    have hpin : posEnum f i = n := hPnth n hPn
    have hex : ∃ M : ℕ, i + 1 ≤ greedyPi f a M := by
      rw [Filter.tendsto_atTop] at hpi
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hpi (i + 1))
      exact ⟨M, hM M le_rfl⟩
    obtain ⟨M, hM⟩ := hex
    have H : ∃ M : ℕ, i + 1 ≤ greedyPi f a M := ⟨M, hM⟩
    have hNspec : i + 1 ≤ greedyPi f a (Nat.find H) := Nat.find_spec H
    have hNpos : 1 ≤ Nat.find H := by
      by_contra hcon
      push Not at hcon
      have hN0 : Nat.find H = 0 := by omega
      rw [hN0, hpi0] at hNspec
      omega
    have hmin : greedyPi f a (Nat.find H - 1) ≤ i := by
      by_contra hcon
      push Not at hcon
      have hle := Nat.find_min' H (show i + 1 ≤ greedyPi f a (Nat.find H - 1) by omega)
      omega
    have hstep : greedyPi f a (Nat.find H)
        = greedyPi f a (Nat.find H - 1) + 1 := by
      have hle1 := greedyPi_le_succ f a (Nat.find H - 1)
      have hNM : Nat.find H - 1 + 1 = Nat.find H := by omega
      rw [hNM] at hle1
      have hmono := (greedyPi_monotone f a) (show Nat.find H - 1 ≤ Nat.find H by omega)
      omega
    have hpos : greedySum f a (Nat.find H - 1) ≤ a := by
      by_contra hcon
      have hsame := greedyPi_succ_neg f a _ hcon
      have hNM : Nat.find H - 1 + 1 = Nat.find H := by omega
      rw [hNM] at hsame
      omega
    have hpi_eq : greedyPi f a (Nat.find H - 1) = i := by omega
    refine ⟨Nat.find H - 1, ?_⟩
    have heq := greedyIdx_pos f a _ hpos
    rw [heq, hpi_eq]
    exact hpin
  · have hQn : f n < 0 := lt_of_not_ge hPn
    set j := Nat.count (fun n => f n < 0) n with hj_def
    have hqin : negEnum f j = n := hQnth n hQn
    have hex : ∃ M : ℕ, j + 1 ≤ greedyQj f a M := by
      rw [Filter.tendsto_atTop] at hqj
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hqj (j + 1))
      exact ⟨M, hM M le_rfl⟩
    obtain ⟨M, hM⟩ := hex
    have H : ∃ M : ℕ, j + 1 ≤ greedyQj f a M := ⟨M, hM⟩
    have hNspec : j + 1 ≤ greedyQj f a (Nat.find H) := Nat.find_spec H
    have hNpos : 1 ≤ Nat.find H := by
      by_contra hcon
      push Not at hcon
      have hN0 : Nat.find H = 0 := by omega
      rw [hN0, hqj0] at hNspec
      omega
    have hmin : greedyQj f a (Nat.find H - 1) ≤ j := by
      by_contra hcon
      push Not at hcon
      have hle := Nat.find_min' H (show j + 1 ≤ greedyQj f a (Nat.find H - 1) by omega)
      omega
    have hstep : greedyQj f a (Nat.find H)
        = greedyQj f a (Nat.find H - 1) + 1 := by
      have hle1 := greedyQj_le_succ f a (Nat.find H - 1)
      have hNM : Nat.find H - 1 + 1 = Nat.find H := by omega
      rw [hNM] at hle1
      have hmono := (greedyQj_monotone f a) (show Nat.find H - 1 ≤ Nat.find H by omega)
      omega
    have hnegstep : ¬ greedySum f a (Nat.find H - 1) ≤ a := by
      by_contra hcon
      have hsame := greedyQj_succ_pos f a _ hcon
      have hNM : Nat.find H - 1 + 1 = Nat.find H := by omega
      rw [hNM] at hsame
      omega
    have hqj_eq : greedyQj f a (Nat.find H - 1) = j := by omega
    refine ⟨Nat.find H - 1, ?_⟩
    have heq := greedyIdx_neg f a _ hnegstep
    rw [heq, hqj_eq]
    exact hqin

/-- Once the greedy sum is within `ε` of `a` at a point past `T` (where every remaining
term is `< ε` in absolute value), it stays within `ε` thereafter: each step moves the
sum toward `a` by less than `ε`, and can only overshoot by less than `ε`. -/
private theorem greedy_stable (f : ℕ → ℝ) (a : ℝ) (T M : ℕ) (ε : ℝ) (I J : ℕ)
    (hmemP : ∀ i : ℕ, 0 ≤ f (posEnum f i))
    (hmemQ : ∀ j : ℕ, f (negEnum f j) < 0)
    (hsmallP : ∀ i : ℕ, I ≤ i → |f (posEnum f i)| < ε)
    (hsmallQ : ∀ j : ℕ, J ≤ j → |f (negEnum f j)| < ε)
    (hcnt : ∀ n ≥ T, I ≤ greedyPi f a n ∧ J ≤ greedyQj f a n)
    (hMT : T ≤ M)
    (hclose : |greedySum f a M - a| < ε) :
    ∀ k : ℕ, |greedySum f a (M + k) - a| < ε := by
  intro k
  induction k with
  | zero =>
    simp only [add_zero]
    exact hclose
  | succ k ih =>
    have hmT : T ≤ M + k := by omega
    obtain ⟨hcI, hcJ⟩ := hcnt _ hmT
    have hid : M + (k + 1) = (M + k) + 1 := by omega
    rw [hid]
    have ihlo := (abs_lt.mp ih).1
    have ihhi := (abs_lt.mp ih).2
    by_cases hSk : greedySum f a (M + k) ≤ a
    · have hSeq := greedySum_succ_pos f a _ hSk
      rw [hSeq]
      have ht0 := hmemP (greedyPi f a (M + k))
      have htε := (abs_lt.mp (hsmallP _ hcI)).2
      rw [abs_lt]
      constructor <;> linarith
    · have hgt := lt_of_not_ge hSk
      have hSeq := greedySum_succ_neg f a _ hSk
      rw [hSeq]
      have ht0 := hmemQ (greedyQj f a (M + k))
      have htlo := (abs_lt.mp (hsmallQ _ hcJ)).1
      rw [abs_lt]
      constructor <;> linarith

/-- The greedy partial sums converge to `a`. Given `ε`, once both counters exceed the
point where all remaining terms are `< ε`, the divergent tails force the sum to cross
to within `ε` of `a`, and from there it never leaves. -/
private theorem greedy_tendsto (f : ℕ → ℝ) (a : ℝ)
    (hP : (Set.ofPred fun n => 0 ≤ f n).Infinite)
    (hQ : (Set.ofPred fun n => f n < 0).Infinite)
    (hEpos : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop)
    (hEneg : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop)
    (hf0p : Filter.Tendsto (fun i => f (posEnum f i)) Filter.atTop (nhds 0))
    (hf0q : Filter.Tendsto (fun j => f (negEnum f j)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (greedySum f a) Filter.atTop (nhds a) := by
  have hmemP : ∀ i : ℕ, 0 ≤ f (posEnum f i) :=
    fun i => Nat.nth_mem_of_infinite hP i
  have hmemQ : ∀ j : ℕ, f (negEnum f j) < 0 :=
    fun j => Nat.nth_mem_of_infinite hQ j
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmallP' : ∀ᶠ i : ℕ in Filter.atTop, f (posEnum f i) ∈ Metric.ball 0 ε :=
    hf0p (Metric.ball_mem_nhds 0 hε)
  have hsmallQ' : ∀ᶠ j : ℕ in Filter.atTop, f (negEnum f j) ∈ Metric.ball 0 ε :=
    hf0q (Metric.ball_mem_nhds 0 hε)
  obtain ⟨I, hI⟩ := Filter.eventually_atTop.mp hsmallP'
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hsmallQ'
  have hsmallP : ∀ i : ℕ, I ≤ i → |f (posEnum f i)| < ε := by
    intro i hi
    have hd := hI i hi
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hd
    exact hd
  have hsmallQ : ∀ j : ℕ, J ≤ j → |f (negEnum f j)| < ε := by
    intro j hj
    have hd := hJ j hj
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hd
    exact hd
  have hposSteps := greedy_posSteps_infinite f a hEneg
  have hnegSteps := greedy_negSteps_infinite f a hEpos
  have hpi := greedyPi_tendsto f a hposSteps
  have hqj := greedyQj_tendsto f a hnegSteps
  obtain ⟨N1, hN1⟩ :=
    Filter.eventually_atTop.mp (hpi.eventually (Filter.eventually_ge_atTop I))
  obtain ⟨N2, hN2⟩ :=
    Filter.eventually_atTop.mp (hqj.eventually (Filter.eventually_ge_atTop J))
  have hT : ∀ n ≥ max N1 N2, I ≤ greedyPi f a n ∧ J ≤ greedyQj f a n := by
    intro n hn
    have hn1 : N1 ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn2 : N2 ≤ n := le_trans (Nat.le_max_right _ _) hn
    exact ⟨le_trans (hN1 N1 le_rfl) ((greedyPi_monotone f a) hn1),
      le_trans (hN2 N2 le_rfl) ((greedyQj_monotone f a) hn2)⟩
  by_cases hST : greedySum f a (max N1 N2) ≤ a
  · have hcross : ∃ M : ℕ, a < greedySum f a (max N1 N2 + M) := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ m ≥ max N1 N2, greedySum f a m ≤ a := by
        intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, max N1 N2 + k = m := ⟨m - max N1 N2, by omega⟩
        exact hcon k
      have hlim := greedy_allPos_tail f a (max N1 N2) hall hEpos
      obtain ⟨k, hk⟩ :=
        (hlim.eventually (Filter.eventually_gt_atTop a)).exists
      have hle := hall (max N1 N2 + k) (by omega)
      linarith
    have H : ∃ M : ℕ, a < greedySum f a (max N1 N2 + M) := hcross
    have hM0spec : a < greedySum f a (max N1 N2 + Nat.find H) := Nat.find_spec H
    have hM0pos : 1 ≤ Nat.find H := by
      by_contra hcon
      push Not at hcon
      have hM00 : Nat.find H = 0 := by omega
      rw [hM00] at hM0spec
      simp only [add_zero] at hM0spec
      linarith
    have hprev : greedySum f a (max N1 N2 + (Nat.find H - 1)) ≤ a := by
      by_contra hcon
      have hlt : a < greedySum f a (max N1 N2 + (Nat.find H - 1)) :=
        lt_of_not_ge hcon
      have hle := Nat.find_min' H hlt
      omega
    have hstep_ge : max N1 N2 ≤ max N1 N2 + (Nat.find H - 1) := by omega
    obtain ⟨hcI, hcJ⟩ := hT _ hstep_ge
    have hSeq : greedySum f a (max N1 N2 + Nat.find H)
        = greedySum f a (max N1 N2 + (Nat.find H - 1))
          + f (posEnum f (greedyPi f a (max N1 N2 + (Nat.find H - 1)))) := by
      have h1 : max N1 N2 + Nat.find H = (max N1 N2 + (Nat.find H - 1)) + 1 := by
        omega
      rw [h1]
      exact greedySum_succ_pos f a _ hprev
    have hclose : |greedySum f a (max N1 N2 + Nat.find H) - a| < ε := by
      have hlt : greedySum f a (max N1 N2 + Nat.find H) < a + ε := by
        rw [hSeq]
        have htε := (abs_lt.mp (hsmallP _ hcI)).2
        linarith
      rw [abs_of_pos (by linarith : 0 < greedySum f a (max N1 N2 + Nat.find H) - a)]
      linarith
    have hMT : max N1 N2 ≤ max N1 N2 + Nat.find H := by omega
    have hmain := greedy_stable f a (max N1 N2) (max N1 N2 + Nat.find H) ε I J
      hmemP hmemQ hsmallP hsmallQ hT hMT hclose
    refine ⟨max N1 N2 + Nat.find H, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, max N1 N2 + Nat.find H + k = n :=
      ⟨n - (max N1 N2 + Nat.find H), by omega⟩
    rw [Real.dist_eq]
    exact hmain k
  · have hST' : a < greedySum f a (max N1 N2) := lt_of_not_ge hST
    have hcross : ∃ M : ℕ, greedySum f a (max N1 N2 + M) ≤ a := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ m ≥ max N1 N2, ¬ greedySum f a m ≤ a := by
        intro m hm
        obtain ⟨k, rfl⟩ : ∃ k, max N1 N2 + k = m := ⟨m - max N1 N2, by omega⟩
        exact not_le.mpr (hcon k)
      have hlim := greedy_allNeg_tail f a (max N1 N2) hall hEneg
      obtain ⟨k, hk⟩ :=
        (hlim.eventually (Filter.eventually_lt_atBot a)).exists
      have hle := hall (max N1 N2 + k) (by omega)
      exact hle (le_of_lt hk)
    have H : ∃ M : ℕ, greedySum f a (max N1 N2 + M) ≤ a := hcross
    have hM0spec : greedySum f a (max N1 N2 + Nat.find H) ≤ a := Nat.find_spec H
    have hM0pos : 1 ≤ Nat.find H := by
      by_contra hcon
      push Not at hcon
      have hM00 : Nat.find H = 0 := by omega
      rw [hM00] at hM0spec
      simp only [add_zero] at hM0spec
      linarith
    have hprev : a < greedySum f a (max N1 N2 + (Nat.find H - 1)) := by
      by_contra hcon
      have hle : greedySum f a (max N1 N2 + (Nat.find H - 1)) ≤ a :=
        le_of_not_gt hcon
      have hmin := Nat.find_min' H hle
      omega
    have hstep_ge : max N1 N2 ≤ max N1 N2 + (Nat.find H - 1) := by omega
    obtain ⟨hcI, hcJ⟩ := hT _ hstep_ge
    have hSeq : greedySum f a (max N1 N2 + Nat.find H)
        = greedySum f a (max N1 N2 + (Nat.find H - 1))
          + f (negEnum f (greedyQj f a (max N1 N2 + (Nat.find H - 1)))) := by
      have h1 : max N1 N2 + Nat.find H = (max N1 N2 + (Nat.find H - 1)) + 1 := by
        omega
      rw [h1]
      exact greedySum_succ_neg f a _ (not_le.mpr hprev)
    have hclose : |greedySum f a (max N1 N2 + Nat.find H) - a| < ε := by
      have hgt : a - ε < greedySum f a (max N1 N2 + Nat.find H) := by
        rw [hSeq]
        have htlo := (abs_lt.mp (hsmallQ _ hcJ)).1
        linarith
      have hle : greedySum f a (max N1 N2 + Nat.find H) - a ≤ 0 := by linarith
      rw [abs_of_nonpos hle]
      linarith
    have hMT : max N1 N2 ≤ max N1 N2 + Nat.find H := by omega
    have hmain := greedy_stable f a (max N1 N2) (max N1 N2 + Nat.find H) ε I J
      hmemP hmemQ hsmallP hsmallQ hT hMT hclose
    refine ⟨max N1 N2 + Nat.find H, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, max N1 N2 + Nat.find H + k = n :=
      ⟨n - (max N1 N2 + Nat.find H), by omega⟩
    rw [Real.dist_eq]
    exact hmain k

/--
**Riemann rearrangement theorem.** Let $f : \mathbb{N} \to \mathbb{R}$ be such that the series
$\sum_n f(n)$ converges in order to some real number, while the series $\sum_n |f(n)|$ is not
summable. Then for every $a \in \mathbb{R}$ there is a permutation $\sigma$ of $\mathbb{N}$ such
that the rearranged series $\sum_n f(\sigma(n))$ converges in order to $a$.

Source: B. Riemann, Über die Darstellbarkeit einer Function durch eine trigonometrische Reihe,
Habilitationsschrift (1854; published 1867).

Proves `Wanted` entry `riemann_rearrangement`.
-/
theorem riemann_rearrangement
    (f : ℕ → ℝ) (hf : ∃ s, OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) (a : ℝ) :
    ∃ e : Equiv.Perm ℕ, OrderedHasSum (fun n => f (e n)) a := by
  obtain ⟨s, hfs⟩ := hf
  -- Terms vanish; both signed parts diverge to +∞. The greedy construction takes the
  -- next fresh nonnegative index while the partial sum is at most `a`, else the next
  -- fresh negative index. Both counters run to infinity, every index is taken exactly
  -- once, and the partial sums converge to `a`.
  have hz : Filter.Tendsto f Filter.atTop (nhds 0) :=
    orderedHasSum_tendsto_zero f s hfs
  have hpos : ¬ Summable (fun n => max (f n) 0) := not_summable_pos_of f s hfs hfa
  have hneg : ¬ Summable (fun n => max (-f n) 0) := not_summable_neg_of f s hfs hfa
  have htop_pos : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (f n) 0)
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => le_max_right _ _)).mp hpos
  have htop_neg : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (-f n) 0)
      Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => le_max_right _ _)).mp hneg
  have hP : (Set.ofPred fun n => 0 ≤ f n).Infinite := posSet_infinite f s hfs hfa
  have hQ : (Set.ofPred fun n => f n < 0).Infinite := negSet_infinite f s hfs hfa
  have hEpos : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop := enum_pos_diverge f htop_pos hP
  have hEneg : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop := enum_neg_diverge f htop_neg hQ
  have hf0p : Filter.Tendsto (fun i => f (posEnum f i)) Filter.atTop (nhds 0) :=
    hz.comp (Nat.nth_strictMono hP).tendsto_atTop
  have hf0q : Filter.Tendsto (fun j => f (negEnum f j)) Filter.atTop (nhds 0) :=
    hz.comp (Nat.nth_strictMono hQ).tendsto_atTop
  have hinj : Function.Injective (greedyIdx f a) := greedyIdx_injective f a hP hQ
  have hposSteps := greedy_posSteps_infinite f a hEneg
  have hnegSteps := greedy_negSteps_infinite f a hEpos
  have hpi := greedyPi_tendsto f a hposSteps
  have hqj := greedyQj_tendsto f a hnegSteps
  have hsurj : Function.Surjective (greedyIdx f a) :=
    greedyIdx_surjective f a hP hQ hpi hqj
  have hbij : Function.Bijective (greedyIdx f a) := ⟨hinj, hsurj⟩
  refine ⟨Equiv.ofBijective (greedyIdx f a) hbij, ?_⟩
  have hS : Filter.Tendsto (greedySum f a) Filter.atTop (nhds a) :=
    greedy_tendsto f a hP hQ hEpos hEneg hf0p hf0q
  have hfun : (fun N => ∑ n ∈ Finset.range N,
        f ((Equiv.ofBijective (greedyIdx f a) hbij) n)) = greedySum f a := by
    funext N
    change (∑ n ∈ Finset.range N, f (greedyIdx f a n)) = greedySum f a N
    exact (greedy_sum_eq f a N).symm
  change Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
    f ((Equiv.ofBijective (greedyIdx f a) hbij) n)) Filter.atTop (nhds a)
  rw [hfun]
  exact hS

end MathlibExt.Analysis.Series.RiemannRearrangementWanted
