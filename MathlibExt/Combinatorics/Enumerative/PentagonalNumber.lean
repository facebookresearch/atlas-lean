/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas

@[expose] public section

open scoped BigOperators
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

/-- **The partition function.** For a natural number $n$, $p(n)$ is the number of partitions of
$n$, that is, of ways of writing $n$ as a sum of positive integers, disregarding order.

Source: https://en.wikipedia.org/wiki/Pentagonal_number_theorem
("Pentagonal number theorem", statement `pentagonal-s1`). -/
def partitionFunction (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- **The partition number of zero.** Let $p(n)$ be the number of partitions of $n$. Then
$p(0) = 1$: the only partition of $0$ is the empty one. -/
@[simp]
theorem partitionFunction_zero : partitionFunction 0 = 1 :=
  Fintype.card_unique

/-- **The partition number of one.** Let $p(n)$ be the number of partitions of $n$. Then
$p(1) = 1$: the only partition of $1$ is $1$ itself. -/
@[simp]
theorem partitionFunction_one : partitionFunction 1 = 1 :=
  Fintype.card_unique

private theorem pentagonal_zero : pentagonal 0 = 0 := by simp [pentagonal_def]

private theorem genFun_one_coeff (n : ℕ) :
    (Nat.Partition.genFun (fun _ _ => (1 : ℤ))).coeff n = ((partitionFunction n : ℕ) : ℤ) := by
  rw [Nat.Partition.coeff_genFun]
  simp only [Finsupp.prod_fun_one]
  unfold partitionFunction
  rw [Finset.sum_const, Finset.card_univ]
  simp

/-- **Partition generating function with unit weights.** Let $p(n)$ be the number of partitions
of $n$. Over the integers, $\sum_{n \ge 0} p(n)\, x^n$ equals the weighted partition generating
function $\sum_{n \ge 0} \sum_{\lambda} \prod_{i} f(i, c_i(\lambda))\, x^n$ with all weights
$f(i, c) = 1$, where $\lambda$ runs over the partitions of $n$, $i$ over the distinct parts of
$\lambda$, and $c_i(\lambda)$ is the number of times $i$ occurs in $\lambda$. -/
theorem mk_partitionFunction_eq_genFun :
    PowerSeries.mk (fun n => ((partitionFunction n : ℕ) : ℤ))
      = Nat.Partition.genFun (fun _ _ => (1 : ℤ)) := by
  ext n
  rw [genFun_one_coeff]
  simp

private theorem factor_rewrite (i : ℕ) :
    (1 : PowerSeries ℤ) +
        ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1)) =
      ∑' j : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j) := by
  have hs : Summable (fun j : ℕ => (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) := by
    have h : Summable (fun j : ℕ => ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) ^ j) := by
      apply PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
      simp
    simpa [pow_mul] using h
  have h2 := hs.tsum_eq_zero_add
  simp only [Nat.mul_zero, pow_zero] at h2
  rw [h2]
  congr 1
  apply tsum_congr
  intro j
  rw [one_smul]

private theorem factor_mul (i : ℕ) :
    (∑' j : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * j)) *
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) = 1 := by
  have h : (∑' j : ℕ, ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) ^ j) *
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) = 1 := by
    apply PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
    simp
  simpa [pow_mul] using h

/-- **Euler's identity for the partition generating function.** Let $p(n)$ be the number of
partitions of $n$. Over the integers,
$\left(\sum_{n \ge 0} p(n)\, x^n\right) \cdot \sum_{k \in \mathbb{Z}} (-1)^k x^{k(3k-1)/2} = 1$.
By the pentagonal number theorem the second factor equals $\prod_{i \ge 1} (1 - x^i)$. -/
theorem mk_partitionFunction_mul_pentagonalSeries :
    PowerSeries.mk (fun n => ((partitionFunction n : ℕ) : ℤ)) *
      PowerSeries.pentagonalSeries ℤ = 1 := by
  have hP : PowerSeries.mk (fun n => ((partitionFunction n : ℕ) : ℤ)) =
      ∏' i : ℕ, ((1 : PowerSeries ℤ) +
        ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) := by
    rw [mk_partitionFunction_eq_genFun]
    exact Nat.Partition.genFun_eq_tprod (fun _ _ => (1 : ℤ))
  have hS : PowerSeries.pentagonalSeries ℤ =
      ∏' i : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) :=
    (PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ).symm
  have hmult1 : Multipliable (fun i : ℕ => ((1 : PowerSeries ℤ) +
      ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1)))) :=
    (Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))).multipliable
  have hmult2 : Multipliable (fun i : ℕ => (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) :=
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ).multipliable
  have hterm : ∀ i : ℕ, ((1 : PowerSeries ℤ) +
      ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) *
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) = 1 := by
    intro i
    rw [factor_rewrite, factor_mul]
  have h1 : (∏' i : ℕ, ((1 : PowerSeries ℤ) +
      ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) *
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) = 1 := by
    rw [tprod_congr hterm, tprod_one]
  have hprod : (∏' i : ℕ, ((1 : PowerSeries ℤ) +
      ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1))) *
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) =
      (∏' i : ℕ, ((1 : PowerSeries ℤ) +
        ∑' j : ℕ, (1 : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ ((i + 1) * (j + 1)))) *
      (∏' i : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1))) :=
    Multipliable.tprod_mul hmult1 hmult2
  rw [hP, hS, ← hprod, h1]

private theorem filter_one_eq_erase (n : ℕ) :
    Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1))
      = (Finset.range (n + 1)).erase 0 := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  omega

private theorem filter_image_eq (p : ℤ → Prop) [DecidablePred p] (f : ℕ → ℤ) (s : Finset ℕ) :
    Finset.filter p (Finset.image f s) = Finset.image f (Finset.filter (fun m => p (f m)) s) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hpy⟩
    exact ⟨m, ⟨hm, hpy⟩, rfl⟩
  · rintro ⟨m, ⟨hm, hpfm⟩, rfl⟩
    exact ⟨⟨m, hm, rfl⟩, hpfm⟩

private theorem natAbs_le_pentagonal (j : ℤ) (hj : j ≠ 0) :
    (j.natAbs : ℤ) ≤ (pentagonal j : ℤ) := by
  have h2 := two_mul_natCast_pentagonal j
  rw [Int.natCast_natAbs]
  rcases lt_or_gt_of_ne hj with h | h
  · rw [abs_of_neg h]
    have h1 : (0 : ℤ) ≤ -j := by omega
    have h2' : (0 : ℤ) ≤ -3 * j - 1 := by omega
    nlinarith [mul_nonneg h1 h2', h2]
  · rw [abs_of_pos h]
    have h1 : (0 : ℤ) ≤ j := by omega
    have h2' : (0 : ℤ) ≤ 3 * j - 3 := by omega
    nlinarith [mul_nonneg h1 h2', h2]

private theorem mem_s0 (n : ℕ) (j : ℤ) (hj : pentagonal j ≤ n) :
    j ∈ (Finset.image (fun m : ℕ => (m : ℤ))
        (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
      ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1))) := by
  by_cases hj0 : j = 0
  · subst hj0
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), by simp⟩
  · have hle : j.natAbs ≤ n := by
      have h1 := natAbs_le_pentagonal j hj0
      have h2 : ((pentagonal j : ℕ) : ℤ) ≤ (n : ℕ) := by exact_mod_cast hj
      exact_mod_cast le_trans h1 h2
    have hm1 : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hj0
    have hmM : j.natAbs ∈ Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1)) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1⟩
    have hmR : j.natAbs ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    rcases le_total 0 j with hle0 | hle0
    · have hjm : ((j.natAbs : ℕ) : ℤ) = j := by
        rw [Int.natCast_natAbs, abs_of_nonneg hle0]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j.natAbs, hmM, hjm⟩
    · have hjm : ((j.natAbs : ℕ) : ℤ) = -j := by
        rw [Int.natCast_natAbs, abs_of_nonpos hle0]
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨j.natAbs, hmR, ?_⟩
      rw [hjm, neg_neg]

private theorem sum_range_conv (n : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 1), (PowerSeries.pentagonalSeries ℤ).coeff k * f k
      = ∑ j ∈ Finset.filter (fun j : ℤ => pentagonal j ≤ n)
          ((Finset.image (fun m : ℕ => (m : ℤ))
              (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
            ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1)))),
          ((j.negOnePow : ℤ) * f (pentagonal j)) := by
  have himg_sub : Finset.image pentagonal (Finset.filter (fun j : ℤ => pentagonal j ≤ n)
      ((Finset.image (fun m : ℕ => (m : ℤ)) (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
        ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1)))))
      ⊆ Finset.range (n + 1) := by
    intro k hk
    obtain ⟨j, hjf, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (by have h := (Finset.mem_filter.mp hjf).2; omega)
  have hvan : ∀ k ∈ Finset.range (n + 1),
      k ∉ Finset.image pentagonal (Finset.filter (fun j : ℤ => pentagonal j ≤ n)
        ((Finset.image (fun m : ℕ => (m : ℤ))
            (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
          ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1)))))
      → (PowerSeries.pentagonalSeries ℤ).coeff k * f k = 0 := by
    intro k hk hkm
    suffices h : (PowerSeries.pentagonalSeries ℤ).coeff k = 0 by rw [h, zero_mul]
    apply PowerSeries.coeff_pentagonalSeries_eq_zero
    rintro ⟨j, rfl⟩
    apply hkm
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply mem_s0
      have h : pentagonal j < n + 1 := Finset.mem_range.mp hk
      omega
    · have h : pentagonal j < n + 1 := Finset.mem_range.mp hk
      omega
  trans ∑ k ∈ Finset.image pentagonal (Finset.filter (fun j : ℤ => pentagonal j ≤ n)
      ((Finset.image (fun m : ℕ => (m : ℤ)) (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
        ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1))))),
      (PowerSeries.pentagonalSeries ℤ).coeff k * f k
  · exact (Finset.sum_subset himg_sub hvan).symm
  · rw [Finset.sum_image (fun _ _ _ _ h => pentagonal_injective h)]
    apply Finset.sum_congr rfl
    intro j _
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal]
    simp only [Int.cast_id]

private theorem sum_s0_split (n : ℕ) (F : ℤ → ℤ) :
    ∑ j ∈ Finset.filter (fun j : ℤ => pentagonal j ≤ n)
        ((Finset.image (fun m : ℕ => (m : ℤ))
            (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
          ∪ (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1)))),
        F j
    = (∑ m ∈ Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1)),
        (if pentagonal (m : ℤ) ≤ n then F (m : ℤ) else 0))
      + F 0
      + (∑ m ∈ Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1)),
        (if pentagonal (-(m : ℤ)) ≤ n then F (-(m : ℤ)) else 0)) := by
  have hdisj : Disjoint
      (Finset.image (fun m : ℕ => (m : ℤ)) (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))))
      (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1))) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨m, hmM, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨m', _, hm'⟩ := Finset.mem_image.mp hxB
    have hm1 : 1 ≤ m := (Finset.mem_filter.mp hmM).2
    omega
  have hdisjF : Disjoint
      (Finset.filter (fun j : ℤ => pentagonal j ≤ n)
        (Finset.image (fun m : ℕ => (m : ℤ))
            (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1)))))
      (Finset.filter (fun j : ℤ => pentagonal j ≤ n)
        (Finset.image (fun m : ℕ => (-(m : ℤ))) (Finset.range (n + 1)))) :=
    Finset.disjoint_left.mpr fun x hx1 hx2 =>
      Finset.disjoint_left.mp hdisj
        (Finset.mem_of_subset (Finset.filter_subset _ _) hx1)
        (Finset.mem_of_subset (Finset.filter_subset _ _) hx2)
  rw [Finset.filter_union, Finset.sum_union hdisjF,
    filter_image_eq (fun j : ℤ => pentagonal j ≤ n) (fun m : ℕ => (m : ℤ)),
    filter_image_eq (fun j : ℤ => pentagonal j ≤ n) (fun m : ℕ => (-(m : ℤ)))]
  rw [Finset.sum_image (fun _ _ _ _ h => Nat.cast_injective h),
    Finset.sum_image (fun _ _ _ _ h => Nat.cast_injective (neg_injective h)),
    ← Finset.sum_filter, ← Finset.sum_filter]
  have hq0 : pentagonal (-(((0 : ℕ)) : ℤ)) ≤ n := by simp [pentagonal_zero]
  have h0 : (0 : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ n)
  have h0mem :
      (0 : ℕ) ∈ Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n) (Finset.range (n + 1)) :=
    Finset.mem_filter.mpr ⟨h0, hq0⟩
  have he : F (-(((0 : ℕ)) : ℤ))
      + ∑ x ∈ (Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n)
          (Finset.range (n + 1))).erase 0,
        F (-(x : ℤ))
      = ∑ x ∈ Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n) (Finset.range (n + 1)),
        F (-(x : ℤ)) :=
    Finset.add_sum_erase _ (fun x : ℕ => F (-(x : ℤ))) h0mem
  have herase1 :
      (Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n) (Finset.range (n + 1))).erase 0
      = Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n)
        ((Finset.range (n + 1)).erase 0) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  have herase2 :
      Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n) ((Finset.range (n + 1)).erase 0)
      = Finset.filter (fun m : ℕ => pentagonal (-(m : ℤ)) ≤ n)
        (Finset.filter (fun m => 1 ≤ m) (Finset.range (n + 1))) := by
    rw [filter_one_eq_erase n]
  have hG0 : F (-(((0 : ℕ)) : ℤ)) = F 0 := by simp
  rw [← he, herase1, herase2, hG0]
  rw [add_assoc]

private theorem reflect_help (n : ℕ) (S P : ℕ → ℤ) :
    (∑ k ∈ Finset.range (n + 1), S (n - k) * P k)
      = (∑ k ∈ Finset.range (n + 1), S k * P (n - k)) := by
  have hr := Finset.sum_range_reflect (fun j => S j * P (n - j)) (n + 1)
  beta_reduce at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : k < n + 1 := Finset.mem_range.mp hk
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n + 1 - 1 - k) = k := by omega
  rw [e2, e1]

private theorem coeff_conv (n : ℕ) :
    (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ)) *
      PowerSeries.pentagonalSeries ℤ).coeff n
    = ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.pentagonalSeries ℤ).coeff k
          * (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ))).coeff (n - k) := by
  have h1 : (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ)) *
        PowerSeries.pentagonalSeries ℤ).coeff n
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.pentagonalSeries ℤ).coeff ij.2
          * (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ))).coeff ij.1 := by
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij _
    rw [mul_comm]
  have h2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (PowerSeries.pentagonalSeries ℤ).coeff b
      * (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ))).coeff a) n
  have h3 : Finset.range n.succ = Finset.range (n + 1) := by
    congr 1
  rw [h1]
  rw [h3] at h2
  exact h2.trans (reflect_help n (fun k => (PowerSeries.pentagonalSeries ℤ).coeff k)
    (fun k => (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ))).coeff k))

private theorem pow_neg_one_succ (m : ℕ) (X : ℤ) :
    (-1 : ℤ) ^ (m + 1) * X = -((m : ℤ).negOnePow * X) := by
  have hnegpow : (m : ℤ).negOnePow = (-1 : ℤ) ^ m := Int.coe_negOnePow_natCast m
  rw [pow_succ, ← hnegpow, mul_neg, mul_one, neg_mul]

private theorem negOnePow_neg_coe (m : ℕ) :
    ((-(m : ℤ)).negOnePow : ℤ) = ((m : ℤ).negOnePow : ℤ) := by
  rw [Int.negOnePow_neg]

/-- **Euler's pentagonal recurrence for the partition function.** Let $p(n)$ be the number of
partitions of $n$, and for an integer $k$ let $g(k) = k(3k - 1)/2$ be the generalized pentagonal
number of $k$. For every natural number $n \ge 1$,
$p(n) = \sum_{k} (-1)^{k+1}\, p(n - g(k))$, where the sum runs over the nonzero integers $k$
with $g(k) \le n$.

Proves `Wanted` entry `pentagonal_number_theorem`.

Source: https://en.wikipedia.org/wiki/Pentagonal_number_theorem
("Pentagonal number theorem", statement `pentagonal-s1`). -/
theorem pentagonal_number_theorem (n : ℕ) (hn : 1 ≤ n) :
    (partitionFunction n : ℤ) =
      ∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1) *
          (if pentagonal (m : ℤ) ≤ n
            then (partitionFunction (n - pentagonal (m : ℤ)) : ℤ)
            else 0)) +
          ((-1 : ℤ) ^ (m + 1) *
            (if pentagonal (-(m : ℤ)) ≤ n
              then (partitionFunction (n - pentagonal (-(m : ℤ))) : ℤ)
              else 0))) := by
  have hprod := mk_partitionFunction_mul_pentagonalSeries
  have h0 : (PowerSeries.mk (fun j => ((partitionFunction j : ℕ) : ℤ)) *
      PowerSeries.pentagonalSeries ℤ).coeff n = 0 := by
    rw [hprod, PowerSeries.coeff_one, ite_eq_right (by omega)]
  rw [coeff_conv] at h0
  simp only [PowerSeries.coeff_mk] at h0
  have e2 := sum_range_conv n (fun l => ((partitionFunction (n - l) : ℕ) : ℤ))
  have e3 := sum_s0_split n
    (fun j => ((j.negOnePow : ℤ)) * ((partitionFunction (n - pentagonal j) : ℕ) : ℤ))
  beta_reduce at e2
  rw [e2, e3] at h0
  have hF0 : (((0:ℤ).negOnePow : ℤ)) * ((partitionFunction (n - pentagonal 0) : ℕ) : ℤ)
      = ((partitionFunction n : ℕ) : ℤ) := by
    rw [pentagonal_zero, Nat.sub_zero, Int.negOnePow_zero]
    simp
  have hAeq : (∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1)) *
          (if pentagonal (m : ℤ) ≤ n
            then (partitionFunction (n - pentagonal (m : ℤ)) : ℤ)
            else 0)))
      = -(∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (if pentagonal (m : ℤ) ≤ n
          then (((m : ℤ).negOnePow : ℤ)) * ((partitionFunction (n - pentagonal (m : ℤ)) : ℕ) : ℤ)
          else 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : pentagonal (m : ℤ) ≤ n
    · rw [ite_eq_left h, ite_eq_left h, pow_neg_one_succ]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, neg_zero]
  have hBeq : (∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1)) *
          (if pentagonal (-(m : ℤ)) ≤ n
            then (partitionFunction (n - pentagonal (-(m : ℤ))) : ℤ)
            else 0)))
      = -(∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (if pentagonal (-(m : ℤ)) ≤ n
          then (((-(m : ℤ)).negOnePow : ℤ)) *
              ((partitionFunction (n - pentagonal (-(m : ℤ))) : ℕ) : ℤ)
          else 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : pentagonal (-(m : ℤ)) ≤ n
    · rw [ite_eq_left h, ite_eq_left h, pow_neg_one_succ, negOnePow_neg_coe]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero, neg_zero]
  have hRHS : ∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1) *
          (if pentagonal (m : ℤ) ≤ n
            then (partitionFunction (n - pentagonal (m : ℤ)) : ℤ)
            else 0)) +
          ((-1 : ℤ) ^ (m + 1) *
            (if pentagonal (-(m : ℤ)) ≤ n
              then (partitionFunction (n - pentagonal (-(m : ℤ))) : ℤ)
              else 0)))
      = (∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1)) *
          (if pentagonal (m : ℤ) ≤ n
            then (partitionFunction (n - pentagonal (m : ℤ)) : ℤ)
            else 0)))
        + (∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
        (((-1 : ℤ) ^ (m + 1)) *
          (if pentagonal (-(m : ℤ)) ≤ n
            then (partitionFunction (n - pentagonal (-(m : ℤ))) : ℤ)
            else 0))) :=
    Finset.sum_add_distrib
  rw [hRHS, hAeq, hBeq]
  omega

end MetaMathlibExt
