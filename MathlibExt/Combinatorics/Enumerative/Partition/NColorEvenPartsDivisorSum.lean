/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.StanleyElderParts
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The even-divisor sum for parts of n-color partitions

We count occurrences of an even-sized colored part by removing a positive number of copies
of that part. Grouping by the size removed then gives the even-divisor sum.

## References

* Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
  [INTEGERS 25 (2025), Article A94](https://math.colgate.edu/~integers/z94/z94.pdf),
  pp. 1–11, Corollary 3 (p. 6). The paper uses generating functions; we give a finite
  counting proof.
-/

namespace MetaMathlibExt

open Finset

private def evenColoredPartsUpTo (m : ℕ) : Finset (ℕ × ℕ) :=
  (nColorPartsUpTo m).toFinset.filter fun p => Even p.1

private lemma mem_evenColoredPartsUpTo {m : ℕ} {p : ℕ × ℕ} :
    p ∈ evenColoredPartsUpTo m ↔ (1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ m) ∧ Even p.1 := by
  simp only [evenColoredPartsUpTo, mem_filter, List.mem_toFinset, mem_nColorPartsUpTo]

private lemma size_add_replicate (s : Multiset (ℕ × ℕ)) (q : ℕ) (p : ℕ × ℕ) :
    ((s + Multiset.replicate q p).map Prod.fst).sum = (s.map Prod.fst).sum + q * p.1 := by
  simp [Multiset.map_replicate, Multiset.sum_replicate]

private lemma card_count_ge {m q : ℕ} {p : ℕ × ℕ} (hc : 1 ≤ p.2 ∧ p.2 ≤ p.1)
    (hqm : q * p.1 ≤ m) :
    ((nColorPartitions m).filter fun s => q ≤ s.count p).card =
      (nColorPartitions (m - q * p.1)).card := by
  refine card_nbij' (fun s => s - Multiset.replicate q p)
    (fun s => s + Multiset.replicate q p) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs, hq⟩ := mem_filter.mp hs
    obtain ⟨hcolors, hsize⟩ := (mem_nColorPartitions m s).mp hs
    have hrep := Multiset.le_count_iff_replicate_le.mp hq
    refine (mem_nColorPartitions _ _).mpr ⟨?_, ?_⟩
    · exact fun x hx => hcolors x (Multiset.mem_of_le (Multiset.sub_le_self ..) hx)
    · change ((s - Multiset.replicate q p).map Prod.fst).sum = m - q * p.1
      have h := size_add_replicate (s - Multiset.replicate q p) q p
      rw [Multiset.sub_add_cancel hrep, hsize] at h
      omega
  · intro s hs
    obtain ⟨hcolors, hsize⟩ := (mem_nColorPartitions _ _).mp hs
    refine mem_filter.mpr ⟨(mem_nColorPartitions _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact hcolors x hx
      · rwa [Multiset.eq_of_mem_replicate hx]
    · rw [size_add_replicate, hsize, Nat.sub_add_cancel hqm]
    · exact Multiset.le_count_iff_replicate_le.mpr (Multiset.le_add_left _ _)
  · intro s hs
    exact Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp (mem_filter.mp hs).2)
  · intro s _
    exact Multiset.add_sub_cancel_right

private lemma card_evenParts_eq_sum_layers {m : ℕ} {s : Multiset (ℕ × ℕ)}
    (hs : s ∈ nColorPartitions m) :
    (s.filter fun p => Even p.1).card =
      ∑ p ∈ evenColoredPartsUpTo m, ((Icc 1 (m / p.1)).filter fun q => q ≤ s.count p).card := by
  obtain ⟨hcolors, hsize⟩ := (mem_nColorPartitions m s).mp hs
  have hpalette : ∀ p ∈ s.filter (fun p => Even p.1), p ∈ evenColoredPartsUpTo m := by
    intro p hp
    obtain ⟨hps, heven⟩ := Multiset.mem_filter.mp hp
    have hp_le : p.1 ≤ m := by
      rw [← hsize]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hps)
    exact mem_evenColoredPartsUpTo.mpr ⟨⟨(hcolors p hps).1, (hcolors p hps).2, hp_le⟩, heven⟩
  rw [← Multiset.sum_count_eq_card hpalette]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨⟨hc, hcd, _⟩, heven⟩ := mem_evenColoredPartsUpTo.mp hp
  rw [Multiset.count_filter_of_pos (p := fun p : ℕ × ℕ => Even p.1) heven]
  -- The weight of all copies of `p` is at most the weight of the partition.
  have hbound : s.count p ≤ m / p.1 := by
    have hp_pos := hc.trans hcd
    have h := size_add_replicate (s - Multiset.replicate (s.count p) p) (s.count p) p
    rw [Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp le_rfl), hsize] at h
    exact (Nat.le_div_iff_mul_le hp_pos).mpr (by omega)
  have hlayers : (Icc 1 (m / p.1)).filter (fun q => q ≤ s.count p) = Icc 1 (s.count p) := by
    ext q
    simp only [mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hbound⟩, h.2⟩⟩
  rw [hlayers, Nat.card_Icc, Nat.add_sub_cancel]

-- A colored part `(d, j)` and a copy count `q` correspond to `(q * d, d, j)`.
private lemma sum_by_even_divisors (m : ℕ) (f : ℕ → ℕ) :
    ∑ p ∈ evenColoredPartsUpTo m, ∑ q ∈ Icc 1 (m / p.1), f (q * p.1) =
      ∑ k ∈ Icc 1 m, sigmaEven k * f k := by
  calc
    _ = ∑ a ∈ (evenColoredPartsUpTo m).sigma (fun p => Icc 1 (m / p.1)),
          f (a.2 * a.1.1) := (sum_sigma ..).symm
    _ = ∑ b ∈ (Icc 1 m).sigma (fun k => (k.divisors.filter Even).sigma (Icc 1)), f b.1 := by
      refine sum_nbij' (fun a => ⟨a.2 * a.1.1, a.1.1, a.1.2⟩)
        (fun b => ⟨(b.2.1, b.2.2), b.1 / b.2.1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · rintro ⟨p, q⟩ ha
        obtain ⟨hp, hq⟩ := mem_sigma.mp ha
        obtain ⟨⟨hc, hcd, _⟩, heven⟩ := mem_evenColoredPartsUpTo.mp hp
        obtain ⟨hq_pos, hq_le⟩ := mem_Icc.mp hq
        have hd := hc.trans hcd
        have hk := Nat.mul_pos hq_pos hd
        exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hk, (Nat.le_div_iff_mul_le hd).mp hq_le⟩,
          mem_sigma.mpr ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, hk.ne'⟩, heven⟩,
            mem_Icc.mpr ⟨hc, hcd⟩⟩⟩
      · rintro ⟨k, d, j⟩ hb
        obtain ⟨hk, hj⟩ := mem_sigma.mp hb
        obtain ⟨hd, hj⟩ := mem_sigma.mp hj
        obtain ⟨hdiv, heven⟩ := mem_filter.mp hd
        have hd_pos := Nat.pos_of_mem_divisors hdiv
        have hdk := Nat.divisor_le hdiv
        exact mem_sigma.mpr ⟨mem_evenColoredPartsUpTo.mpr
          ⟨⟨(mem_Icc.mp hj).1, (mem_Icc.mp hj).2, hdk.trans (mem_Icc.mp hk).2⟩, heven⟩,
          mem_Icc.mpr ⟨Nat.div_pos hdk hd_pos, Nat.div_le_div_right (mem_Icc.mp hk).2⟩⟩
      · rintro ⟨p, q⟩ ha
        obtain ⟨⟨hc, hcd, _⟩, _⟩ := mem_evenColoredPartsUpTo.mp (mem_sigma.mp ha).1
        simp [Nat.mul_div_cancel _ (hc.trans hcd)]
      · rintro ⟨k, d, j⟩ hb
        have hdiv := (mem_filter.mp (mem_sigma.mp (mem_sigma.mp hb).2).1).1
        simp [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hdiv)]
    _ = _ := by
      simp_rw [sum_sigma, sum_const, Nat.card_Icc, Nat.add_sub_cancel, Nat.nsmul_eq_mul,
        sigmaEven, sum_mul]

/-- **Even divisor sums count the even parts of $n$-color partitions.** For $m \ge 1$, let
$A_e(m)$ be the total number of parts of even size, counted with multiplicity, over the
$n$-color partitions of $m$, and for $r \ge 0$ let $C(r)$ be the number of $n$-color partitions
of $r$. Then
$$A_e(m) = \sum_{k=1}^{m} \sigma_{\mathrm{even}}(k) \, C(m - k),$$
where $\sigma_{\mathrm{even}}(k)$ is the sum of the even divisors of $k$.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`integers-2025-A94-cor-3`). -/
public theorem nColor_evenParts_eq_sum_sigmaEven (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Even p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaEven k * (nColorPartitions (m - k)).card := by
  by_cases hzero : m = 0
  · exact (ne_of_gt hm hzero).elim
  calc
    _ = ∑ s ∈ nColorPartitions m, ∑ p ∈ evenColoredPartsUpTo m,
          ∑ q ∈ Icc 1 (m / p.1), if q ≤ s.count p then 1 else 0 := by
      refine sum_congr rfl fun s hs => ?_
      simp only [card_evenParts_eq_sum_layers hs, card_eq_sum_ones, sum_filter]
    _ = ∑ p ∈ evenColoredPartsUpTo m, ∑ q ∈ Icc 1 (m / p.1),
          ((nColorPartitions m).filter fun s => q ≤ s.count p).card := by
      rw [sum_comm]
      refine sum_congr rfl fun p _ => ?_
      simp only [card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ = ∑ p ∈ evenColoredPartsUpTo m, ∑ q ∈ Icc 1 (m / p.1),
          (nColorPartitions (m - q * p.1)).card := by
      refine sum_congr rfl fun p hp => sum_congr rfl fun q hq => ?_
      obtain ⟨⟨hc, hcd, _⟩, _⟩ := mem_evenColoredPartsUpTo.mp hp
      exact card_count_ge ⟨hc, hcd⟩ ((Nat.le_div_iff_mul_le (hc.trans hcd)).mp (mem_Icc.mp hq).2)
    _ = _ := sum_by_even_divisors m fun k => (nColorPartitions (m - k)).card

end MetaMathlibExt
