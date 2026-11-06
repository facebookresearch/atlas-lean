/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Two-associated Stirling numbers of the second kind

This file defines the two-associated Stirling numbers of the second kind and proves their
recurrence and support bound.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **2-associated Stirling numbers of the second kind.** For natural numbers $n$ and $k$, the
2-associated Stirling number of the second kind is the integer
$S_2(n, k) = \sum_{j=0}^{k} (-1)^j \binom{n}{j} S(n - j, k - j)$, where $S$ denotes the
Stirling numbers of the second kind.

By inclusion and exclusion over singleton blocks, $S_2(n, k)$ is the number of partitions of an
$n$-element set into $k$ blocks, each containing at least two elements. -/
def twoAssocStirlingSecond (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (Nat.choose n j : ℤ) *
      (Nat.stirlingSecond (n - j) (k - j) : ℤ)

private lemma twoAssoc_succ_zero (n : ℕ) :
    twoAssocStirlingSecond (n + 1) 0 = 0 := by
  simp only [twoAssocStirlingSecond]
  simp

private lemma twoAssoc_eq_zero_of_lt (n k : ℕ) (h : n < k) :
    twoAssocStirlingSecond n k = 0 := by
  simp only [twoAssocStirlingSecond]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.mem_range] at hu
  by_cases hnu : n < u
  · have hC : Nat.choose n u = 0 :=
      Nat.choose_eq_zero_of_lt hnu
    simp [hC]
  · push Not at hnu
    have hS : Nat.stirlingSecond (n - u) (k - u) = 0 := by
      apply Nat.stirlingSecond_eq_zero_of_lt
      omega
    simp [hS]

private lemma twoAssoc_self (n : ℕ) (hn : n ≠ 0) :
    twoAssocStirlingSecond n n = 0 := by
  simpa only [twoAssocStirlingSecond, Nat.stirlingSecond_self,
    Nat.cast_one, mul_one] using
    Int.alternating_sum_range_choose_of_ne hn

private lemma pascal_succ_aux (m u : ℕ) (hu : 1 ≤ u) :
    Nat.choose (m + 2) u
      = Nat.choose (m + 1) u + Nat.choose (m + 1) (u - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h : m + 2 = (m + 1) + 1 := by omega
  rw [h, Nat.choose_succ_succ]
  exact add_comm _ _

private lemma choose_mul_aux (m u : ℕ) (hu : 1 ≤ u) :
    u * Nat.choose (m + 1) u = (m + 1) * Nat.choose m (u - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq m v
  exact (mul_comm _ _).trans h.symm

/-- **Recurrence for 2-associated Stirling numbers of the second kind.** Write $S_2(n, k)$ for
the 2-associated Stirling number of the second kind. For natural numbers $m$ and $k$ with
$1 \le k \le m$, we have $S_2(m + 2, k) = k \, S_2(m + 1, k) + (m + 1) \, S_2(m, k - 1)$. -/
theorem twoAssocStirlingSecond_recurrence (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    twoAssocStirlingSecond (m + 2) k =
      (k : ℤ) * twoAssocStirlingSecond (m + 1) k +
        (m + 1 : ℤ) * twoAssocStirlingSecond m (k - 1) := by
  have hpascal :
      (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 2) u : ℤ) *
          (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)) =
        (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
          (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)) +
        ∑ v ∈ Finset.range k, ((-1 : ℤ) ^ (v + 1)) * (Nat.choose (m + 1) v : ℤ) *
          (Nat.stirlingSecond (m + 1 - v) (k - 1 - v) : ℤ) := by
    let f : ℕ → ℤ := fun u => (-1) ^ u * (Nat.choose (m + 2) u : ℤ) *
      (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)
    let g : ℕ → ℤ := fun u => (-1) ^ u * (Nat.choose (m + 1) u : ℤ) *
      (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)
    let q : ℕ → ℤ := fun v => (-1) ^ (v + 1) * (Nat.choose (m + 1) v : ℤ) *
      (Nat.stirlingSecond (m + 1 - v) (k - 1 - v) : ℤ)
    have hzero : f 0 = g 0 := by simp [f, g]
    have htail : ∀ v < k, f (v + 1) = g (v + 1) + q v := by
      intro v hv
      have hv1 : 1 ≤ v + 1 := by omega
      simp only [f, g, q]
      rw [pascal_succ_aux m (v + 1) hv1]
      push_cast
      have hsub1 : m + 2 - (v + 1) = m + 1 - v := by omega
      have hsub2 : k - (v + 1) = k - 1 - v := by omega
      rw [hsub2]
      ring
    change (∑ u ∈ Finset.range (k + 1), f u) =
      (∑ u ∈ Finset.range (k + 1), g u) + ∑ v ∈ Finset.range k, q v
    calc
      _ = f 0 + ∑ v ∈ Finset.range k, f (v + 1) := by
        rw [Finset.sum_range_succ']
        ring
      _ = g 0 + ∑ v ∈ Finset.range k, (g (v + 1) + q v) := by
        rw [hzero]
        apply congrArg (g 0 + ·)
        apply Finset.sum_congr rfl
        intro v hv
        exact htail v (Finset.mem_range.mp hv)
      _ = (g 0 + ∑ v ∈ Finset.range k, g (v + 1)) +
          ∑ v ∈ Finset.range k, q v := by
        rw [Finset.sum_add_distrib]
        ring
      _ = _ := by
        rw [Finset.sum_range_succ']
        ring
  have hstirling : ∀ u < k + 1,
      Nat.stirlingSecond (m + 2 - u) (k - u) =
        (k - u) * Nat.stirlingSecond (m + 1 - u) (k - u) +
          Nat.stirlingSecond (m + 1 - u) (k - u - 1) := by
    intro u hu
    by_cases huk : u = k
    · subst u
      have hpos : 0 < m + 1 - k := by omega
      have hpos' : 0 < m + 2 - k := by omega
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos')
      simp only [Nat.sub_self, Nat.zero_sub, zero_mul]
      rw [ha, hb, Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_succ_zero]
    · have huklt : u < k := by omega
      have hpos : 0 < k - u := by omega
      have hfirst : m + 2 - u = (m + 1 - u) + 1 := by omega
      rw [hfirst, Nat.stirlingSecond_succ_left _ _ (Nat.ne_of_gt hpos)]
  have hI :
      (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
          (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)) =
        (k : ℤ) * twoAssocStirlingSecond (m + 1) k +
          (m + 1 : ℤ) * twoAssocStirlingSecond m (k - 1) +
            twoAssocStirlingSecond (m + 1) (k - 1) := by
    have hexpand :
        (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
            (Nat.stirlingSecond (m + 2 - u) (k - u) : ℤ)) =
          (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
            ((k - u : ℕ) : ℤ) * (Nat.stirlingSecond (m + 1 - u) (k - u) : ℤ)) +
          ∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
            (Nat.stirlingSecond (m + 1 - u) (k - u - 1) : ℤ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      rw [hstirling u hu]
      push_cast
      ring
    have hweighted :
        (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
            ((k - u : ℕ) : ℤ) * (Nat.stirlingSecond (m + 1 - u) (k - u) : ℤ)) =
          (k : ℤ) * twoAssocStirlingSecond (m + 1) k +
            (m + 1 : ℤ) * twoAssocStirlingSecond m (k - 1) := by
      let a : ℕ → ℤ := fun u => (-1) ^ u * (Nat.choose (m + 1) u : ℤ) *
        (Nat.stirlingSecond (m + 1 - u) (k - u) : ℤ)
      let w : ℕ → ℤ := fun u => (-1) ^ u * (Nat.choose (m + 1) u : ℤ) *
        (u : ℤ) * (Nat.stirlingSecond (m + 1 - u) (k - u) : ℤ)
      let c : ℕ → ℤ := fun v => (-1) ^ v * (Nat.choose m v : ℤ) *
        (Nat.stirlingSecond (m - v) (k - 1 - v) : ℤ)
      have hdecomp :
          (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
              ((k - u : ℕ) : ℤ) * (Nat.stirlingSecond (m + 1 - u) (k - u) : ℤ)) =
            (k : ℤ) * (∑ u ∈ Finset.range (k + 1), a u) -
              ∑ u ∈ Finset.range (k + 1), w u := by
        calc
          _ = ∑ u ∈ Finset.range (k + 1), ((k : ℤ) * a u - w u) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.mem_range] at hu
            have huk : u ≤ k := by omega
            have hcast : ((k - u : ℕ) : ℤ) = (k : ℤ) - (u : ℤ) := by
              exact Nat.cast_sub huk
            rw [hcast]
            simp only [a, w]
            ring
          _ = (∑ u ∈ Finset.range (k + 1), (k : ℤ) * a u) -
              ∑ u ∈ Finset.range (k + 1), w u := by
            rw [Finset.sum_sub_distrib]
          _ = _ := by rw [Finset.mul_sum]
      have hw : (∑ u ∈ Finset.range (k + 1), w u) =
          -(m + 1 : ℤ) * twoAssocStirlingSecond m (k - 1) := by
        have hshift : ∀ v < k, w (v + 1) = -(m + 1 : ℤ) * c v := by
          intro v hv
          have hv1 : 1 ≤ v + 1 := by omega
          have hchoose : ((v + 1 : ℕ) : ℤ) * (Nat.choose (m + 1) (v + 1) : ℤ) =
              (m + 1 : ℤ) * (Nat.choose m v : ℤ) := by
            exact_mod_cast choose_mul_aux m (v + 1) hv1
          push_cast at hchoose
          have hsub1 : m + 1 - (v + 1) = m - v := by omega
          have hsub2 : k - (v + 1) = k - 1 - v := by omega
          simp only [w, c, hsub1, hsub2, pow_succ]
          calc
            (-1 : ℤ) ^ v * -1 * (Nat.choose (m + 1) (v + 1) : ℤ) *
                (v + 1 : ℤ) * (Nat.stirlingSecond (m - v) (k - 1 - v) : ℤ) =
              -((-1 : ℤ) ^ v * ((v + 1 : ℤ) *
                (Nat.choose (m + 1) (v + 1) : ℤ)) *
                (Nat.stirlingSecond (m - v) (k - 1 - v) : ℤ)) := by ring
            _ = -((-1 : ℤ) ^ v * ((m + 1 : ℤ) * (Nat.choose m v : ℤ)) *
                (Nat.stirlingSecond (m - v) (k - 1 - v) : ℤ)) := by rw [hchoose]
            _ = -(m + 1 : ℤ) * ((-1 : ℤ) ^ v * (Nat.choose m v : ℤ) *
                (Nat.stirlingSecond (m - v) (k - 1 - v) : ℤ)) := by ring
        calc
          _ = ∑ v ∈ Finset.range k, w (v + 1) + w 0 := Finset.sum_range_succ' w k
          _ = ∑ v ∈ Finset.range k, (-(m + 1 : ℤ) * c v) := by
            simp only [w, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
              Nat.cast_zero, mul_zero, zero_mul, add_zero]
            apply Finset.sum_congr rfl
            intro v hv
            exact hshift v (Finset.mem_range.mp hv)
          _ = -(m + 1 : ℤ) * (∑ v ∈ Finset.range k, c v) := by
            rw [Finset.mul_sum]
          _ = _ := by
            rw [twoAssocStirlingSecond]
            have hrange : k - 1 + 1 = k := by omega
            rw [hrange]
      have ha : (∑ u ∈ Finset.range (k + 1), a u) =
          twoAssocStirlingSecond (m + 1) k := by
        rw [twoAssocStirlingSecond]
      rw [hdecomp, hw, ha]
      ring
    have hdrop :
        (∑ u ∈ Finset.range (k + 1), ((-1 : ℤ) ^ u) * (Nat.choose (m + 1) u : ℤ) *
            (Nat.stirlingSecond (m + 1 - u) (k - u - 1) : ℤ)) =
          twoAssocStirlingSecond (m + 1) (k - 1) := by
      rw [twoAssocStirlingSecond]
      have hrange : k - 1 + 1 = k := by omega
      rw [hrange, Finset.sum_range_succ]
      have hlast : Nat.stirlingSecond (m + 1 - k) (k - k - 1) = 0 := by
        simp only [Nat.sub_self, Nat.zero_sub]
        have hpos : 0 < m + 1 - k := by omega
        obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rw [ha, Nat.stirlingSecond_succ_zero]
      rw [hlast]
      simp only [Nat.cast_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      have hsub : k - u - 1 = k - 1 - u := by omega
      rw [hsub]
    rw [hexpand, hweighted, hdrop]
  rw [twoAssocStirlingSecond, hpascal, hI]
  have hneg :
      (∑ v ∈ Finset.range k, ((-1 : ℤ) ^ (v + 1)) * (Nat.choose (m + 1) v : ℤ) *
          (Nat.stirlingSecond (m + 1 - v) (k - 1 - v) : ℤ)) =
        -twoAssocStirlingSecond (m + 1) (k - 1) := by
    rw [twoAssocStirlingSecond]
    have hrange : k - 1 + 1 = k := by omega
    rw [hrange, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [pow_succ]
    ring
  rw [hneg]
  ring

private lemma twoAssoc_near_diagonal (m : ℕ) (hm : 0 < m) :
    twoAssocStirlingSecond (m + 2) (m + 1) = 0 := by
  rw [twoAssocStirlingSecond]
  have hstirling : ∀ u < m + 2,
      Nat.stirlingSecond (m + 2 - u) (m + 1 - u) = Nat.choose (m + 2 - u) 2 := by
    intro u hu
    have hfirst : m + 2 - u = (m + 1 - u) + 1 := by omega
    rw [hfirst, Nat.stirlingSecond_succ_self_left]
  have hprod : ∀ u ≤ m,
      Nat.choose (m + 2) u * Nat.choose (m + 2 - u) 2 =
        Nat.choose (m + 2) 2 * Nat.choose m u := by
    intro u hu
    have hmul := Nat.choose_mul (n := m + 2) (k := m + 2 - 2) (s := u) (by omega)
    have hsymm1 : Nat.choose (m + 2) (m + 2 - 2) = Nat.choose (m + 2) 2 := by
      simpa using Nat.choose_symm (by omega : 2 ≤ m + 2)
    have harg : m + 2 - u - 2 = m - u := by omega
    have hsymm2 : Nat.choose (m + 2 - u) (m - u) =
        Nat.choose (m + 2 - u) 2 := by
      have hle : 2 ≤ m + 2 - u := by omega
      have h := Nat.choose_symm hle
      rw [harg] at h
      exact h
    have hm2 : m + 2 - 2 = m := by omega
    rw [hsymm1, hm2, hsymm2] at hmul
    exact hmul.symm
  rw [Finset.sum_range_succ]
  have hlast : Nat.stirlingSecond (m + 2 - (m + 1)) (m + 1 - (m + 1)) = 0 := by
    norm_num [Nat.stirlingSecond_succ_zero]
  rw [hlast]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  calc
    (∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ u * (Nat.choose (m + 2) u : ℤ) *
        (Nat.stirlingSecond (m + 2 - u) (m + 1 - u) : ℤ)) =
      (Nat.choose (m + 2) 2 : ℤ) *
        ∑ u ∈ Finset.range (m + 1), (-1 : ℤ) ^ u * (Nat.choose m u : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mem_range] at hu
      rw [hstirling u (by omega)]
      have hp := hprod u (by omega)
      have hpz : (Nat.choose (m + 2) u : ℤ) * (Nat.choose (m + 2 - u) 2 : ℤ) =
          (Nat.choose (m + 2) 2 : ℤ) * (Nat.choose m u : ℤ) := by
        exact_mod_cast hp
      calc
        (-1 : ℤ) ^ u * (Nat.choose (m + 2) u : ℤ) *
            (Nat.choose (m + 2 - u) 2 : ℤ) =
          (-1 : ℤ) ^ u * ((Nat.choose (m + 2) u : ℤ) *
            (Nat.choose (m + 2 - u) 2 : ℤ)) := by ring
        _ = (-1 : ℤ) ^ u * ((Nat.choose (m + 2) 2 : ℤ) *
            (Nat.choose m u : ℤ)) := by rw [hpz]
        _ = (Nat.choose (m + 2) 2 : ℤ) *
            ((-1 : ℤ) ^ u * (Nat.choose m u : ℤ)) := by ring
    _ = 0 := by
      rw [Int.alternating_sum_range_choose_of_ne (Nat.ne_of_gt hm), mul_zero]

/-- **Vanishing of 2-associated Stirling numbers of the second kind.** For natural numbers
$n$ and $k$ with $n < 2k$, the 2-associated Stirling number of the second kind $S_2(n, k)$
equals $0$. -/
theorem twoAssocStirlingSecond_eq_zero_of_lt_two_mul (n k : ℕ) (hnk : n < 2 * k) :
    twoAssocStirlingSecond n k = 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      have hk : 1 ≤ k := by omega
      by_cases hnk' : n < k
      · exact twoAssoc_eq_zero_of_lt n k hnk'
      push Not at hnk'
      by_cases heq : k = n
      · subst k
        exact twoAssoc_self n (by omega)
      have hkn : k < n := by omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      by_cases hnear : k = m + 1
      · subst k
        exact twoAssoc_near_diagonal m (by omega)
      have hkm : k ≤ m := by omega
      rw [twoAssocStirlingSecond_recurrence m k hk hkm,
        ih (m + 1) (by omega) k (by omega),
        ih m (by omega) (k - 1) (by omega)]
      ring

end MetaMathlibExt
