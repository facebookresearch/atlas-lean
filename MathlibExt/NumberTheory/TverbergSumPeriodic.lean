/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import MathlibExt.NumberTheory.FloorCeilingSums
import Mathlib.Data.Nat.Choose.Sum

/-!
# Periodicity of Tverberg's sum

Adding a multiple of the modulus translates the rounded values by the same integer on all
affected subsets. The alternating signs on those subsets sum to zero.
-/

namespace MetaMathlibExt

namespace tverbergSum_periodic

open Finset

-- Taking complements turns the supersets of `s` into the subsets of its nonempty complement.
private theorem sum_sign_mul_ite {ℓ : ℕ} (s : Finset (Fin ℓ)) (hs : s.card < ℓ) (q : ℤ) :
    (∑ T : Finset (Fin ℓ), (-1 : ℤ) ^ (ℓ - T.card) * (if s ⊆ T then q else 0)) = 0 := by
  have hne : sᶜ.Nonempty := card_pos.mp (by simpa [card_compl] using Nat.sub_pos_of_lt hs)
  calc
    _ = ∑ U : Finset (Fin ℓ), if U ∈ sᶜ.powerset then (-1 : ℤ) ^ U.card * q else 0 := by
      refine Fintype.sum_equiv compl_involutive.toPerm _ _ fun T ↦ ?_
      change _ = if Tᶜ ∈ sᶜ.powerset then (-1 : ℤ) ^ Tᶜ.card * q else 0
      simp [card_compl, mul_ite]
    _ = (∑ U ∈ sᶜ.powerset, (-1 : ℤ) ^ U.card) * q := by
      rw [sum_ite_mem_eq, sum_mul]
    _ = 0 := by rw [sum_powerset_neg_one_pow_card_of_nonempty hne, zero_mul]

private theorem translate_rounding (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (x : ℝ) (q : ℤ) : F (x + q) = F x + q := by
  rcases hF with rfl | rfl | rfl | h
  · exact Int.floor_add_intCast _ _
  · exact Int.ceil_add_intCast _ _
  · exact round_add_intCast _ _
  · obtain rfl := Set.mem_singleton_iff.mp h
    simpa only [add_sub_right_comm] using Int.ceil_add_intCast (x - 1 / 2) q

end tverbergSum_periodic

open tverbergSum_periodic in
/-- **Periodicity of Tverberg's sum.** Let $\ell \ge 2$ and let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. For every index $i$ and every integer $q$, replacing
$a_i$ by $a_i + q m$ does not change $f(a, m, k)$, and $f(a, m, k + q m) = f(a, m, k)$.

The hypothesis $\ell \ge 2$ is needed: for $\ell = 1$, $F = \lfloor \cdot \rfloor$ and $m \ge 1$,
$f((a), m, k) = \lfloor (k + a)/m \rfloor - \lfloor k/m \rfloor$ increases by $q$ when $a$ is
replaced by $a + q m$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 3. -/
public theorem tverbergSum_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) (i : Fin ℓ) (q : ℤ) :
    tverbergSum F (Function.update a i (a i + q * m)) m k = tverbergSum F a m k ∧
      tverbergSum F a m (k + q * m) = tverbergSum F a m k := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hshift (z : ℤ) : F (((z + q * m : ℤ) : ℝ) / m) = F ((z : ℝ) / m) + q := by
    simpa [Int.cast_add, Int.cast_mul, add_div, Nat.cast_ne_zero.mpr hm] using
      translate_rounding F hF (z / m) q
  have hupdate (T : Finset (Fin ℓ)) :
      F (((k + ∑ j ∈ T, Function.update a i (a i + q * m) j : ℤ) : ℝ) / m) =
        F (((k + ∑ j ∈ T, a j : ℤ) : ℝ) / m) + if {i} ⊆ T then q else 0 := by
    by_cases hi : i ∈ T
    · rw [Finset.sum_update_of_mem hi, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi a]
      simp only [Finset.singleton_subset_iff, hi, ite_true]
      simpa only [add_assoc, add_left_comm, add_comm] using
        hshift (k + (a i + ∑ j ∈ T \ {i}, a j))
    · simp [Finset.sum_update_of_notMem hi, hi]
  constructor
  · simp only [tverbergSum, hupdate, mul_add, Finset.sum_add_distrib]
    rw [sum_sign_mul_ite {i} (by simpa using Nat.lt_of_succ_le hℓ) q, add_zero]
  · simp only [tverbergSum, add_right_comm k (q * m), hshift, mul_add, Finset.sum_add_distrib]
    have hzero := sum_sign_mul_ite (∅ : Finset (Fin ℓ)) (by simp; omega) q
    simpa using hzero

namespace tverbergPartialSum_vanish_and_periodic

open Finset tverbergSum_periodic

-- Moving the interval one step replaces its first term by that term plus one.
private theorem sum_range_add_int {m : ℕ} (g : ℤ → ℤ)
    (hg : ∀ c : ℤ, g ((m : ℤ) + c) = g c + 1) (c : ℤ) :
    (∑ k ∈ range m, g ((k : ℤ) + c)) = (∑ k ∈ range m, g k) + c := by
  let S (d : ℤ) := ∑ k ∈ range m, g ((k : ℤ) + d)
  have hstep (d : ℤ) : S (d + 1) = S d + 1 := by
    have h := (sum_range_succ' (fun k : ℕ ↦ g ((k : ℤ) + d)) m).symm.trans
      (sum_range_succ (fun k : ℕ ↦ g ((k : ℤ) + d)) m)
    simp only [Nat.cast_add, Nat.cast_one, add_right_comm _ 1 d, add_assoc, Nat.cast_zero,
      zero_add, hg] at h
    change S (d + 1) + g d = S d + (g d + 1) at h
    omega
  suffices S c = S 0 + c by simpa only [S, add_zero] using this
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih => rw [hstep, ih, add_assoc]
  | pred n ih =>
    have h := hstep (-(n : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    omega

private theorem sum_range_tverbergSum_eq_zero {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) : ∑ k ∈ range m, tverbergSum F a m k = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  let g (z : ℤ) := F ((z : ℝ) / m)
  have hg (c : ℤ) : g ((m : ℤ) + c) = g c + 1 := by
    simpa [g, Int.cast_add, add_div, Nat.cast_ne_zero.mpr hm, add_comm] using
      translate_rounding F hF ((c : ℝ) / m) 1
  let C := ∑ k ∈ range m, g k
  let sign (T : Finset (Fin ℓ)) := (-1 : ℤ) ^ (ℓ - T.card)
  have hcoords (T : Finset (Fin ℓ)) :
      (∑ i ∈ T, a i) = ∑ i : Fin ℓ, if {i} ⊆ T then a i else 0 := by
    simp only [singleton_subset_iff, sum_ite_mem, univ_inter]
  calc
    _ = ∑ T : Finset (Fin ℓ), sign T * (C + ∑ i ∈ T, a i) := by
      simp only [tverbergSum]
      -- Interchange the index and subset sums.
      rw [sum_comm]
      simp only [← mul_sum, sum_range_add_int g hg, C, sign, g]
    _ = (∑ T : Finset (Fin ℓ), sign T * C) +
        ∑ i : Fin ℓ, ∑ T : Finset (Fin ℓ), sign T * (if {i} ⊆ T then a i else 0) := by
      simp only [hcoords, mul_add, sum_add_distrib, mul_sum]
      rw [sum_comm (s := (univ : Finset (Finset (Fin ℓ)))) (t := (univ : Finset (Fin ℓ)))]
    _ = 0 := by
      have hconstant := sum_sign_mul_ite (∅ : Finset (Fin ℓ)) (by simp; omega) C
      have hcoordinate (i : Fin ℓ) := sum_sign_mul_ite {i}
        (by simpa using Nat.lt_of_succ_le hℓ) (a i)
      simp only [empty_subset, ite_true] at hconstant
      simp only [sign, hconstant, hcoordinate, sum_const_zero, zero_add]

-- Separate the contribution of index zero to compare positive-index tails.
private theorem sum_range_eq_add_sum_Icc (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), f k = f 0 + ∑ k ∈ Icc 1 n, f k := by
  have h : range (n + 1) = insert 0 (Icc 1 n) := by
    ext k
    simp
    omega
  rw [h, sum_insert (by simp)]

end tverbergPartialSum_vanish_and_periodic

open Finset tverbergPartialSum_vanish_and_periodic in
/-- **Vanishing and periodicity of partial Tverberg sums.** Let $\ell \ge 2$, let
$a = (a_1, \dots, a_\ell)$ be integers and let $m$ be a natural number. Let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$, and for an integer $k$ let
$f^F(a, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum, with $x/0 = 0$. For natural $K$ put $S^F(a, K) = \sum_{k=0}^{K} f^F(a, k)$
and $T^F(a, K) = \sum_{k=1}^{K} f^F(a, k)$, and for an index $i$ and an integer $p$ let $a'$ be
$a$ with $a_i$ replaced by $a_i + p m$. Then:
(i) $\sum_{k=0}^{m-1} f^F(a, k) = 0$ (an empty sum when $m = 0$);
(ii) $S^F(a, K + q m) = S^F(a, K)$ for all natural $K$ and $q$, and $S^F(a', K) = S^F(a, K)$
for every natural $K$, every index $i$ and every integer $p$;
(iii) if $F$ is $\lceil \cdot \rceil$ or $r^-$, then $T^F(a, m) = 0$,
$T^F(a, K + q m) = T^F(a, K)$ for all natural $K$ and $q$, and $T^F(a', K) = T^F(a, K)$ for
every natural $K$, every index $i$ and every integer $p$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 7. -/
public theorem tverbergPartialSum_vanish_and_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (a : Fin ℓ → ℤ) (m : ℕ) :
    (∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
      ∑ k ∈ Finset.range m, tverbergSum F a m k = 0 ∧
        ∀ K q : ℕ, ∑ k ∈ Finset.range (K + q * m + 1), tverbergSum F a m k =
          ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k ∧
        ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
          ∑ k ∈ Finset.range (K + 1), tverbergSum F (Function.update a i (a i + q * m)) m k =
            ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k) ∧
      ∀ F ∈ ({Int.ceil, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∑ k ∈ Finset.Icc 1 m, tverbergSum F a m k = 0 ∧
          ∀ K q : ℕ, ∑ k ∈ Finset.Icc 1 (K + q * m), tverbergSum F a m k =
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k ∧
          ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F (Function.update a i (a i + q * m)) m k =
              ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k := by
  let i₀ : Fin ℓ := ⟨0, by omega⟩
  have hvanish (F : ℝ → ℤ) (hF : F ∈ ({Int.floor, Int.ceil, round,
      fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ))) := sum_range_tverbergSum_eq_zero hℓ F hF a m
  have hperiod (F : ℝ → ℤ) (hF : F ∈ ({Int.floor, Int.ceil, round,
      fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ))) (k q : ℕ) :
      tverbergSum F a m ((q * m + k : ℕ) : ℤ) = tverbergSum F a m k := by
    simpa only [Nat.cast_add, Nat.cast_mul, add_comm] using
      (tverbergSum_periodic hℓ F hF a m k i₀ q).2
  have hblocks (F : ℝ → ℤ) (hF : F ∈ ({Int.floor, Int.ceil, round,
      fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ))) (q : ℕ) :
      ∑ k ∈ range (q * m), tverbergSum F a m k = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      simp only [hperiod F hF, zero_add, hvanish F hF]
  have hprefix (F : ℝ → ℤ) (hF : F ∈ ({Int.floor, Int.ceil, round,
      fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ))) (K q : ℕ) :
      ∑ k ∈ range (K + q * m + 1), tverbergSum F a m k =
        ∑ k ∈ range (K + 1), tverbergSum F a m k := by
    rw [add_right_comm K, add_comm (K + 1), sum_range_add, hblocks F hF]
    simp only [hperiod F hF, zero_add]
  have hupdate (F : ℝ → ℤ) (hF : F ∈ ({Int.floor, Int.ceil, round,
      fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ))) (s : Finset ℕ) (i : Fin ℓ) (q : ℤ) :
      ∑ k ∈ s, tverbergSum F (Function.update a i (a i + q * m)) m k =
        ∑ k ∈ s, tverbergSum F a m k :=
    sum_congr rfl fun k _ ↦ (tverbergSum_periodic hℓ F hF a m k i q).1
  refine ⟨fun F hF ↦ ⟨hvanish F hF, fun K q ↦ ⟨hprefix F hF K q, fun K ↦ hupdate F hF _⟩⟩,
    fun F hF ↦ ?_⟩
  have hF' : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
    rcases hF with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have hend : tverbergSum F a m m = tverbergSum F a m 0 := by
    simpa using hperiod F hF' 0 1
  refine ⟨?_, fun K q ↦ ⟨?_, fun K ↦ hupdate F hF' _⟩⟩
  · have h := sum_range_succ (fun k : ℕ ↦ tverbergSum F a m k) m
    rw [sum_range_eq_add_sum_Icc, hvanish F hF', hend, zero_add] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  · have h := hprefix F hF' K q
    simp only [sum_range_eq_add_sum_Icc] at h
    exact add_left_cancel h

end MetaMathlibExt
