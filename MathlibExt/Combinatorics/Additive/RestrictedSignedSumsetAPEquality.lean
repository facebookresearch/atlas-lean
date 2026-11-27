/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumsetAPOneExtra
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Restricted signed sumsets of positive arithmetic progressions

The first `h + 1` terms give the lower bound via the initial-segment extension theorem.
When the common difference is twice the first term, the signed sums are multiples of
that first term with a fixed parity after division, and their absolute values are bounded
by the sum of the largest `h` terms.

## References

* Mohan, Raj Kumar Mistri, and Ram Krishna Pandey, *Some Direct and Inverse Problems for the
  Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, pp. 1–36,
  Corollary 1 (pp. 6–7), with Theorem 3 and the initial-segment bound of Lemma 1.
* Melvyn B. Nathanson, *Additive Number Theory: Inverse Problems and the Geometry of Sumsets*,
  Graduate Texts in Mathematics 165, Springer, 1996, Theorem 1.9. The paper uses Nathanson's
  restricted sumset bound for the extension step; here we use the initial-segment theorem,
  whose Lean proof instead counts new sums each time a term is adjoined.
-/

open Finset

namespace MetaMathlibExt

private theorem orderedFinset_castLE {m k : ℕ} (a : Fin k → ℤ) (hm : m ≤ k) :
    orderedFinset (fun i : Fin m => a (i.castLE hm)) = initialSegment a m := by
  ext x
  simp only [orderedFinset, initialSegment, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.castLE hm, i.isLt, hi⟩,
    fun ⟨i, hi, hix⟩ => ⟨⟨i, hi⟩, hix⟩⟩

-- The largest `s.card` odd numbers below `2*k` sum to `2*s.card*k - s.card^2`.
private theorem sum_odd_le {k : ℕ} {s : Finset ℕ} (hs : s ⊆ range k) :
    ∑ i ∈ s, (2 * (i : ℤ) + 1) ≤ 2 * (s.card : ℤ) * k - (s.card : ℤ) ^ 2 := by
  induction k generalizing s with
  | zero =>
    have h : s = ∅ := by simpa using hs
    simp [h]
  | succ k ih =>
    rw [range_add_one] at hs
    rw [Nat.cast_succ]
    by_cases hk : k ∈ s
    · have hsub : s.erase k ⊆ range k := fun i hi =>
        (mem_insert.mp (hs (mem_of_mem_erase hi))).resolve_left (ne_of_mem_erase hi)
      have hcard : ((s.erase k).card : ℤ) + 1 = s.card := by
        exact_mod_cast card_erase_add_one hk
      rw [← sum_erase_add s (fun i : ℕ => 2 * (i : ℤ) + 1) hk, ← hcard]
      calc
        _ ≤ (2 * ((s.erase k).card : ℤ) * k - ((s.erase k).card : ℤ) ^ 2) +
            (2 * (k : ℤ) + 1) := add_le_add (ih hsub) le_rfl
        _ = _ := by ring
    · have hsub : s ⊆ range k := fun i hi =>
        (mem_insert.mp (hs hi)).resolve_left (fun he => hk (he ▸ hi))
      nlinarith only [ih hsub, show (0 : ℤ) ≤ s.card by positivity]

private theorem card_restrictedSignedSumset_odd_le {h k : ℕ} (a : Fin k → ℤ)
    (hk : 0 < k) (hhk : h ≤ k) (hb : 0 < a ⟨0, hk⟩)
    (hap : IsIndexedAP a (2 * a ⟨0, hk⟩)) :
    ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≤
      2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 := by
  let b := a ⟨0, hk⟩
  let odd (i : ℕ) : ℤ := 2 * (i : ℤ) + 1
  let term (i : ℕ) := b * odd i
  have hterm (i : ℕ) (hi : i < k) : a ⟨i, hi⟩ = term i := by
    induction i with
    | zero => simp [b, term, odd]
    | succ i ih =>
      rw [hap.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl, ih (by omega)]
      simp only [term, odd, Nat.cast_succ]
      change b * (2 * (i : ℤ) + 1) + 2 * b = _
      ring
  have hinj : Function.Injective term := by
    intro i j hij
    have he := mul_left_cancel₀ hb.ne' hij
    dsimp [odd] at he
    omega
  have hA : orderedFinset a = (range k).image term := by
    ext x
    simp only [orderedFinset, mem_image, mem_range, mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i.isLt, (hterm i i.isLt).symm.trans hi⟩,
      fun ⟨i, hi, hix⟩ => ⟨⟨i, hi⟩, (hterm i hi).trans hix⟩⟩
  let M : ℤ := 2 * (h : ℤ) * k - (h : ℤ) ^ 2
  -- Write each normalized signed sum as `2*t + h`. The bound `M` gives
  -- a range of at most `M + 1` integer values for `t`.
  let I := Icc ((-M - h) / 2) ((M - h) / 2)
  have hsum (s : Finset ℕ) : ∑ y ∈ s.image term, y = b * ∑ i ∈ s, odd i := by
    rw [sum_image (fun _ _ _ _ he => hinj he), mul_sum]
  have hsubset : restrictedSignedSumset h (orderedFinset a) ⊆
      I.image (fun t : ℤ => b * (2 * t + h)) := by
    rw [hA]
    intro x hx
    simp only [restrictedSignedSumset, mem_image, mem_sigma, mem_powersetCard, mem_powerset,
      Sigma.exists] at hx
    obtain ⟨B, N, ⟨⟨hB, hcard⟩, hN⟩, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := subset_image_iff.mp hB
    obtain ⟨n, hn, rfl⟩ := subset_image_iff.mp hN
    rw [card_image_of_injective _ hinj] at hcard
    have hupper : ∑ i ∈ s, odd i ≤ M := by
      simpa only [M, hcard] using sum_odd_le hs
    have hn0 : 0 ≤ ∑ i ∈ n, odd i := sum_nonneg fun i _ => by dsimp [odd]; positivity
    have hnsum : ∑ i ∈ n, odd i ≤ ∑ i ∈ s, odd i :=
      sum_le_sum_of_subset_of_nonneg hn fun i _ _ => by dsimp [odd]; positivity
    have hparity : ∑ i ∈ s, odd i = 2 * (∑ i ∈ s, (i : ℤ)) + h := by
      simp [odd, sum_add_distrib, mul_sum, hcard]
    let t : ℤ := (∑ i ∈ s, (i : ℤ)) - ∑ i ∈ n, odd i
    have hnorm : 2 * t + h = (∑ i ∈ s, odd i) - 2 * ∑ i ∈ n, odd i := by
      dsimp [t]
      omega
    refine mem_image.mpr ⟨t, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · change (-M - h) / 2 ≤ t
      omega
    · change t ≤ (M - h) / 2
      omega
    · rw [hnorm, hsum, hsum]
      ring
  have hM : 0 ≤ M := by
    have hhk' : (h : ℤ) ≤ k := by exact_mod_cast hhk
    unfold M
    nlinarith only [mul_nonneg (show (0 : ℤ) ≤ h by positivity)
      (show (0 : ℤ) ≤ 2 * k - h by omega)]
  have hI : (I.card : ℤ) = M + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  have hc : (restrictedSignedSumset h (orderedFinset a)).card ≤ I.card :=
    (card_le_card hsubset).trans card_image_le
  exact (show ((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≤ I.card by
    exact_mod_cast hc).trans_eq hI

/-- **Lower bound for restricted signed sumsets of arithmetic progressions.** Let $h \ge 3$ and
$k \ge h + 1$ be natural numbers, and let $a_1 < a_2 < \cdots < a_k$ be integers with $a_1 > 0$
that form an arithmetic progression with common difference $d > 0$, that is,
$a_{i+1} = a_i + d$ for $1 \le i < k$. Let $A = \{a_1, \ldots, a_k\}$ and let $h^{\wedge}_{\pm} A$
be the restricted signed sumset of $A$. Then $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 1$ if
$d = 2a_1$, and $|h^{\wedge}_{\pm} A| \ge 2hk - h^2 + 2$ otherwise. Moreover,
$|h^{\wedge}_{\pm} A| = 2hk - h^2 + 1$ if and only if $d = 2a_1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Corollary 1. -/
public theorem card_restrictedSignedSumset_ap_ge
    (h k : ℕ) (hh : 3 ≤ h) (hk : h + 1 ≤ k) (a : Fin k → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : 0 < a ⟨0, by omega⟩) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1
      else 2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 2) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        2 * (h : ℤ) * k - (h : ℤ) ^ 2 + 1 ↔ d = 2 * a ⟨0, by omega⟩) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let b : Fin (h + 1) → ℤ := fun i => a (i.castLE hk)
  have hpos' (i : Fin k) : 0 < a i := hpos.trans_le (ha.monotone (show i₀ ≤ i from Nat.zero_le _))
  have hb : StrictMono b := fun _ _ hij => ha hij
  have hap' : IsIndexedAP b d := ⟨hap.1, fun i j hij => hap.2 (i.castLE hk) (j.castLE hk) hij⟩
  have hshort := (card_restrictedSignedSumset_ap_h_add_one h hh b d hb
    (fun i => hpos' (i.castLE hk)) hap').1
  change _ ≥ if d = 2 * a i₀ then _ else _ at hshort
  rw [show orderedFinset b = initialSegment a (h + 1) from orderedFinset_castLE a hk] at hshort
  change (_ ≥ if d = 2 * a i₀ then _ else _) ∧ (_ = _ ↔ d = 2 * a i₀)
  by_cases hd : d = 2 * a i₀
  · have hlo := card_restrictedSignedSumset_ge_of_initialSegment h k hh (by omega) a 0
      ha hpos' (by decide) (by simpa only [ite_eq_left hd, add_zero] using hshort)
    rw [add_zero] at hlo
    have hhi := card_restrictedSignedSumset_odd_le a i₀.isLt (by omega : h ≤ k) hpos (hd ▸ hap)
    exact ⟨by simpa only [ite_eq_left hd] using hlo,
      ⟨fun _ => hd, fun _ => le_antisymm hhi hlo⟩⟩
  · have hlo := card_restrictedSignedSumset_ge_of_initialSegment h k hh (by omega) a 1
      ha hpos' (by decide) (by simpa only [ite_eq_right hd] using hshort)
    exact ⟨by rw [ite_eq_right hd]; omega, ⟨fun he => by omega, fun he => (hd he).elim⟩⟩

end MetaMathlibExt
