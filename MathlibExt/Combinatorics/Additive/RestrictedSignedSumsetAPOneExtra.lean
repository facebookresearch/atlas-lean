/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Restricted signed sums of an arithmetic progression with one extra term

For the lower bound, translate the signed sums of the shorter progression by the new largest
term. Below this translate, count two all-negative sums and a progression of sums with just
one positive term. For the equality case, the normalized odd progression has an upper bound
from the common parity and the largest possible unsigned sum.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Finite integer sequences in arithmetic progression.** A sequence $a_0, \dots, a_{k-1}$ of
integers is an arithmetic progression with common difference $d$ if $d > 0$ and
$a_{i+1} = a_i + d$ for every $i$ with $i + 1 < k$.

The condition is stated on adjacent terms, so no nonemptiness assumption is needed to name a
first term.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, definition of
arithmetic progression. -/
public def IsIndexedAP {k : ℕ} (a : Fin k → ℤ) (d : ℤ) : Prop :=
  0 < d ∧ ∀ (i j : Fin k), (i : ℕ) + 1 = (j : ℕ) → a j = a i + d

end

private def apTerm (b d : ℤ) (i : ℕ) : ℤ := b + (i : ℤ) * d

private theorem apTerm_injective (b : ℤ) {d : ℤ} (hd : d ≠ 0) :
    Function.Injective (apTerm b d) := by
  intro i j hij
  unfold apTerm at hij
  have he : (i : ℤ) * d = (j : ℤ) * d := by omega
  exact_mod_cast mul_right_cancel₀ hd he

private def apFinset (b d : ℤ) (n : ℕ) : Finset ℤ := (range n).image (apTerm b d)

private theorem mem_ap_signed {b d x : ℤ} (hd : d ≠ 0) {n h : ℕ} :
    x ∈ restrictedSignedSumset h (apFinset b d n) ↔
      ∃ B ⊆ range n, B.card = h ∧ ∃ N ⊆ B,
        (∑ i ∈ B, apTerm b d i) - 2 * ∑ i ∈ N, apTerm b d i = x := by
  classical
  have hi := apTerm_injective b hd
  have hsum (B : Finset ℕ) : ∑ i ∈ B.image (apTerm b d), i = ∑ i ∈ B, apTerm b d i :=
    Finset.sum_image (fun _ _ _ _ h => hi h)
  simp only [restrictedSignedSumset, mem_image, mem_sigma, mem_powersetCard, mem_powerset,
    Sigma.exists, apFinset]
  constructor
  · rintro ⟨S, T, ⟨⟨hS, hSc⟩, hT⟩, hx⟩
    obtain ⟨B, hB, rfl⟩ := Finset.subset_image_iff.mp hS
    obtain ⟨N, hN, rfl⟩ := Finset.subset_image_iff.mp hT
    rw [card_image_of_injective _ hi] at hSc
    exact ⟨B, hB, hSc, N, hN, by simpa only [hsum] using hx⟩
  · rintro ⟨B, hB, hBc, N, hN, hx⟩
    exact ⟨B.image (apTerm b d), N.image (apTerm b d),
      ⟨⟨image_subset_image hB, (card_image_of_injective _ hi).trans hBc⟩,
        image_subset_image hN⟩, by simpa only [hsum] using hx⟩

private theorem orderedFinset_eq_ap {h : ℕ} {a : Fin (h + 1) → ℤ} {d : ℤ}
    (hap : IsIndexedAP a d) : orderedFinset a = apFinset (a 0) d (h + 1) := by
  have he (i : ℕ) (hi : i < h + 1) : a ⟨i, hi⟩ = apTerm (a 0) d i := by
    induction i with
    | zero => simp [apTerm]
    | succ i ih =>
      rw [hap.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl, ih (by omega)]
      simp only [apTerm, Nat.cast_succ]
      ring
  ext x
  simp only [orderedFinset, apFinset, mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, (he i.val i.isLt).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, he i hi⟩

-- Translate the shorter sumset by the new largest element. The new witnesses all lie
-- below that translate: omit one of the first two terms with all signs negative, or
-- omit `i` and make `j` positive, where `i + 2*j` takes the values from 1 to `2*n-1`.
private theorem card_ap_signed_step {b d : ℤ} (hb : 0 < b) (hd : 0 < d)
    {n : ℕ} (hn : 3 ≤ n) :
    (restrictedSignedSumset (n - 1) (apFinset b d n)).card + (2 * n + 1) ≤
      (restrictedSignedSumset n (apFinset b d (n + 1))).card := by
  classical
  let a := apTerm b d
  let T := ∑ i ∈ range (n + 1), a i
  let S := restrictedSignedSumset (n - 1) (apFinset b d n)
  let U := S.image (fun x => x + a n)
  let V := (range 2).image (fun i => -T + a i)
  let W := (Icc 1 (2 * n - 1)).image (fun r : ℕ => -T + b + 2 * b + (r : ℤ) * d)
  let X := restrictedSignedSumset n (apFinset b d (n + 1))
  have ha (i : ℕ) : a i = b + (i : ℤ) * d := rfl
  have hab (i : ℕ) : b ≤ a i := by
    rw [ha]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hd.le)
  have hpos (i : ℕ) : 0 ≤ a i := hb.le.trans (hab i)
  have hnew : n ∉ range n := by simp
  have hT : T = (∑ i ∈ range n, a i) + a n := by simp [T, sum_range_succ]
  have hUn (z : ℤ) (hz : z ∈ U) : z ∈ X ∧ -T + b + 2 * a n ≤ z := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨B, hB, hBc, N, hN, hx⟩ := (mem_ap_signed hd.ne').mp hx
    have hnB : n ∉ B := fun h => hnew (hB h)
    have hins : insert n B ⊆ range (n + 1) := by
      rw [range_add_one]
      exact insert_subset_insert _ hB
    refine ⟨(mem_ap_signed hd.ne').mpr ⟨insert n B, hins, ?_, N,
      hN.trans (subset_insert _ _), ?_⟩, ?_⟩
    · rw [card_insert_of_notMem hnB, hBc]
      omega
    · rw [sum_insert hnB, ← hx]
      ring
    · have hne : B ≠ range n := by
        intro h
        rw [h, card_range] at hBc
        omega
      obtain ⟨j, hj, hjB⟩ := exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hB, hne⟩)
      have hsumB := sum_le_sum_of_subset_of_nonneg (insert_subset hj hB)
        (f := a) (fun i _ _ => hpos i)
      rw [sum_insert hjB] at hsumB
      have hsumN := sum_le_sum_of_subset_of_nonneg hN (f := a) (fun i _ _ => hpos i)
      change (∑ i ∈ B, a i) - 2 * (∑ i ∈ N, a i) = x at hx
      linarith only [hsumB, hsumN, hab j, hx, hT]
  have hVn (z : ℤ) (hz : z ∈ V) : z ∈ X ∧ z ≤ -T + b + d := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    have hi' : i < 2 := mem_range.mp hi
    have hir : i ∈ range (n + 1) := mem_range.mpr (by omega)
    let B := (range (n + 1)).erase i
    have hBc : B.card = n := by simp [B, card_erase_of_mem hir]
    have hsum : (∑ j ∈ B, a j) + a i = T := sum_erase_add _ a hir
    refine ⟨(mem_ap_signed hd.ne').mpr ⟨B, erase_subset _ _, hBc, B, Subset.rfl, ?_⟩, ?_⟩
    · linarith only [hsum]
    · have hle : (i : ℤ) ≤ 1 := by omega
      rw [ha]
      linarith only [mul_le_mul_of_nonneg_right hle hd.le]
  have hWn (z : ℤ) (hz : z ∈ W) :
      z ∈ X ∧ -T + b + d < z ∧ z < -T + b + 2 * a n := by
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hz
    obtain ⟨hr1, hr2⟩ := mem_Icc.mp hr
    have hrlo : (1 : ℤ) ≤ (r : ℤ) := by omega
    have hrhi : (r : ℤ) < 2 * (n : ℤ) := by omega
    refine ⟨?_, ?_, ?_⟩
    · have hw : ∃ i j : ℕ, i ≤ n ∧ j ≤ n ∧ i ≠ j ∧ i + 2 * j = r := by
        by_cases hm : r % 2 = 0
        · exact ⟨0, r / 2, by omega, by omega, by omega, by omega⟩
        · by_cases h3 : r = 3
          · exact ⟨3, 0, hn, by omega, by decide, by omega⟩
          · exact ⟨1, r / 2, by omega, by omega, by omega, by omega⟩
      obtain ⟨i, j, hi, hj, hij, hr⟩ := hw
      have hir : i ∈ range (n + 1) := mem_range.mpr (by omega)
      let B := (range (n + 1)).erase i
      have hjB : j ∈ B := mem_erase.mpr ⟨Ne.symm hij, mem_range.mpr (by omega)⟩
      have hBc : B.card = n := by simp [B, card_erase_of_mem hir]
      have hB : (∑ k ∈ B, a k) + a i = T := sum_erase_add _ a hir
      have hN := sum_erase_add B a hjB
      have hre : (i : ℤ) + 2 * (j : ℤ) = r := by exact_mod_cast hr
      refine (mem_ap_signed hd.ne').mpr
        ⟨B, erase_subset _ _, hBc, B.erase j, erase_subset _ _, ?_⟩
      change (∑ k ∈ B, a k) - 2 * (∑ k ∈ B.erase j, a k) = _
      rw [ha i] at hB
      rw [ha j] at hN
      linarith only [hB, hN, congrArg (· * d) hre]
    · linarith only [hb, mul_le_mul_of_nonneg_right hrlo hd.le]
    · rw [ha]
      linarith only [mul_lt_mul_of_pos_right hrhi hd]
  have hcut : -T + b + d < -T + b + 2 * a n := by
    have hn' : (1 : ℤ) ≤ (n : ℤ) := by omega
    rw [ha n]
    linarith only [hb, hd, mul_le_mul_of_nonneg_right hn' hd.le]
  have hVW : Disjoint V W := disjoint_left.mpr fun z hV hW =>
    (hWn z hW).2.1.not_ge (hVn z hV).2
  have hVU : Disjoint (V ∪ W) U := by
    refine disjoint_left.mpr fun z hz hU => ?_
    rcases mem_union.mp hz with hV | hW
    · exact ((hVn z hV).2.trans_lt hcut).not_ge (hUn z hU).2
    · exact (hWn z hW).2.2.not_ge (hUn z hU).2
  have hsubset : (V ∪ W) ∪ U ⊆ X :=
    union_subset (union_subset (fun z hz => (hVn z hz).1) (fun z hz => (hWn z hz).1))
      (fun z hz => (hUn z hz).1)
  have hVc : V.card = 2 := by
    change ((range 2).image (fun i => -T + a i)).card = 2
    rw [card_image_of_injective _ (fun _ _ h => apTerm_injective b hd.ne' (add_left_cancel h))]
    simp
  have hWc : W.card = 2 * n - 1 := by
    change ((Icc 1 (2 * n - 1)).image (apTerm (-T + b + 2 * b) d)).card = _
    rw [card_image_of_injective _ (apTerm_injective (-T + b + 2 * b) hd.ne'), Nat.card_Icc]
    omega
  have hUc : U.card = S.card :=
    card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  have hcard := card_le_card hsubset
  rw [card_union_of_disjoint hVU, card_union_of_disjoint hVW, hVc, hWc, hUc] at hcard
  change S.card + (2 * n + 1) ≤ X.card
  omega

-- The sixteen witnesses are ordered independently of the ratio `d / b`. The
-- seventeenth, `-b - 4*d`, lies between the third and fifth and meets the fourth
-- exactly when `d = 2*b`.
private theorem card_ap_signed_three {b d : ℤ} (hb : 0 < b) (hd : 0 < d) :
    (if d = 2 * b then 16 else 17) ≤ (restrictedSignedSumset 3 (apFinset b d 4)).card := by
  let f : Fin 16 → ℤ := ![-3*b-6*d, -3*b-5*d, -3*b-4*d, -3*b-3*d,
    -b-3*d, -b-2*d, -b-d, -b, -b+d, b+d, b+2*d, b+3*d,
    3*b+3*d, 3*b+4*d, 3*b+5*d, 3*b+6*d]
  let s := univ.image f
  let X := restrictedSignedSumset 3 (apFinset b d 4)
  have hf : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> simp [f] <;> linarith
  have hc : s.card = 16 := by simp [s, card_image_of_injective _ hf.injective]
  have hs : s ⊆ X := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    -- Supplying the supports on the index set keeps every side condition decidable.
    let B : Fin 16 → Finset ℕ := ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2},
      {0, 1, 2}, {0, 1, 3}, {0, 1, 2}, {1, 2, 3}, {0, 1, 2}, {0, 1, 2},
      {0, 1, 3}, {0, 1, 2}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}]
    let N : Fin 16 → Finset ℕ := ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2},
      {1, 2}, {0, 3}, {0, 2}, {1, 2}, {0, 1}, {1}, {1}, {0}, ∅, ∅, ∅, ∅]
    refine (mem_ap_signed hd.ne').2 ⟨B i, ?_, ?_, N i, ?_, ?_⟩
    · fin_cases i <;> decide
    · fin_cases i <;> decide
    · fin_cases i <;> decide
    · fin_cases i <;> norm_num [B, N, f, sum_insert, apTerm] <;> ring
  by_cases he : d = 2 * b
  · simpa only [ite_eq_left he, hc] using card_le_card hs
  · have hx : -b - 4*d ∈ X := by
      refine (mem_ap_signed hd.ne').2 ⟨{0, 1, 3}, by decide, by decide, {1, 3}, by decide, ?_⟩
      (norm_num [sum_insert, apTerm]; ring)
    have hxs : -b - 4*d ∉ s := by
      intro hx
      obtain ⟨i, _, hi⟩ := mem_image.mp hx
      fin_cases i <;> simp [f] at hi <;> (first | linarith | exact he (by linarith))
    have hcard := card_le_card (insert_subset hx hs)
    simpa only [card_insert_of_notMem hxs, hc, ite_eq_right he] using hcard

private theorem card_ap_signed_lower {b d : ℤ} (hb : 0 < b) (hd : 0 < d) (h : ℕ)
    (hh : 3 ≤ h) :
    ((h + 1) ^ 2 + if d = 2 * b then 0 else 1) ≤
      (restrictedSignedSumset h (apFinset b d (h + 1))).card := by
  induction h with
  | zero => omega
  | succ h ih =>
    by_cases h3 : 3 ≤ h
    · have hstep := card_ap_signed_step hb hd (show 3 ≤ h + 1 by omega)
      rw [Nat.add_sub_cancel] at hstep
      have he : (h + 1 + 1) ^ 2 = (h + 1) ^ 2 + (2 * (h + 1) + 1) := by ring
      rw [he, add_right_comm]
      exact (Nat.add_le_add_right (ih h3) _).trans hstep
    · have he : h = 2 := by omega
      subst h
      by_cases he : d = 2 * b <;> simpa [he] using card_ap_signed_three hb hd

-- At `d = 2*b`, every term is `b` times an odd number. If `i` is omitted and
-- `N` is the set of negative indices, the signed sum is `b * (M - 2*t)` with
-- `M = (h+1)^2 - 1` and `t = i + ∑ j ∈ N, (2*j + 1)` in `[0,M]`.
private theorem card_ap_signed_upper {b : ℤ} (hb : 0 < b) (h : ℕ) :
    (restrictedSignedSumset h (apFinset b (2 * b) (h + 1))).card ≤ (h + 1) ^ 2 := by
  let odd (i : ℕ) : ℤ := 2 * (i : ℤ) + 1
  let M : ℤ := ((h : ℤ) + 1) ^ 2 - 1
  let f (t : ℤ) : ℤ := b * (M - 2 * t)
  have htotal (n : ℕ) : (∑ i ∈ range n, odd i) = (n : ℤ) ^ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, Nat.cast_succ]
      unfold odd
      ring
  have hfactor (s : Finset ℕ) : (∑ i ∈ s, apTerm b (2 * b) i) = b * ∑ i ∈ s, odd i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    unfold apTerm odd
    ring
  have hd : 2 * b ≠ 0 := by omega
  have hsubset : restrictedSignedSumset h (apFinset b (2 * b) (h + 1)) ⊆ (Icc 0 M).image f := by
    intro x hx
    obtain ⟨B, hB, hBc, N, hN, rfl⟩ := (mem_ap_signed hd).mp hx
    have hne : B ≠ range (h + 1) := by
      intro he
      rw [he, card_range] at hBc
      omega
    obtain ⟨i, hi, hiB⟩ := exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hB, hne⟩)
    have he : B = (range (h + 1)).erase i := by
      apply eq_of_subset_of_card_le (subset_erase.mpr ⟨hB, hiB⟩)
      simp [card_erase_of_mem hi, hBc]
    have hsum := sum_erase_add (range (h + 1)) odd hi
    rw [← he, htotal (h + 1), Nat.cast_add, Nat.cast_one] at hsum
    have hnonneg (j : ℕ) : 0 ≤ odd j := by
      unfold odd
      positivity
    have hN0 := sum_nonneg (s := N) (fun j _ => hnonneg j)
    have hNB := sum_le_sum_of_subset_of_nonneg hN (fun j _ _ => hnonneg j)
    refine mem_image.mpr ⟨(i : ℤ) + ∑ j ∈ N, odd j, mem_Icc.mpr ⟨by positivity, ?_⟩, ?_⟩
    · unfold odd at hsum
      unfold M
      have hi0 : 0 ≤ (i : ℤ) := by positivity
      linarith only [hsum, hNB, hi0]
    · rw [hfactor, hfactor]
      have hsum' : (∑ j ∈ B, odd j) = M - 2 * (i : ℤ) := by
        unfold odd at hsum
        unfold M
        linarith only [hsum]
      rw [hsum']
      unfold f
      ring
  have hcard : (Icc 0 M).card = (h + 1) ^ 2 := by
    rw [Int.card_Icc]
    have he : M + 1 - 0 = (((h + 1) ^ 2 : ℕ) : ℤ) := by
      unfold M
      push_cast
      ring
    rw [he, Int.toNat_natCast]
  exact (card_le_card hsubset).trans (card_image_le.trans_eq hcard)

/-- **Restricted signed sumsets of arithmetic progressions with one more term than summands.**
Let $h \ge 3$ be a natural number and let $a_1 < a_2 < \cdots < a_{h+1}$ be positive integers that
form an arithmetic progression with common difference $d > 0$, that is, $a_{i+1} = a_i + d$ for
$1 \le i \le h$. Let $A = \{a_1, \ldots, a_{h+1}\}$ and let $h^{\wedge}_{\pm} A$ be the
restricted signed sumset of $A$. Then $|h^{\wedge}_{\pm} A| \ge (h+1)^2$ if $d = 2a_1$, and
$|h^{\wedge}_{\pm} A| \ge (h+1)^2 + 1$ otherwise. Moreover, $|h^{\wedge}_{\pm} A| = (h+1)^2$ if
and only if $d = 2a_1$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the
Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Theorem 3. -/
public theorem card_restrictedSignedSumset_ap_h_add_one
    (h : ℕ) (hh : 3 ≤ h) (a : Fin (h + 1) → ℤ) (d : ℤ)
    (ha : StrictMono a) (hpos : ∀ i, 0 < a i) (hap : IsIndexedAP a d) :
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) ≥
      if d = 2 * a ⟨0, by omega⟩ then ((h + 1 : ℕ) : ℤ) ^ 2
      else ((h + 1 : ℕ) : ℤ) ^ 2 + 1) ∧
    (((restrictedSignedSumset h (orderedFinset a)).card : ℤ) =
        ((h + 1 : ℕ) : ℤ) ^ 2 ↔ d = 2 * a ⟨0, by omega⟩) := by
  let b := a 0
  have hb : 0 < b := hpos 0
  have hd : 0 < d := by
    have h01 : a ⟨0, by omega⟩ < a ⟨1, by omega⟩ := ha (by
      change (0 : ℕ) < 1
      decide)
    rw [hap.2 ⟨0, by omega⟩ ⟨1, by omega⟩ rfl] at h01
    omega
  change (_ ≥ if d = 2 * b then _ else _) ∧ (_ = _ ↔ d = 2 * b)
  rw [show orderedFinset a = apFinset b d (h + 1) from orderedFinset_eq_ap hap]
  have hl := card_ap_signed_lower hb hd h hh
  by_cases he : d = 2 * b
  · have hl' : (h + 1) ^ 2 ≤ (restrictedSignedSumset h (apFinset b d (h + 1))).card := by
      simpa [he] using hl
    have hu := he ▸ card_ap_signed_upper hb h
    have hc : (restrictedSignedSumset h (apFinset b d (h + 1))).card = (h + 1) ^ 2 :=
      le_antisymm hu hl'
    have hcZ : ((restrictedSignedSumset h (apFinset b d (h + 1))).card : ℤ) =
        ((h + 1 : ℕ) : ℤ) ^ 2 := by exact_mod_cast hc
    rw [ite_eq_left he, hcZ]
    simp [he]
  · have hl' : ((h + 1 : ℕ) : ℤ) ^ 2 + 1 ≤
        ((restrictedSignedSumset h (apFinset b d (h + 1))).card : ℤ) := by
      exact_mod_cast (show (h + 1) ^ 2 + 1 ≤ _ by simpa [he] using hl)
    exact ⟨by simpa [he] using hl', ⟨fun hc => by omega, fun h => (he h).elim⟩⟩

end MetaMathlibExt
