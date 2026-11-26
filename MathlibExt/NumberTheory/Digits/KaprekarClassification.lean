/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Induction
import all Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# A classification of the decimal Kaprekar numbers

Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly 62
(2024), Article iwasaki06162024-ASrev2.

`D_n` is the set of `n`-digit strings of decimal digits (leading zeros allowed), i.e. the
numbers `α < 10^n` written with exactly `n` digits. The Kaprekar transformation sends
`α ∈ D_n` to `α_M - α_L`, where `α_M` and `α_L` arrange the `n` digits of `α` in descending and
ascending order; it depends only on the multiset of digits, and a nonzero `α` with
`f(α) = α` is a Kaprekar number. The value depends on `n`: `495` is a Kaprekar number in `D_3`,
but in `D_4` it is the string `0495` and is sent to `9540 - 0459 = 9081`.

The theorem `kaprekarMap_fixed_iff` characterizes the nonzero fixed points by five families
of digit strings.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Kaprekar difference.** Let $l$ be a list of $k$ natural numbers and let
$a_0 \le a_1 \le \dots \le a_{k-1}$ be its entries in increasing order. The Kaprekar difference of
$l$ is $\alpha_M - \alpha_L$, where $\alpha_M = \sum_{i<k} a_i 10^i$ and
$\alpha_L = \sum_{i<k} a_{k-1-i} 10^i$. When the entries are decimal digits, $\alpha_M$ is the
number written with the digits of $l$ in descending order and $\alpha_L$ is the number written
with them in ascending order (leading zeros allowed).

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarDiff (l : List ℕ) : ℕ :=
  Nat.ofDigits 10 (List.insertionSort (· ≤ ·) l) - Nat.ofDigits 10 (List.insertionSort (· ≥ ·) l)

/-- **Kaprekar map.** For natural numbers $n$ and $\alpha$, take the decimal digits of $\alpha$
(without leading zeros, and no digits at all for $\alpha = 0$) and, if there are fewer than $n$
of them, pad them with leading zeros to a string of exactly $n$ digits. The Kaprekar map sends
$\alpha$ to the Kaprekar difference $\alpha_M - \alpha_L$ of this digit string: the number with
these digits in descending order minus the number with them in ascending order. For
$\alpha < 10^n$ this is the Kaprekar transformation on the set $D_n$ of $n$-digit strings; for
$\alpha \ge 10^n$ nothing is padded and all digits of $\alpha$ are used.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public def kaprekarMap (n α : ℕ) : ℕ :=
  kaprekarDiff (Nat.digits 10 α ++ List.replicate (n - (Nat.digits 10 α).length) 0)

/-- **6174 is fixed by the four-digit Kaprekar map.** The Kaprekar map with $n = 4$ sends $6174$
to itself: $7641 - 1467 = 6174$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_four_6174 : kaprekarMap 4 6174 = 6174 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- **495 is fixed by the three-digit Kaprekar map.** The Kaprekar map with $n = 3$ sends $495$ to
itself: $954 - 459 = 495$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Section 1. -/
public theorem kaprekarMap_three_495 : kaprekarMap 3 495 = 495 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

/-- **The four-digit Kaprekar map sends 495 to 9081.** With $n = 4$, the number $495$ is padded to
the digit string $0495$, and the Kaprekar map sends it to $9540 - 0459 = 9081$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1. -/
public theorem kaprekarMap_four_495 : kaprekarMap 4 495 = 9081 := by
  norm_num [kaprekarMap, kaprekarDiff, List.insertionSort_cons, List.orderedInsert_cons,
    Nat.ofDigits_cons]

end

namespace kaprekarMap_fixed_iff

private abbrev Counts := ℕ → ℕ

private def copies (a k d : ℕ) := if a = d then k else 0

private def addPair (v : Counts) (a b k : ℕ) : Counts :=
  fun d => v d + copies a k d + copies b k d

private def balanced (h g : Counts) (big small c m : ℕ) : Prop :=
  ∀ d : ℕ, h d + copies c m d + copies (9 - big) 1 d + copies small 1 d =
    g d + copies 9 m d + copies (10 - big) 1 d + copies (small - 1) 1 d

/-- Read the smaller digits from the outside in, followed by the middle and the larger digits. -/
private def pairedDigits (c m : ℕ) : List (ℕ × ℕ) → List ℕ
  | [] => List.replicate m c
  | (a, b) :: ps => a :: (pairedDigits c m ps ++ [b])

/-- Subtract the reversal of a sorted digit string. The first column borrows from the
next, and the last unequal pair nearest the middle absorbs the borrow. -/
private def differenceDigits (m t : ℕ) : List (ℕ × ℕ) → List ℕ
  | [] => List.replicate m 9
  | (a, b) :: ps => (10 + a - b - t) ::
    (differenceDigits m 1 ps ++ [b - a - (if ps = [] then 1 else 0)])

private theorem length_out (c m t : ℕ) (ps : List (ℕ × ℕ)) :
    (differenceDigits m t ps).length = (pairedDigits c m ps).length := by
  induction ps generalizing t with
  | nil => simp [differenceDigits, pairedDigits]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp [differenceDigits, pairedDigits, ih]

private theorem ofDigits_nines (m : ℕ) : Nat.ofDigits 10 (List.replicate m 9) + 1 = 10 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ']
    omega

private theorem wrap_val (a b : ℕ) (l : List ℕ) :
    Nat.ofDigits 10 (a :: (l ++ [b])) = a + 10 * (Nat.ofDigits 10 l + 10 ^ l.length * b) := by
  rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton]

private theorem rev_wrap (a b : ℕ) (l : List ℕ) :
    (a :: (l ++ [b])).reverse = b :: (l.reverse ++ [a]) := by simp

private theorem out_correct (c m t : ℕ) (ps : List (ℕ × ℕ))
    (ht : t ≤ 1) (he : ps = [] → t = 1)
    (hps : ∀ p ∈ ps, p.1 < p.2 ∧ p.2 < 10) :
    Nat.ofDigits 10 (differenceDigits m t ps) + Nat.ofDigits 10 (pairedDigits c m ps).reverse + t =
      Nat.ofDigits 10 (pairedDigits c m ps) +
        (if ps = [] then 10 ^ (pairedDigits c m ps).length else 0) := by
  induction ps generalizing t with
  | nil =>
    have h := ofDigits_nines m
    simp [differenceDigits, pairedDigits, he rfl] at *
    omega
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hab, hb⟩ := hps _ (.head _)
    have h := ih 1 (by decide) (fun _ => rfl) (fun p hp => hps p (.tail _ hp))
    simp only [differenceDigits, pairedDigits, rev_wrap, wrap_val, List.length_reverse,
      length_out c, List.cons_ne_nil, ↓reduceIte, add_zero]
    dsimp at hab hb
    have hlo : 10 + a - b - t + b + t = 10 + a := by omega
    by_cases hnil : ps = []
    · simp only [hnil, ↓reduceIte] at *
      have hhi : b - a - 1 + a + 1 = b := by omega
      linear_combination hlo + 10 * h + 10 * 10 ^ (pairedDigits c m []).length * hhi
    · simp only [hnil, ↓reduceIte, Nat.sub_zero, add_zero] at *
      have hhi : b - a + a = b := by omega
      linear_combination hlo + 10 * h + 10 * 10 ^ (pairedDigits c m ps).length * hhi

private theorem out_lt (m t : ℕ) (ps : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, p.1 < p.2 ∧ p.2 < 10) : ∀ d ∈ differenceDigits m t ps, d < 10 := by
  induction ps generalizing t with
  | nil => simp [differenceDigits]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hab, hb⟩ := hps _ (.head _)
    simp only [differenceDigits, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    intro d hd
    rcases hd with rfl | hd | rfl
    · dsimp at *; omega
    · exact ih 1 (fun p hp => hps p (.tail _ hp)) _ hd
    · dsimp at *; omega

/-- The intervals determined by successively pairing the smallest and largest digits
are nested. Any digits left in the middle are equal. -/
private inductive Nested (c : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Prop where
  | nil {lo hi} : lo ≤ c → c ≤ hi → Nested c lo hi []
  | cons {lo hi a b ps} : lo ≤ a → a < b → b ≤ hi → Nested c a b ps →
      Nested c lo hi ((a, b) :: ps)

private theorem decompose {l : List ℕ} (hs : l.Pairwise (· ≤ ·)) {lo hi : ℕ}
    (hle : lo ≤ hi) (hl : ∀ d ∈ l, lo ≤ d ∧ d ≤ hi) :
    ∃ c m ps, l = pairedDigits c m ps ∧ Nested c lo hi ps := by
  induction l using List.bidirectionalRecOn generalizing lo hi with
  | H0 => exact ⟨lo, 0, [], rfl, .nil (by rfl) hle⟩
  | H1 a =>
    have ha := hl a (by simp)
    exact ⟨a, 1, [], rfl, .nil ha.1 ha.2⟩
  | Hn a l b ih =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    simp only [List.pairwise_cons, List.pairwise_append, List.mem_append, List.mem_singleton] at hs
    have hab := hs.1 b (Or.inr rfl)
    have hmid : ∀ d ∈ l, a ≤ d ∧ d ≤ b :=
      fun d hd => ⟨hs.1 d (Or.inl hd), hs.2.2.2 d hd b (by simp)⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · have heq : a :: (l ++ [a]) = List.replicate (l.length + 2) a := by
        apply List.eq_replicate_iff.mpr
        refine ⟨by simp, ?_⟩
        intro x hx
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | hx | rfl
        · rfl
        · exact (hmid x hx).2.antisymm (hmid x hx).1
        · rfl
      exact ⟨a, _, [], heq, .nil ha.1 ha.2⟩
    · obtain ⟨c, m, ps, heq, hn⟩ := ih hs.2.1 hab hmid
      exact ⟨c, m, (a, b) :: ps, by simp [pairedDigits, ← heq], .cons ha.1 hlt hb.2 hn⟩

private theorem Nested.bounds {c lo hi ps} (hn : Nested c lo hi ps) :
    ∀ p ∈ ps, lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ hi := by
  induction hn with
  | nil => simp
  | cons h₁ h₂ h₃ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h₁, h₂, h₃⟩
    · obtain ⟨ha, hab, hb⟩ := ih _ hp
      exact ⟨h₁.trans ha, hab, hb.trans h₃⟩

private theorem sorted_diff (l s : List ℕ) (hs : s.SortedLE) (hp : l.Perm s) :
    kaprekarDiff l = Nat.ofDigits 10 s - Nat.ofDigits 10 s.reverse := by
  have h₁ := (List.perm_insertionSort (· ≤ ·) l).trans hp
  have h₂ := ((List.perm_insertionSort (· ≥ ·) l).trans hp).trans s.reverse_perm.symm
  rw [kaprekarDiff, h₁.eq_of_sortedLE List.sortedLE_insertionSort hs,
    h₂.eq_of_sortedGE List.sortedGE_insertionSort hs.reverse]

private theorem padded_diff (l : List ℕ) (c m : ℕ) (ps : List (ℕ × ℕ)) (hp : ps ≠ [])
    (hs : (pairedDigits c m ps).SortedLE) (hl : l.Perm (pairedDigits c m ps))
    (hv : ∀ p ∈ ps, p.1 < p.2 ∧ p.2 < 10) :
    Nat.digitsAppend 10 l.length (kaprekarDiff l) = differenceDigits m 0 ps := by
  have h := out_correct c m 0 ps (by decide) (by simp [hp]) hv
  simp only [hp, ↓reduceIte, add_zero] at h
  rw [sorted_diff l _ hs hl, ← h, Nat.add_sub_cancel]
  exact (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 10) l.length).1
    ⟨(length_out c m 0 ps).trans hl.length_eq.symm, out_lt m 0 ps hv⟩

private abbrev Pair := ℕ × ℕ

private def gap (p : Pair) := p.2 - p.1

private def regular (p : Pair) : Pair := (gap p, 9 - gap p)

private def tally (f : Pair → Pair) (ps : List Pair) (d : ℕ) : ℕ :=
  (ps.map (fun p => copies (f p).1 1 d + copies (f p).2 1 d)).sum

private theorem count_cons' (d a : ℕ) (l : List ℕ) :
    (a :: l).count d = l.count d + copies a 1 d := by
  simp [List.count_cons, copies]

private theorem count_rep (d a m : ℕ) : (List.replicate m a).count d = copies a m d := by
  simp [List.count_replicate, copies]

private theorem input_count (ps : List Pair) (c m d : ℕ) :
    (pairedDigits c m ps).count d = tally id ps d + copies c m d := by
  induction ps with
  | nil => simp [pairedDigits, tally, count_rep]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp [pairedDigits, tally, count_cons', List.count_append, ih, add_comm,
      add_left_comm, add_assoc]

/-- Each pair with gap `g` normally contributes digits `g` and `9 - g`. Only the
outermost low digit and the innermost high digit require corrections. -/
private theorem output_count (p : Pair) (ps : List Pair) (m t d : ℕ) (ht : t ≤ 1)
    (hv : ∀ q ∈ p :: ps, q.1 < q.2 ∧ q.2 < 10) :
    (differenceDigits m t (p :: ps)).count d + copies (9 - gap p) 1 d +
      copies (gap (ps.getLastD p)) 1 d =
    tally regular (p :: ps) d + copies 9 m d + copies (10 - gap p - t) 1 d +
      copies (gap (ps.getLastD p) - 1) 1 d := by
  induction ps generalizing p t with
  | nil =>
    obtain ⟨a, b⟩ := p
    have ⟨hab, hb⟩ := hv _ (.head _)
    dsimp at hab hb
    have he : a + 10 - b = 10 - (b - a) := by omega
    simp [differenceDigits, tally, regular, gap, List.count_append, count_cons', count_rep, he,
      add_comm, add_left_comm, add_assoc]
  | cons q qs ih =>
    obtain ⟨a, b⟩ := p
    have ⟨hab, hb⟩ := hv _ (.head _)
    have ⟨hq, hq'⟩ := hv _ (.tail _ (.head _))
    dsimp at hab hb
    have heq : 10 - gap q - 1 = 9 - gap q := by omega
    have hind := ih q 1 (by decide) (fun r hr => hv r (.tail _ hr))
    rw [heq] at hind
    simp only [differenceDigits]
    change ((10 + a - b - t) :: (differenceDigits m 1 (q :: qs) ++ [b - a - 0])).count d + _ + _ = _
    simp only [show 10 + a - b = 10 - (b - a) by omega, Nat.sub_zero, count_cons',
      List.count_append, List.count_nil, zero_add, List.getLastD_cons] at *
    change _ = (copies (gap (a, b)) 1 d + copies (9 - gap (a, b)) 1 d +
      tally regular (q :: qs) d) + _ + _ + _
    simp only [gap] at *
    omega

private def familyOne (h : Counts) :=
  h 0 = 0 ∧ h 1 = 0 ∧ h 2 = 0 ∧ h 3 = 0 ∧ h 6 = 0 ∧ h 7 = 0 ∧ h 8 = 0 ∧
    h 4 = h 5 ∧ h 5 = h 9 ∧ 0 < h 9

private def familyTwo (h : Counts) :=
  h 0 = 0 ∧ h 2 = 0 ∧ h 5 = 0 ∧ h 8 = 0 ∧ h 9 = 0 ∧ h 1 = 1 ∧ h 7 = 1 ∧ h 4 = 1 ∧
    h 6 = h 3 + 1

private def familyThree (h : Counts) :=
  h 0 = 0 ∧ h 1 = h 2 ∧ h 2 = h 4 ∧ h 4 = h 5 ∧ h 5 = h 7 ∧ h 7 = h 8 ∧ h 8 = h 9 ∧
    h 3 = h 6 ∧ 0 < h 1 ∧ h 1 ≤ h 3

private def familyFour (h : Counts) :=
  h 0 = 0 ∧ h 1 = h 8 ∧ h 3 = h 6 ∧ h 4 = h 5 ∧ h 5 = h 9 ∧ h 2 = h 7 ∧
    h 4 + h 1 = 2 * h 3 ∧ h 2 + 2 * h 1 = 3 * h 3 ∧ 0 < h 1 ∧ h 1 < h 3

private def familyFive (h : Counts) :=
  h 1 = h 2 ∧ h 2 = h 4 ∧ h 4 = h 5 ∧ h 5 = h 7 ∧ h 7 = h 8 ∧ h 3 = h 6 ∧
    0 < h 0 ∧ h 0 ≤ h 9 ∧ h 9 < h 1 + h 0 ∧ h 9 ≤ h 3 + h 0

/-- The largest and smallest positive gaps distinguish the families. For gaps eight
and two, the counts of ones and nines distinguish the two possibilities. -/
private def classify (big small : ℕ) (v : Counts) : Prop :=
  match big, small with
  | 5, 5 => familyOne v
  | 6, 2 => familyTwo v
  | 8, 2 => if v 1 = v 9 then familyThree v else familyFour v
  | 9, 1 => familyFive v
  | _, _ => False

/-- At each interval, take `k` pairs of its endpoints. When a further pair remains,
at least one endpoint moves inwards. When pairing stops, the middle is a constant
string. Only the ranges and the middle digit are enumerated, with unrestricted
natural numbers for all multiplicities. -/
private def paths (big : ℕ) : ℕ → ℕ → Counts → Counts → Prop
  | 0, _, _, _ => True
  | depth + 1, lo, h, g =>
    ∀ k : ℕ, (depth + 1 = big → 0 < k) →
      let h' := addPair h lo (lo + (depth + 1)) k
      let g' := addPair g (depth + 1) (9 - (depth + 1)) k
      (0 < k → ∀ c, lo ≤ c → c ≤ lo + (depth + 1) → ∀ m,
        balanced h' g' big (depth + 1) c m → classify big (depth + 1)
          (fun d => h' d + copies c m d)) ∧
      paths big depth lo h' g' ∧ paths big depth (lo + 1) h' g'

private theorem Nested.center {lo hi c ps} (h : Nested c lo hi ps) : lo ≤ c ∧ c ≤ hi := by
  induction h with
  | nil hl hu => exact ⟨hl, hu⟩
  | cons hl _ hu _ ih => exact ⟨hl.trans ih.1, ih.2.trans hu⟩

private theorem Nested.dropRun {lo hi c k ps}
    (h : Nested c lo hi (List.replicate k (lo, hi) ++ ps)) : Nested c lo hi ps := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append] at h
    cases h with | cons _ _ _ tail => exact ih tail

private theorem splitRun {α : Type*} (p : α) (l : List α) :
    ∃ k qs, l = List.replicate k p ++ qs ∧ qs.head? ≠ some p := by
  classical
  induction l with
  | nil => exact ⟨0, [], rfl, by simp⟩
  | cons q qs ih =>
    by_cases h : q = p
    · obtain ⟨k, ts, rfl, h₁⟩ := ih
      exact ⟨k + 1, ts, by simp [List.replicate_succ, h], h₁⟩
    · exact ⟨0, q :: qs, rfl, by simpa⟩

private theorem tally_run (f : Pair → Pair) (k : ℕ) (p : Pair) (l : List Pair) (d : ℕ) :
    tally f (List.replicate k p ++ l) d =
      copies (f p).1 k d + copies (f p).2 k d + tally f l d := by
  simp only [tally, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate_nat]
  simp [copies, Nat.mul_add]

private def innerGap (l : List Pair) := gap (l.getLastD (0, 0))

private theorem getLastD_run {α : Type*} (k : ℕ) (p q : α) (ts : List α) (w : α) :
    (List.replicate k p ++ q :: ts).getLastD w = ts.getLastD q := by
  induction k generalizing w with
  | zero => exact List.getLastD_cons
  | succ k ih => simpa only [List.replicate_succ, List.cons_append, List.getLastD_cons] using ih p

private theorem getLastD_rep {α : Type*} {k : ℕ} (hk : 0 < k) (p w : α) :
    (List.replicate k p).getLastD w = p := by
  induction k generalizing w with
  | zero => omega
  | succ k ih =>
    rw [List.replicate_succ, List.getLastD_cons]
    cases k with
    | zero => rfl
    | succ k => exact ih (by omega) p

private theorem follow_path {big depth lo : ℕ} {h g : Counts} (checks : paths big depth lo h g)
    (hd : depth ≤ big) (ps : List Pair) (c m : ℕ) (hn : Nested c lo (lo + depth) ps)
    (hp : ps ≠ []) (ho : depth = big → ps.head? = some (lo, lo + depth))
    (hb : balanced (fun d => h d + tally id ps d) (fun d => g d + tally regular ps d)
      big (innerGap ps) c m) :
    classify big (innerGap ps) (fun d => h d + tally id ps d + copies c m d) := by
  induction depth generalizing lo h g ps with
  | zero =>
    obtain ⟨⟨a, b⟩, ts, rfl⟩ := List.exists_cons_of_ne_nil hp
    have ⟨ha, hab, hb'⟩ := hn.bounds _ (.head _)
    dsimp at *
    omega
  | succ depth ih =>
    let top : Pair := (lo, lo + (depth + 1))
    obtain ⟨k, qs, heq, hnext⟩ := splitRun top ps
    subst ps
    have hk : depth + 1 = big → 0 < k := by
      intro hbig
      have hh := ho hbig
      cases k with
      | zero => exact False.elim (hnext hh)
      | succ k => omega
    obtain ⟨stop, lower, upper⟩ := checks k hk
    have half := hn.dropRun
    have hg : gap top = depth + 1 := by simp [top, gap]
    -- Move the contribution of the outer run into the two accumulators.
    have push (f : Pair → Pair) (v : Counts) (d : ℕ) :
        v d + tally f (List.replicate k top ++ qs) d =
          addPair v (f top).1 (f top).2 k d + tally f qs d := by
      rw [tally_run, addPair]
      omega
    simp only [push, id_eq, regular, hg] at hb ⊢
    cases qs with
    | nil =>
      have hk' : 0 < k := by
        by_contra! hz
        simp [show k = 0 by omega] at hp
      have he : innerGap (List.replicate k top ++ []) = depth + 1 := by
        simp only [innerGap, List.append_nil, getLastD_rep hk', hg]
      simp only [he, tally, List.map_nil, List.sum_nil, add_zero] at hb ⊢
      exact stop hk' c half.center.1 half.center.2 m hb
    | cons q ts =>
      obtain ⟨a, b⟩ := q
      have he : innerGap (List.replicate k top ++ (a, b) :: ts) = innerGap ((a, b) :: ts) := by
        simp only [innerGap, getLastD_run, List.getLastD_cons]
      rw [he] at hb ⊢
      cases half with
      | cons ha hab hb' hn' =>
        by_cases hs : lo < a
        · apply ih upper (by omega) ((a, b) :: ts)
          · exact .cons hs hab (by omega) hn'
          · simp
          · omega
          · exact hb
        · have hlu : b ≤ lo + depth := by
            by_contra! hz
            apply hnext
            change some (a, b) = some (lo, lo + (depth + 1))
            rw [show a = lo by omega, show b = lo + (depth + 1) by omega]
          apply ih lower (by omega) ((a, b) :: ts)
          · exact .cons ha hab hlu hn'
          · simp
          · omega
          · exact hb

private inductive Form where
  | one (x : ℕ)
  | two (y : ℕ)
  | three (x y : ℕ)
  | four (x z : ℕ)
  | five (x z y w : ℕ)

private abbrev block (k : ℕ) (l : List ℕ) := (List.replicate k l).flatten

private def Form.word : Form → List ℕ
  | .one x => block x [4, 9, 5]
  | .two y => [6, 1, 7, 4] ++ block y [3, 6]
  | .three x y => block x [1, 2, 3, 4, 5, 6, 7, 8, 9] ++ block y [3, 6]
  | .four x z =>
    block x [1, 2, 3, 4, 5, 6, 7, 8, 9] ++ block z [3, 6] ++ block (2 * z) [4, 9, 5] ++
      block (3 * z) [2, 7]
  | .five x z y w =>
    block x [1, 2, 4, 5, 7, 8] ++ block z [0, 9] ++ block y [1, 2, 3, 4, 5, 6, 7, 8, 9] ++
      block w [3, 6]

private def Form.Valid : Form → Prop
  | .one x | .three x _ => 1 ≤ x
  | .two _ => True
  | .four x z | .five x z _ _ => 1 ≤ x ∧ 1 ≤ z

private theorem count_block (k : ℕ) (l : List ℕ) (d : ℕ) :
    (block k l).count d = k * l.count d := by
  induction k with
  | zero => simp [block]
  | succ k ih =>
    simpa only [block, List.replicate_succ, List.flatten_cons, List.count_append, Nat.succ_mul,
      add_comm] using congrArg (fun a => l.count d + a) ih

private theorem Form.digits_lt (f : Form) : ∀ d ∈ f.word, d < 10 := by
  cases f <;> simp [Form.word, block] <;> omega

private theorem perm_of_digit_counts {l s : List ℕ} (hl : ∀ d ∈ l, d < 10)
    (hs : ∀ d ∈ s, d < 10) (he : ∀ d < 10, l.count d = s.count d) : l.Perm s := by
  apply List.perm_iff_count.mpr
  intro d
  by_cases hd : d < 10
  · exact he d hd
  · rw [List.count_eq_zero_of_not_mem (fun h => hd (hl d h)),
      List.count_eq_zero_of_not_mem (fun h => hd (hs d h))]

local macro "compare_word" hl:ident : tactic => `(tactic|
  (apply perm_of_digit_counts (Form.digits_lt _) $hl
   intro d hd
   interval_cases d <;> simp +decide [Form.word, count_block] <;>
     dsimp +zetaDelta only at * <;> omega))

private theorem recover_form {big small : ℕ} (l : List ℕ) (hl : ∀ d ∈ l, d < 10)
    (hf : classify big small (fun d => l.count d)) :
    ∃ f : Form, f.Valid ∧ f.word.Perm l := by
  let v := fun d : ℕ => l.count d
  have h : familyOne v ∨ familyTwo v ∨ familyThree v ∨ familyFour v ∨ familyFive v := by
    unfold classify at hf
    split at hf
    · exact Or.inl hf
    · exact Or.inr (.inl hf)
    · split at hf
      · exact Or.inr (.inr (.inl hf))
      · exact Or.inr (.inr (.inr (.inl hf)))
    · exact Or.inr (.inr (.inr (.inr hf)))
    · contradiction
  rcases h with h | h | h | h | h
  · refine ⟨.one (v 9), ?_, ?_⟩
    all_goals unfold familyOne at h
    · dsimp [Form.Valid]
      omega
    · compare_word hl
  · refine ⟨.two (v 3), trivial, ?_⟩
    unfold familyTwo at h
    compare_word hl
  · refine ⟨.three (v 1) (v 3 - v 1), ?_, ?_⟩
    all_goals unfold familyThree at h
    · dsimp [Form.Valid]
      omega
    · compare_word hl
  · refine ⟨.four (v 1) (v 3 - v 1), ?_, ?_⟩
    all_goals unfold familyFour at h
    · constructor <;> omega
    · compare_word hl
  · refine ⟨.five (v 1 - (v 9 - v 0)) (v 0) (v 9 - v 0) (v 3 - (v 9 - v 0)), ?_, ?_⟩
    all_goals unfold familyFive at h
    · constructor <;> omega
    · compare_word hl

private abbrev Runs := List (Pair × ℕ)

private def expand : Runs → List Pair
  | [] => []
  | (p, k) :: rs => List.replicate k p ++ expand rs

private def fits (lo hi : ℕ) : Runs → Prop
  | [] => lo ≤ 5 ∧ 5 ≤ hi
  | ((a, b), _) :: rs => lo ≤ a ∧ a < b ∧ b ≤ hi ∧ fits a b rs

/-- Paired digits of each of the five words after sorting, from the extremes inwards. -/
private def Form.runs : Form → Runs
  | .one x => [((4, 9), x)]
  | .two y => [((1, 7), 1), ((3, 6), y), ((4, 6), 1)]
  | .three x y => [((1, 9), x), ((2, 8), x), ((3, 7), x), ((3, 6), y), ((4, 6), x)]
  | .four x z => [((1, 9), x), ((2, 9), 2 * z), ((2, 8), x), ((2, 7), z),
      ((3, 7), x + z), ((4, 7), z), ((4, 6), x + z)]
  | .five x z y w => [((0, 9), z), ((1, 9), y), ((1, 8), x), ((2, 8), y), ((2, 7), x),
      ((3, 7), y), ((3, 6), w), ((4, 6), y), ((4, 5), x)]

private def Form.middle : Form → ℕ
  | .one x | .three x _ => x
  | .two _ => 0
  | .four x z => x + 2 * z
  | .five _ _ y _ => y

private def Form.extremes : Form → Pair × Pair
  | .one _ => ((4, 9), (4, 9))
  | .two _ => ((1, 7), (4, 6))
  | .three _ _ | .four _ _ => ((1, 9), (4, 6))
  | .five _ _ _ _ => ((0, 9), (4, 5))

private theorem Nested.widen {lo hi a b c ps} (h : Nested c a b ps) (hl : lo ≤ a)
    (hu : b ≤ hi) : Nested c lo hi ps := by
  cases h with
  | nil ha hb => exact .nil (hl.trans ha) (hb.trans hu)
  | cons ha hab hb h => exact .cons (hl.trans ha) hab (hb.trans hu) h

private theorem fits_nested {rs lo hi} (h : fits lo hi rs) : Nested 5 lo hi (expand rs) := by
  induction rs generalizing lo hi with
  | nil => exact .nil h.1 h.2
  | cons r rs ih =>
    rcases r with ⟨⟨a, b⟩, k⟩
    obtain ⟨hl, hlt, hu, hr⟩ := h
    have tail := ih hr
    suffices h : Nested 5 a b (List.replicate k (a, b) ++ expand rs) from h.widen hl hu
    induction k with
    | zero => exact tail
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      exact .cons le_rfl hlt le_rfl ih

private theorem Nested.sorted {c lo hi ps} (hn : Nested c lo hi ps) (m : ℕ) :
    (pairedDigits c m ps).Pairwise (· ≤ ·) ∧ ∀ d ∈ pairedDigits c m ps, lo ≤ d ∧ d ≤ hi := by
  induction hn with
  | nil hl hu =>
    simp only [pairedDigits, List.pairwise_replicate, le_rfl, or_true, true_and]
    intro d hd
    rw [(List.mem_replicate.mp hd).2]
    exact ⟨hl, hu⟩
  | @cons lo hi a b ps hl hab hu _ ih =>
    obtain ⟨hp, hb⟩ := ih
    constructor
    · simp only [pairedDigits, List.pairwise_cons, List.pairwise_append, List.mem_append,
        List.mem_singleton, List.mem_nil_iff, List.Pairwise.nil]
      grind
    · simp only [pairedDigits, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      intro d hd
      rcases hd with rfl | hd | rfl
      · exact ⟨hl, hab.le.trans hu⟩
      · exact ⟨hl.trans (hb d hd).1, (hb d hd).2.trans hu⟩
      · exact ⟨hl.trans hab.le, hu⟩

private theorem Form.order (f : Form) : Nested 5 0 9 (expand f.runs) := by
  apply fits_nested
  cases f <;> norm_num [Form.runs, fits]

private theorem Form.ends (f : Form) (hf : f.Valid) :
    (expand f.runs).head? = some f.extremes.1 ∧
      (expand f.runs).getLast? = some f.extremes.2 := by
  cases f <;> simp only [Form.Valid] at hf <;>
    simp +contextual [Form.runs, Form.extremes, expand, List.getLast?_append,
      List.getLast?_replicate, List.head?_append, List.head?_replicate,
      show ∀ k : ℕ, 1 ≤ k → k ≠ 0 by omega] <;> grind

private theorem Form.input_counts (f : Form) (d : ℕ) (hd : d < 10) :
    f.word.count d = tally id (expand f.runs) d + copies 5 f.middle d := by
  cases f <;> interval_cases d <;> simp +decide [Form.runs, Form.word, Form.middle,
    expand, count_block, copies, tally] <;> omega

private theorem Form.balance (f : Form) :
    balanced (tally id (expand f.runs)) (tally regular (expand f.runs))
      (gap f.extremes.1) (gap f.extremes.2) 5 f.middle := by
  intro d
  by_cases hd : d < 10
  · cases f <;> interval_cases d <;>
      simp +decide [Form.runs, Form.middle, Form.extremes, expand, copies,
        tally, regular, gap] <;> omega
  · have hh (i : ℕ) (hi : i < 10) : i ≠ d := by omega
    cases f <;>
      simp [Form.runs, Form.extremes, expand, copies, tally,
        regular, gap, hh _ (by decide : 0 < 10), hh _ (by decide : 1 < 10),
        hh _ (by decide : 2 < 10), hh _ (by decide : 3 < 10), hh _ (by decide : 4 < 10),
        hh _ (by decide : 5 < 10), hh _ (by decide : 6 < 10), hh _ (by decide : 7 < 10),
        hh _ (by decide : 8 < 10), hh _ (by decide : 9 < 10)]

private theorem balance_iff (p : Pair) (ps : List Pair) (c m : ℕ)
    (hv : ∀ q ∈ p :: ps, q.1 < q.2 ∧ q.2 < 10) :
    balanced (tally id (p :: ps)) (tally regular (p :: ps))
      (gap p) (innerGap (p :: ps)) c m ↔
      (pairedDigits c m (p :: ps)).Perm (differenceDigits m 0 (p :: ps)) := by
  rw [List.perm_iff_count]
  unfold balanced
  refine forall_congr' fun d => ?_
  have ho := output_count p ps m 0 d (by decide) hv
  rw [input_count]
  simp only [innerGap, List.getLastD_cons, Nat.sub_zero] at *
  omega

private theorem diff_perm {l s : List ℕ} (h : l.Perm s) : kaprekarDiff l = kaprekarDiff s := by
  have hs := List.perm_insertionSort (· ≤ ·) s
  rw [sorted_diff l _ List.sortedLE_insertionSort (h.trans hs.symm),
    sorted_diff s _ List.sortedLE_insertionSort hs.symm]

private theorem Form.fixed (f : Form) (hv : f.Valid) :
    kaprekarMap f.word.length (kaprekarDiff f.word) = kaprekarDiff f.word := by
  obtain ⟨hf, hl⟩ := f.ends hv
  have hn := f.order
  have hb := f.balance
  have hc := f.input_counts
  cases he : expand f.runs with
  | nil => simp [he] at hf
  | cons p ps =>
    rw [he] at hf hl hn hb hc
    have h₁ : p = f.extremes.1 := Option.some.inj hf
    have h₂ : innerGap (p :: ps) = gap f.extremes.2 := by
      change gap ((p :: ps).getLast?.getD (0, 0)) = _
      rw [hl]
      rfl
    rw [← h₁, ← h₂] at hb
    have hps : ∀ q ∈ p :: ps, q.1 < q.2 ∧ q.2 < 10 :=
      fun q hq => ⟨(hn.bounds _ hq).2.1, (hn.bounds _ hq).2.2.trans_lt (by decide)⟩
    have hper := (balance_iff p ps 5 f.middle hps).mp hb
    obtain ⟨hord, hrange⟩ := hn.sorted f.middle
    have hinput : f.word.Perm (pairedDigits 5 f.middle (p :: ps)) := by
      apply perm_of_digit_counts f.digits_lt (fun d hd => (hrange d hd).2.trans_lt (by decide))
      simpa only [input_count] using hc
    have hpad := padded_diff f.word 5 f.middle (p :: ps) (by simp) hord.sortedLE hinput hps
    change kaprekarDiff (Nat.digitsAppend 10 f.word.length (kaprekarDiff f.word)) = _
    rw [hpad]
    exact diff_perm (hinput.trans hper).symm

private abbrev Checked := ∀ big lo : ℕ, 0 < big → lo + big ≤ 9 →
  paths big big lo (fun _ => 0) (fun _ => 0)

local macro "check_end" : tactic => `(tactic|
  (intro m bal
   have h0 := bal 0
   have h1 := bal 1
   have h2 := bal 2
   have h3 := bal 3
   have h4 := bal 4
   have h5 := bal 5
   have h6 := bal 6
   have h7 := bal 7
   have h8 := bal 8
   have h9 := bal 9
   clear bal
   simp +decide [addPair, copies, classify, familyOne, familyTwo, familyThree,
     familyFour, familyFive, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
     ↓reduceIte, add_zero, zero_add] at * <;>
   first | omega | (split <;> ((repeat' apply And.intro) <;> omega)) |
     ((repeat' apply And.intro) <;> omega)))

local syntax "check_paths" : tactic
local macro_rules | `(tactic| check_paths) => `(tactic|
  first | exact True.intro |
    (intro k hk
     dsimp only []
     constructor
     · intro hpos c hl hu
       interval_cases c <;> check_end
     · constructor <;> check_paths))

private abbrev AtGap (big : ℕ) := ∀ lo : ℕ, lo + big ≤ 9 →
  paths big big lo (fun _ => 0) (fun _ => 0)

local macro "check_gap" : tactic => `(tactic|
  (intro lo hl
   have hu := Nat.le_sub_of_add_le hl
   interval_cases lo <;> check_paths))

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 18 interval and middle-digit choices.
private theorem gap1 : AtGap 1 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 56 interval and middle-digit choices.
private theorem gap2 : AtGap 2 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 126 interval and middle-digit choices.
private theorem gap3 : AtGap 3 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 246 interval and middle-digit choices.
private theorem gap4 : AtGap 4 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 440 interval and middle-digit choices.
private theorem gap5 : AtGap 5 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 732 interval and middle-digit choices.
private theorem gap6 : AtGap 6 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 1122 interval and middle-digit choices.
private theorem gap7 : AtGap 7 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 1514 interval and middle-digit choices.
private theorem gap8 : AtGap 8 := by check_gap

set_option maxHeartbeats 50000000 in
-- Check the balance equations for all 1524 interval and middle-digit choices.
private theorem gap9 : AtGap 9 := by check_gap

private theorem checks : Checked := by
  intro big lo hb hu
  have hb' : big ≤ 9 := by omega
  interval_cases big
  · exact gap1 lo hu
  · exact gap2 lo hu
  · exact gap3 lo hu
  · exact gap4 lo hu
  · exact gap5 lo hu
  · exact gap6 lo hu
  · exact gap7 lo hu
  · exact gap8 lo hu
  · exact gap9 lo hu

private theorem fixed_form (checks : Checked) {n α : ℕ} (hα : α < 10 ^ n) (hα0 : α ≠ 0)
    (hfix : kaprekarMap n α = α) :
    ∃ f : Form, f.Valid ∧ f.word.Perm (Nat.digitsAppend 10 n α) := by
  let l := Nat.digitsAppend 10 n α
  let s := List.insertionSort (· ≤ ·) l
  have hs : s.SortedLE := List.sortedLE_insertionSort
  have hperm : s.Perm l := List.perm_insertionSort _ _
  have hl : ∀ d ∈ l, d < 10 := fun d => Nat.lt_of_mem_digitsAppend (by decide : 1 < 10) n d
  have hd : kaprekarDiff l = α := hfix
  obtain ⟨c, m, qs, hs', hn⟩ := decompose hs.pairwise (by decide : 0 ≤ 9)
    (fun d h => ⟨Nat.zero_le _, Nat.le_of_lt_succ (hl d (hperm.mem_iff.mp h))⟩)
  have hls : l.Perm (pairedDigits c m qs) := hs' ▸ hperm.symm
  rw [hs'] at hs
  cases qs with
  | nil =>
    rw [sorted_diff l _ hs hls] at hd
    simp [pairedDigits] at hd
    exact (hα0 hd.symm).elim
  | cons p ps =>
    obtain ⟨a, b⟩ := p
    have hv : ∀ q ∈ (a, b) :: ps, q.1 < q.2 ∧ q.2 < 10 :=
      fun q h => ⟨(hn.bounds q h).2.1, (hn.bounds q h).2.2.trans_lt (by decide)⟩
    have hp := padded_diff l c m ((a, b) :: ps) (by simp) hs hls hv
    rw [hd, Nat.length_digitsAppend (by decide) n hα] at hp
    have hop : (pairedDigits c m ((a, b) :: ps)).Perm (differenceDigits m 0 ((a, b) :: ps)) :=
      (show l = _ from hp) ▸ hls.symm
    have hb := (balance_iff (a, b) ps c m hv).mpr hop
    have ⟨hab, hb9⟩ := hv _ (.head _)
    dsimp at hab hb9
    have he : a + (b - a) = b := by omega
    have hn' : Nested c a (a + (b - a)) ((a, b) :: ps) := by
      rw [he]
      cases hn with | cons _ h _ rest => exact .cons le_rfl h le_rfl rest
    have hc := follow_path (checks (b - a) a (by omega) (by omega)) le_rfl ((a, b) :: ps) c m hn'
      (by simp) (by simp [he]) (by simpa [gap] using hb)
    have heq (d : ℕ) : l.count d = tally id ((a, b) :: ps) d + copies c m d := by
      rw [hls.count_eq, input_count]
    apply recover_form l hl
    simpa only [zero_add, ← heq] using hc

end kaprekarMap_fixed_iff

open kaprekarMap_fixed_iff in
set_option linter.unusedVariables false in
/-- **Classification of decimal Kaprekar numbers.** Let $n \ge 3$ and $0 < \alpha < 10^n$. Then
the Kaprekar map on $n$-digit strings fixes $\alpha$ if and only if $\alpha$ is the Kaprekar
difference of some string $s$ of exactly $n$ decimal digits of one of the following five forms,
where juxtaposition is concatenation, $(w)^k$ is the block $w$ repeated $k$ times, and in each
form the exponents are chosen independently with $x, x_1, x_2 \ge 1$ and $y, y_1, y_2 \ge 0$:
$(495)^x$; $6174\,(36)^y$; $(123456789)^x (36)^y$;
$(123456789)^{x_1} (36)^{x_2} (495)^{2x_2} (27)^{3x_2}$;
$(124578)^{x_1} (09)^{x_2} (123456789)^{y_1} (36)^{y_2}$.

The witness string must have length $n$: $495$ is the Kaprekar difference of $(495)^1$, but the
Kaprekar map on $4$-digit strings sends $495$ to $9081$.

Source: Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly
62 (2024), Article iwasaki06162024-ASrev2, Theorem 3.1. -/
public theorem kaprekarMap_fixed_iff {n α : ℕ} (hn : 3 ≤ n) (hα : α < 10 ^ n)
    (hα0 : α ≠ 0) :
    kaprekarMap n α = α ↔
      ∃ s : List ℕ, s.length = n ∧ kaprekarDiff s = α ∧
        ((∃ x, 1 ≤ x ∧ s = (List.replicate x [4, 9, 5]).flatten) ∨
          (∃ y, s = [6, 1, 7, 4] ++ (List.replicate y [3, 6]).flatten) ∨
          (∃ x y, 1 ≤ x ∧ s = (List.replicate x [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
            (List.replicate y [3, 6]).flatten) ∨
          (∃ x₁ x₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate x₂ [3, 6]).flatten ++ (List.replicate (2 * x₂) [4, 9, 5]).flatten ++
              (List.replicate (3 * x₂) [2, 7]).flatten) ∨
          (∃ x₁ x₂ y₁ y₂, 1 ≤ x₁ ∧ 1 ≤ x₂ ∧
            s = (List.replicate x₁ [1, 2, 4, 5, 7, 8]).flatten ++
              (List.replicate x₂ [0, 9]).flatten ++
              (List.replicate y₁ [1, 2, 3, 4, 5, 6, 7, 8, 9]).flatten ++
              (List.replicate y₂ [3, 6]).flatten)) := by
  constructor
  · intro h
    obtain ⟨f, hv, hp⟩ := fixed_form checks hα hα0 h
    refine ⟨f.word, hp.length_eq.trans (Nat.length_digitsAppend (by decide) n hα),
      (diff_perm hp).trans h, ?_⟩
    cases f with
    | one x => exact Or.inl ⟨x, hv, rfl⟩
    | two y => exact Or.inr (.inl ⟨y, rfl⟩)
    | three x y => exact Or.inr (.inr (.inl ⟨x, y, hv, rfl⟩))
    | four x z => exact Or.inr (.inr (.inr (.inl ⟨x, z, hv.1, hv.2, rfl⟩)))
    | five x z y w => exact Or.inr (.inr (.inr (.inr ⟨x, z, y, w, hv.1, hv.2, rfl⟩)))
  · rintro ⟨s, hlen, hd, hf⟩
    suffices ∃ f : Form, f.Valid ∧ s = f.word by
      obtain ⟨f, hv, rfl⟩ := this
      rw [← hlen, ← hd]
      exact f.fixed hv
    rcases hf with ⟨x, hx, rfl⟩ | ⟨y, rfl⟩ | ⟨x, y, hx, rfl⟩ | ⟨x, z, hx, hz, rfl⟩ |
      ⟨x, z, y, w, hx, hz, rfl⟩
    · exact ⟨.one x, hx, rfl⟩
    · exact ⟨.two y, trivial, rfl⟩
    · exact ⟨.three x y, hx, rfl⟩
    · exact ⟨.four x z, ⟨hx, hz⟩, rfl⟩
    · exact ⟨.five x z y w, ⟨hx, hz⟩, rfl⟩

end MetaMathlibExt
