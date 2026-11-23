/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsum
import all MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsum
import MathlibExt.Combinatorics.Words.FibonacciFactorization
import Mathlib.Tactic.FinCases

/-!
# Palindromes between upper Wythoff unsum markers

Read each Fibonacci block of the unsum recognizer as a list of gaps, starting at the
unsum three positions past the block boundary. The blocks have eight possible forms.
In the initial block, every completed word between markers is a singleton or a central
Fibonacci word flanked by two threes.
-/

namespace MetaMathlibExt.upperWythoffUnsumPalindrome_reverse

open upperWythoffUnsumPalindrome_head_getLast

-- Read false as 5 and true as 3. Removing the last two letters of letters (n + 1)
-- gives central n. Its omitted suffix alternates between 53 and 35.
private def letters (n : ℕ) : List ℕ := (fibWord n).map fun b => if b then 3 else 5

private theorem letters_rec (n : ℕ) : letters (n + 2) = letters (n + 1) ++ letters n := by
  simp [letters, fibWord_add_two]

private def central : ℕ → List ℕ
  | 0 => []
  | 1 => [5]
  | n + 2 => letters (n + 2) ++ central n

private theorem central_swap (n : ℕ) : central (n + 2) = letters (n + 1) ++ central (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change letters (n + 3) ++ central (n + 1) = letters (n + 2) ++ central (n + 2)
    rw [letters_rec (n + 1), List.append_assoc, ← ih]

private def ending : ℕ → List ℕ
  | 0 => [5, 3]
  | n + 1 => (ending n).reverse

private theorem letters_ending : ∀ n, letters (n + 1) = central n ++ ending n
  | 0 | 1 => rfl
  | n + 2 => by rw [letters_rec (n + 1), letters_ending n, central, ending, ending,
      List.reverse_reverse, List.append_assoc]

private theorem central_reverse : ∀ n, (central n).reverse = central n
  | 0 | 1 => rfl
  | n + 2 => by
    calc
      (central (n + 2)).reverse =
          central n ++ ending n ++ central (n + 1) := by
        rw [central, letters_ending (n + 1), List.reverse_append, List.reverse_append,
          central_reverse n, central_reverse (n + 1), ending, List.reverse_reverse,
          List.append_assoc]
      _ = central (n + 2) := by rw [← letters_ending, central_swap]

private def enclosed (w : List ℕ) : List ℕ := 3 :: w ++ [3]

private def blocks : ℕ → List (List ℕ)
  | 0 => [[3], [3], [3, 3]]
  | n + 1 => blocks n ++ [enclosed (central n), enclosed (central (n + 1))]

-- At level zero the gap list starts at unsum 3 (gap index 2). The eight gaps
-- before the first marker bring us to index 10. The final 3 starts the next word.
private def initialGaps (n : ℕ) : List ℕ :=
  [1, 1, 1, 2, 2, 1, 2, 1] ++ (blocks n).flatMap (2 :: ·) ++ [2, 3]

private theorem initialGaps_succ (n : ℕ) : initialGaps (n + 1) =
    initialGaps n ++ central n ++ [3, 2, 3] ++ central (n + 1) ++ [3, 2, 3] := by
  simp [initialGaps, blocks, enclosed, List.append_assoc]

-- Each row is classified by its base gaps and the classes of its children.
private def kind (i : RowIndex) : Fin 8 :=
  #[0, 0, 1, 1, 2, 2, 3, 4, 4, 5, 6, 5, 5, 7, 4, 7, 7, 4, 4, 7, 6, 5, 7, 6, 7, 6,
    5, 5, 7, 6, 7, 7, 4, 7, 6, 7, 7, 6, 7, 7, 4, 4, 7, 6, 7, 7, 6, 7, 6, 7, 6, 7,
    7, 6, 6, 5, 5, 7, 6, 7, 7, 6, 7, 6, 7, 4, 4, 7, 6, 6, 5, 5, 7, 4, 4][i.val]!

-- Cases 0, 1 and 2 contain the initial block or two marker endings. Cases 3, 4 and 5
-- contain one marker ending, and cases 6 and 7 are ordinary finite Fibonacci words.
-- A marker ending 323 completes one palindrome and starts the next.
private def gaps (n : ℕ) : Fin 8 → List ℕ
  | 0 => initialGaps n
  | 1 => central n ++ [3, 2, 3] ++ central (n + 1) ++ [3, 2, 3]
  | 2 => central (n + 1) ++ [3, 2, 3] ++ central (n + 2) ++ [3, 2, 3]
  | 3 => central (n + 2) ++ [3, 2, 3] ++ letters (n + 2)
  | 4 => central (n + 2) ++ [3, 2, 3]
  | 5 => central (n + 3) ++ [3, 2, 3]
  | 6 => letters (n + 3)
  | 7 => letters (n + 4)

private def childrenKinds : Fin 8 → Fin 8 × Option (Fin 8)
  | 0 => (0, some 1)
  | 1 => (2, none)
  | 2 => (3, some 4)
  | 3 => (5, some 6)
  | 4 => (5, none)
  | 5 => (7, some 4)
  | 6 => (7, none)
  | 7 => (7, some 6)

private theorem kind_step : ∀ i : RowIndex, childrenKinds (kind i) =
    (kind (nextRow i false), if (frame i).short then none else some (kind (nextRow i true))) := by
  decide +kernel

private theorem gaps_step (n : ℕ) (k : Fin 8) :
    gaps (n + 1) k = gaps n (childrenKinds k).1 ++
      ((childrenKinds k).2.elim [] (gaps n)) := by
  fin_cases k <;> simp only [childrenKinds, Option.elim, gaps, List.append_nil]
  · rw [initialGaps_succ]; simp [List.append_assoc]
  · rw [central_swap (n + 1)]; simp [List.append_assoc]
  · rw [central]; simp [List.append_assoc]
  · exact letters_rec _

-- The gaps describe exactly the marked positions of a predicate, including both endpoints.
private def Traces (u : ℕ → Prop) (x : ℕ) : List ℕ → Prop
  | [] => u x
  | d :: ds => 0 < d ∧ (∀ j < d, u (x + j) ↔ j = 0) ∧ Traces u (x + d) ds

private instance decidableTraces (u : ℕ → Prop) [DecidablePred u] (x : ℕ) (ds : List ℕ) :
    Decidable (Traces u x ds) := by
  induction ds generalizing x with
  | nil => exact inferInstanceAs (Decidable (u x))
  | cons d ds ih =>
    unfold Traces
    letI := ih (x + d)
    infer_instance

private theorem traces_start {u : ℕ → Prop} {x : ℕ} {ds : List ℕ} (h : Traces u x ds) : u x := by
  cases ds with
  | nil => exact h
  | cons d ds => simpa using (h.2.1 0 h.1).mpr rfl

private theorem traces_congr {u v : ℕ → Prop} {x y : ℕ} {ds : List ℕ} (h : Traces u x ds)
    (he : ∀ j ≤ ds.sum, u (x + j) ↔ v (y + j)) : Traces v y ds := by
  induction ds generalizing x y with
  | nil =>
    change u x at h
    change v y
    simpa using (he 0 (by simp)).mp (by simpa using h)
  | cons d ds ih =>
    simp only [List.sum_cons] at he
    refine ⟨h.1, fun j hj => (he j (by omega)).symm.trans (h.2.1 j hj), ih h.2.2 ?_⟩
    intro j hj
    simpa only [Nat.add_assoc] using he (d + j) (by omega)

private theorem traces_append {u : ℕ → Prop} {x : ℕ} {as bs : List ℕ}
    (ha : Traces u x as) (hb : Traces u (x + as.sum) bs) : Traces u x (as ++ bs) := by
  induction as generalizing x with
  | nil => simpa using hb
  | cons d as ih =>
    exact ⟨ha.1, ha.2.1, ih ha.2.2 (by simpa [Nat.add_assoc] using hb)⟩

private theorem base_gaps : ∀ i : RowIndex, (gaps 0 (kind i)).sum = width 0 (frame i).short ∧
    Traces (fun z => baseMissing (frame i) z = true) 1 (gaps 0 (kind i)) := by
  decide +kernel

private theorem frame_step (n : ℕ) (i : RowIndex) (x : Bool)
    (hx : ((frame i).short && x) = false) {z : ℕ} (hz : z < width n false + 8) :
    missing (n + 1) (frame i) (offset n x + z) ↔ missing n (frame (nextRow i x)) z := by
  rw [← transitions i x hx]
  exact missing_advance n (frame i) x hz

private theorem level_gaps (n : ℕ) (i : RowIndex) :
    (gaps n (kind i)).sum = width n (frame i).short ∧
      Traces (missing n (frame i)) 1 (gaps n (kind i)) := by
  induction n generalizing i with
  | zero =>
    obtain ⟨hlen, h⟩ := base_gaps i
    exact ⟨hlen, traces_congr h fun j _ => baseMissing_spec _ _⟩
  | succ n ih =>
    have childShort (x : Bool) (hx : ((frame i).short && x) = false) :
        (frame (nextRow i x)).short = x := by rw [← transitions i x hx]; rfl
    obtain ⟨hl, hleft⟩ := ih (nextRow i false)
    rw [childShort false (Bool.and_false _)] at hl
    have left := traces_congr (v := missing (n + 1) (frame i)) (y := 1) hleft
      (fun j hj => by
        simpa [offset] using (frame_step n i false (Bool.and_false _) (z := 1 + j) (by omega)).symm)
    rw [gaps_step, kind_step]
    cases hs : (frame i).short with
    | true =>
      simpa [hs, (widths n).2] using And.intro hl left
    | false =>
      have hx : ((frame i).short && true) = false := by simp [hs]
      obtain ⟨hr, hright⟩ := ih (nextRow i true)
      rw [childShort true hx] at hr
      have bounds := widthBounds n
      simp only [Bool.false_eq_true, ite_false, Option.elim, List.sum_append, hl, hr, (widths n).1,
        true_and]
      apply traces_append left
      apply traces_congr hright
      intro j hj
      rw [hl, show 1 + width n false + j = offset n true + (1 + j) by simp [offset]; omega]
      exact (frame_step n i true hx (by omega)).symm

-- Use the left child of a larger root so that the last unsum of the block is
-- still strictly inside the Fibonacci word where missing_root applies.
private theorem initial_trace (n : ℕ) : Traces IsUpperWythoffUnsum 3 (initialGaps n) := by
  obtain ⟨hlen, h⟩ := level_gaps n 1
  have hshort : (frame 1).short = false := by decide +kernel
  have hk : kind 1 = 0 := by decide
  rw [hk] at h hlen
  rw [hshort] at hlen
  change (initialGaps n).sum = width n false at hlen
  refine traces_congr h fun j hj => ?_
  change j ≤ (initialGaps n).sum at hj
  have hg := widthBounds n
  have hroot : frame 0 = root := by decide +kernel
  have ht := frame_step n 0 false (Bool.and_false _) (z := 1 + j) (by omega)
  rw [hroot] at ht
  simp only [offset, Bool.false_eq_true, ite_false, Nat.zero_add] at ht
  have hw := (widths n).1
  exact ht.symm.trans ((missing_root (n + 1) (1 + j) (by omega)).trans (by
    rw [show 1 + j + 2 = 3 + j by omega]))

private theorem next_nth {p : ℕ → Prop} (hp : (Set.ofPred p).Infinite) {k x d : ℕ}
    (hk : Nat.nth p k = x) (hd : 0 < d) (hend : p (x + d))
    (hmid : ∀ j < d, p (x + j) → j = 0) : Nat.nth p (k + 1) = x + d := by
  have hle := (Nat.nth_add_one_le_iff hp hend).mpr (by omega : Nat.nth p k < x + d)
  have hlt : Nat.nth p k < Nat.nth p (k + 1) := Nat.nth_strictMono hp (Nat.lt_succ_self k)
  by_contra! h
  let j := Nat.nth p (k + 1) - x
  have he : x + j = Nat.nth p (k + 1) := by dsimp [j]; omega
  have := hmid j (by omega) (he ▸ Nat.nth_mem_of_infinite hp (k + 1))
  omega

private def Reads (k : ℕ) (ds : List ℕ) : Prop :=
  (List.range' k ds.length).map upperWythoffUnsumGap = ds

private theorem reads_cons {k d : ℕ} {ds : List ℕ} :
    Reads k (d :: ds) ↔ upperWythoffUnsumGap k = d ∧ Reads (k + 1) ds := by
  simp [Reads, List.range'_succ]

private theorem reads_split {k : ℕ} {as bs : List ℕ} (h : Reads k (as ++ bs)) :
    Reads k as ∧ Reads (k + as.length) bs := by
  unfold Reads at *
  rw [List.length_append, ← List.range'_append_1, List.map_append] at h
  exact List.append_inj h (by simp)

private theorem reads_trace {k x : ℕ} {ds : List ℕ} (hk : unsum k = x)
    (h : Traces IsUpperWythoffUnsum x ds) : Reads k ds := by
  induction ds generalizing k x with
  | nil => rfl
  | cons d ds ih =>
    have he := next_nth infiniteUnsums hk h.1 (traces_start h.2.2) (fun j hj => (h.2.1 j hj).mp)
    refine reads_cons.mpr ⟨?_, ih he h.2.2⟩
    change unsum (k + 1) - unsum k = d
    rw [show unsum (k + 1) = x + d from he, hk, Nat.add_sub_cancel_left]

private theorem central_no_two (n : ℕ) : 2 ∉ central n := by
  have h : 2 ∉ letters (n + 1) := by simp [letters, List.mem_map]
  rw [letters_ending] at h
  exact fun hc => h (List.mem_append_left _ hc)

private theorem blocks_spec (n : ℕ) : ∀ w ∈ blocks n, w.reverse = w ∧ 2 ∉ w := by
  induction n with
  | zero => decide
  | succ n ih =>
    intro w hw
    simp only [blocks, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | rfl | rfl
    · exact ih w h
    all_goals simp [enclosed, central_reverse, central_no_two]

private theorem blocks_length (n : ℕ) : (blocks n).length = 2 * n + 3 := by
  induction n with
  | zero => decide
  | succ n ih => simp [blocks, ih, Nat.mul_add]

-- Enumerate the delimiters of the explicit list of blocks using the same nth operation
-- as the definition of the markers. The extra 2 at the end closes the last block.
private theorem read_words {ws : List (List ℕ)} {j a : ℕ}
    (h : Reads a (ws.flatMap (2 :: ·) ++ [2, 3])) (ha : upperWythoffUnsumMarker j = a)
    (hws : ∀ w ∈ ws, 2 ∉ w) {t : ℕ} (ht : t < ws.length) :
    upperWythoffUnsumWord (j + t) = ws[t] := by
  induction ws generalizing j a t with
  | nil => simp at ht
  | cons w ws ih =>
    change Reads a (2 :: ((w ++ ws.flatMap (2 :: ·)) ++ [2, 3])) at h
    rw [List.append_assoc] at h
    obtain ⟨hw, hrest⟩ := reads_split (reads_cons.mp h).2
    have h2 : upperWythoffUnsumGap (a + 1 + w.length) = 2 := by
      cases ws with
      | nil => exact (reads_cons.mp hrest).1
      | cons w' ws => exact (reads_cons.mp hrest).1
    have ha10 : 10 ≤ a := by
      rw [← ha]
      exact (Nat.nth_mem_of_infinite infiniteMarkers j).1
    have hn := next_nth infiniteMarkers ha (d := 1 + w.length) (by omega)
      (show IsUpperWythoffUnsumMarker (a + (1 + w.length)) from
        ⟨by omega, by simpa [Nat.add_assoc] using h2⟩) (by
        intro s hs hm
        by_contra! hne
        have hg : upperWythoffUnsumGap (a + s) ∈ w := by
          rw [← hw]
          exact List.mem_map_of_mem (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        exact (hws w List.mem_cons_self) (hm.2 ▸ hg))
    change upperWythoffUnsumMarker (j + 1) = _ at hn
    cases t with
    | zero =>
      change upperWythoffUnsumWord j = w
      rw [upperWythoffUnsumWord, ha, hn, show a + (1 + w.length) - a - 1 = w.length by omega]
      exact hw
    | succ t =>
      rw [show j + (t + 1) = j + 1 + t by omega]
      exact ih hrest (by simpa [Nat.add_assoc] using hn)
        (fun v hv => hws v (List.mem_cons_of_mem _ hv)) (by simpa using ht)

private theorem _root_.MetaMathlibExt.upperWythoffUnsumPalindrome_tendsto.word_eq_block
    {n j : ℕ} (hj : j < (blocks n).length) : upperWythoffUnsumWord j = (blocks n)[j] := by
  have h₃ : unsum 2 = 3 := nth_unsum (by decide) (by decide +kernel) (by decide +kernel)
  have h := reads_trace h₃ (initial_trace n)
  unfold initialGaps at h
  have hblocks : Reads 10 ((blocks n).flatMap (2 :: ·) ++ [2, 3]) := by
    rw [List.append_assoc] at h
    exact (reads_split h).2
  simpa only [Nat.zero_add] using read_words hblocks upperWythoffUnsumMarker_zero_one.1
    (fun w h => (blocks_spec n w h).2) hj

private theorem word_reverse (j : ℕ) :
    (upperWythoffUnsumWord j).reverse = upperWythoffUnsumWord j := by
  have hj : j < (blocks j).length := by rw [blocks_length]; omega
  have hw := upperWythoffUnsumPalindrome_tendsto.word_eq_block hj
  rw [hw]
  exact (blocks_spec j _ (List.getElem_mem _)).1

end MetaMathlibExt.upperWythoffUnsumPalindrome_reverse

namespace MetaMathlibExt

/-- **The gap words are palindromes.** Let $g_k$ be the $k$-th gap between
consecutive unsums (OEIS A260317), counted from zero, and let $m_0 < m_1 < \cdots$ be the
markers, the indices $k \ge 10$ with $g_k = 2$, in increasing order. For $i \ge 1$ let $W_i$
be the word of the gaps $g_k$ with $m_{2i-2} < k < m_{2i-1}$, in increasing order of $k$. Then
for every $i \ge 1$, the word $W_i$ read backwards is $W_i$ itself.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 4 (`jis-2025-25.3.8-lem-4`). -/
public theorem upperWythoffUnsumPalindrome_reverse {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).reverse = upperWythoffUnsumPalindrome i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa only [upperWythoffUnsumPalindrome, Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_left]
    using upperWythoffUnsumPalindrome_reverse.word_reverse (2 * k)

end MetaMathlibExt
