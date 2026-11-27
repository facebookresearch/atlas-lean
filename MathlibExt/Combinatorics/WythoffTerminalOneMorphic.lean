/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WythoffTerminalPositions
import Mathlib.Data.List.Chain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord

/-!
# Morphic coding of the level-one Wythoff mex pairs

The theorem `wythoffTerminal_one_morphic` constructs the limit of the five-letter
substitution and identifies its coded letters at both mex coordinates.
-/

namespace MetaMathlibExt
namespace wythoffTerminal_one_morphic

private def subst : Fin 5 → List (Fin 5) := ![[0, 1], [2], [3, 4], [3, 1], [2]]

private def code : Fin 5 → Bool := fun c => decide (c ∈ ({0, 1, 3} : Finset (Fin 5)))

private def isB (c : Fin 5) : Bool := !code c

private def short (c : Fin 5) : Bool := decide ((subst c).length = 1)

private def word (k : ℕ) : List (Fin 5) := morphIterate subst k [0]

private theorem word_succ (k : ℕ) : word (k + 1) = morphExtend subst (word k) := rfl

private theorem short_subst : ∀ c : Fin 5, (subst c).map short = fibSubst (short c) := by decide

private theorem short_image (v : List (Fin 5)) :
    (morphExtend subst v).map short = fibMorph (v.map short) := by
  induction v with
  | nil => rfl
  | cons c v ih =>
    change (subst c ++ morphExtend subst v).map short = fibSubst (short c) ++ fibMorph _
    rw [List.map_append, short_subst, ih]

private theorem short_word (k : ℕ) : (word k).map short = fibWord k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [word_succ, short_image, ih, fibWord]

private theorem word_length (k : ℕ) : k + 1 ≤ (word k).length := by
  simpa only [← short_word k, List.length_map] using fibWord_length k

private theorem word_prefix_succ (k : ℕ) : word k <+: word (k + 1) := by
  induction k with
  | zero => exact ⟨[1], rfl⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨morphExtend subst v, by
      calc
        _ = morphExtend subst (word k ++ v) := (morphExtend_append subst _ _).symm
        _ = _ := by rw [hv, ← word_succ]⟩

private theorem word_prefix {k l : ℕ} (h : k ≤ l) : word k <+: word l := by
  induction l, h using Nat.le_induction with
  | base => exact ⟨[], List.append_nil _⟩
  | succ l _ ih => exact ih.trans (word_prefix_succ l)

private theorem omegaLimit : ∃ w : ℕ → Fin 5, IsOmegaLimit subst 0 w := by
  refine ⟨fun i => (word i)[i]'(word_length i), fun M => ⟨M, Nat.le_of_succ_le (word_length M)⟩,
    fun k i hi => ?_⟩
  rcases le_total k i with h | h
  · exact (word_prefix h).getElem hi
  · exact ((word_prefix h).getElem (word_length i)).symm

-- The two projections differ by a shift. The boundary lists record the pending
-- letters when comparing the two substituted binary words from left to right.
private def before : Fin 5 → List Bool := ![[false], [true], [false, true], [false], [true]]

private def after : Fin 5 → List Bool := ![[true], [false, true], [false], [true], [false]]

private abbrev Joins (a b : Fin 5) : Prop := after a = before b

private theorem boundary : ∀ c : Fin 5,
    before c ++ fibSubst (isB c) = (subst c).map isB ++ after c := by decide

private theorem chain_subst (c : Fin 5) : (subst c).IsChain Joins := by
  fin_cases c <;> decide

private theorem joins_subst : ∀ a b : Fin 5, Joins a b →
    ∀ x : Fin 5, x ∈ (subst a).getLast? → ∀ y : Fin 5, y ∈ (subst b).head? → Joins x y := by
  decide

private theorem head_image (c : Fin 5) (v : List (Fin 5)) :
    (morphExtend subst (c :: v)).head? = (subst c).head? := by
  change (subst c ++ morphExtend subst v).head? = _
  rw [List.head?_append]
  fin_cases c <;> rfl

private theorem chain_image : ∀ {v : List (Fin 5)}, v.IsChain Joins →
    (morphExtend subst v).IsChain Joins
  | [], _ => List.isChain_nil
  | [a], _ => by simpa [morphExtend] using chain_subst a
  | a :: b :: v, h => by
    obtain ⟨hab, hb⟩ := List.isChain_cons_cons.mp h
    change (subst a ++ morphExtend subst (b :: v)).IsChain Joins
    apply (chain_subst a).append (chain_image hb)
    rw [head_image]
    exact joins_subst a b hab

private theorem code_image (a : Fin 5) (v : List (Fin 5)) (h : (a :: v).IsChain Joins) :
    ∃ tail, (morphExtend subst (a :: v)).map isB ++ tail =
      before a ++ fibMorph ((a :: v).map isB) := by
  induction v generalizing a with
  | nil => exact ⟨after a, by simpa [morphExtend, fibMorph] using (boundary a).symm⟩
  | cons b v ih =>
    obtain ⟨hab, hb⟩ := List.isChain_cons_cons.mp h
    obtain ⟨tail, ht⟩ := ih b hb
    refine ⟨tail, ?_⟩
    change ((subst a ++ morphExtend subst (b :: v)).map isB) ++ tail =
      before a ++ (fibSubst (isB a) ++ fibMorph ((b :: v).map isB))
    rw [List.map_append, List.append_assoc, ht, ← List.append_assoc, ← hab, ← List.append_assoc,
      ← boundary, List.append_assoc]

private theorem word_chain (k : ℕ) : (word k).IsChain Joins := by
  induction k with
  | zero => exact List.IsChain.singleton _
  | succ k ih => exact chain_image ih

private theorem code_prefix (k : ℕ) :
    fibWord k <+: [false, true] ++ (word k).map isB := by
  induction k with
  | zero => exact ⟨[true, false], rfl⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := word_prefix (Nat.zero_le k)
    change 0 :: v = word k at hv
    obtain ⟨tail, ht⟩ := code_image 0 v (hv ▸ word_chain k)
    rw [hv, ← word_succ] at ht
    obtain ⟨s, hs⟩ := ih
    have hp : fibWord (k + 1) <+: ([false, true] ++ (word (k + 1)).map isB) ++ tail := by
      refine ⟨fibMorph s, ?_⟩
      calc
        _ = fibMorph (fibWord k ++ s) := by rw [fibMorph_append, ← fibWord]
        _ = fibMorph ([false, true] ++ (word k).map isB) := congrArg fibMorph hs
        _ = [false, true] ++ (false :: fibMorph ((word k).map isB)) := rfl
        _ = _ := by rw [List.append_assoc, ht]; rfl
    apply List.prefix_of_prefix_length_le hp (List.prefix_append _ _)
    rw [← short_word (k + 1), List.length_append, List.length_map, List.length_map]
    omega

private theorem code_limit {w : ℕ → Fin 5} (hw : IsOmegaLimit subst 0 w) (i : ℕ) :
    fibInf (i + 2) = isB (w i) := by
  have hlen := word_length (i + 2)
  have hi : i < (word (i + 2)).length := by omega
  have hf : i + 2 < (fibWord (i + 2)).length := by
    simpa only [← short_word, List.length_map] using Nat.lt_of_succ_le hlen
  have h := (code_prefix (i + 2)).getElem hf
  rw [List.getElem_append_right (by simp)] at h
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel] at h
  have hwi : (word (i + 2))[i] = w i := hw.2 (i + 2) i hi
  rw [List.getElem_map, hwi] at h
  rw [← fibInf_agrees (i + 2) (i + 2) hf, List.getD_eq_getElem _ _ hf]
  exact h

-- In the Fibonacci substitution, every block begins with a zero, and it
-- contains a one just when the input letter is zero.
private def blockStart : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockStart n + (fibSubst (fibInf n)).length

private theorem blockStart_succ (n : ℕ) :
    blockStart (n + 1) = blockStart n + (if fibInf n then 1 else 2) := by
  cases h : fibInf n <;> simp [blockStart, h, fibSubst]

private theorem blockStart_strictMono : StrictMono blockStart := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [blockStart_succ]
  split <;> omega

private theorem blockStart_take (k n : ℕ) (h : n ≤ (fibWord k).length) :
    (fibMorph ((fibWord k).take n)).length = blockStart n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : n < (fibWord k).length := h
    have hbit : (fibWord k)[n] = fibInf n := by
      simpa only [List.getD_eq_getElem _ _ hi] using fibInf_agrees k n hi
    rw [List.take_succ_eq_append_getElem hi, fibMorph_append, List.length_append,
      ih hi.le, hbit]
    simp [fibMorph, blockStart]

private theorem block_get (n i : ℕ) (hi : i < (fibSubst (fibInf n)).length) :
    fibInf (blockStart n + i) = (fibSubst (fibInf n))[i] := by
  have hn : n < (fibWord n).length := fibWord_length n
  have hbit : (fibWord n)[n] = fibInf n := by
    simpa only [List.getD_eq_getElem _ _ hn] using fibInf_agrees n n hn
  have hp : fibMorph ((fibWord n).take n) ++ fibSubst (fibInf n) <+: fibWord (n + 1) := by
    refine ⟨fibMorph ((fibWord n).drop (n + 1)), ?_⟩
    rw [fibWord, ← hbit]
    conv_rhs =>
      rw [← List.take_append_drop (n + 1) (fibWord n), fibMorph_append,
        List.take_succ_eq_append_getElem hn, fibMorph_append]
    simp [fibMorph]
  have hstart := blockStart_take n n hn.le
  have hb : blockStart n + i <
      (fibMorph ((fibWord n).take n) ++ fibSubst (fibInf n)).length := by
    simpa [hstart] using Nat.add_lt_add_left hi (blockStart n)
  have hf : blockStart n + i < (fibWord (n + 1)).length := hb.trans_le hp.length_le
  rw [← fibInf_agrees (n + 1) _ hf, List.getD_eq_getElem _ _ hf, ← hp.getElem hb,
    List.getElem_append_right (by omega)]
  simp only [hstart, Nat.add_sub_cancel_left]

private theorem zero_at_start (n : ℕ) : fibInf (blockStart n) = false := by
  have h := block_get n 0 (by cases fibInf n <;> decide)
  cases hb : fibInf n <;> simpa [hb, fibSubst] using h

private theorem one_after_start {n : ℕ} (h : fibInf n = false) :
    fibInf (blockStart n + 1) = true := by
  simpa [h, fibSubst] using block_get n 1 (by simp [h, fibSubst])

-- The start of block `blockStart n` is shifted by `n`: each intervening
-- block of the first substitution contributes exactly one zero.
private theorem blockStart_twice (n : ℕ) :
    blockStart (blockStart n) = blockStart n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [blockStart_succ n]
    cases h : fibInf n with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [blockStart_succ (blockStart n + 1), blockStart_succ (blockStart n),
        zero_at_start, one_after_start h, ih]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      omega
    | true =>
      simp only [ite_true]
      rw [blockStart_succ (blockStart n), zero_at_start, ih]
      simp only [Bool.false_eq_true, ite_false]
      omega

private theorem block_cover (m : ℕ) :
    ∃ k, blockStart k ≤ m ∧ m < blockStart (k + 1) := by
  induction m with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨k, hlo, hhi⟩ := ih
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hhi) with hlt | heq
    · exact ⟨k, by omega, hlt⟩
    · change m + 1 = blockStart (k + 1) at heq
      exact ⟨k + 1, heq.ge, heq.symm ▸ blockStart_strictMono (Nat.lt_succ_self (k + 1))⟩

private theorem position_cases (m : ℕ) :
    (∃ k, m = blockStart k) ∨ (∃ k, m = blockStart k + 1 ∧ fibInf k = false) := by
  obtain ⟨k, hlo, hhi⟩ := block_cover m
  by_cases h : m = blockStart k
  · exact Or.inl ⟨k, h⟩
  rw [blockStart_succ] at hhi
  cases hb : fibInf k <;> simp [hb] at hhi
  · exact Or.inr ⟨k, by omega, hb⟩
  · omega

private def lower (n : ℕ) : ℕ := blockStart (n + 1)

private def upper (n : ℕ) : ℕ := lower n + n + 2

private theorem lower_strictMono : StrictMono lower :=
  fun _ _ h => blockStart_strictMono (Nat.succ_lt_succ h)

private theorem lower_least (n : ℕ) : 2 ≤ lower n :=
  lower_strictMono.monotone (Nat.zero_le n)

private theorem fibInf_upper (n : ℕ) : fibInf (upper n) = true := by
  unfold upper lower
  rw [show blockStart (n + 1) + n + 2 = blockStart (blockStart (n + 1)) + 1 by
    rw [blockStart_twice]; omega]
  exact one_after_start (zero_at_start (n + 1))

private theorem coords_cover {m : ℕ} (hm : 2 ≤ m) :
    (∃ n, m = lower n) ∨ (∃ n, m = upper n) := by
  rcases position_cases m with ⟨k, hk⟩ | ⟨k, hk, hb⟩
  · cases k with
    | zero => simp [blockStart] at hk; omega
    | succ n => exact Or.inl ⟨n, hk⟩
  · obtain ⟨j, hj⟩ : ∃ j, k = blockStart j := by
      rcases position_cases k with h | ⟨j, hj, hf⟩
      · exact h
      · rw [hj, one_after_start hf] at hb
        contradiction
    rw [hj, blockStart_twice] at hk
    cases j with
    | zero =>
      simp only [blockStart, Nat.add_zero, Nat.zero_add] at hk
      omega
    | succ n => exact Or.inr ⟨n, by unfold upper lower; omega⟩

private theorem mex_eq (n : ℕ) : wythoffMexA 1 n = lower n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [wythoffMexA]
    let s : Set ℕ := {m | 1 < m ∧ ∀ i : Fin n,
      m ≠ wythoffMexA 1 i ∧ m ≠ wythoffMexA 1 i + i + 1 + 1}
    change sInf s = lower n
    have hmem : lower n ∈ s := by
      refine ⟨lower_least n, fun i => ?_⟩
      rw [ih i i.isLt, show lower i + (i : ℕ) + 1 + 1 = upper i by rfl]
      refine ⟨ne_of_gt (lower_strictMono i.isLt), fun heq => ?_⟩
      have h := zero_at_start (n + 1)
      change fibInf (lower n) = false at h
      rw [heq, fibInf_upper] at h
      contradiction
    have hmin : ∀ m ∈ s, lower n ≤ m := by
      intro m hm
      rcases coords_cover hm.1 with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · by_contra! h
        have hi : i < n := lower_strictMono.lt_iff_lt.mp h
        exact (hm.2 ⟨i, hi⟩).1 (ih i hi).symm
      · by_contra! h
        have hlo : lower i ≤ upper i := by unfold upper; omega
        have hi : i < n := lower_strictMono.lt_iff_lt.mp (hlo.trans_lt h)
        exact (hm.2 ⟨i, hi⟩).2 (by rw [ih i hi]; rfl)
    exact le_antisymm (Nat.sInf_le hmem) (hmin _ (Nat.sInf_mem ⟨_, hmem⟩))

end wythoffTerminal_one_morphic

open wythoffTerminal_one_morphic in
/-- **Morphic coding of the Wythoff mex pairs at level one.** Let $a_n$ be the least natural
number $m > 1$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 2$,
so that $(a_0, b_0) = (2, 4)$. Let $f_1$ be the morphism on the alphabet $\{0, 1, 2, 3, 4\}$
given by $0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 3\,1$, $4 \mapsto 2$ and
extended to finite words by concatenation, and let $g_1$ send the letters $0, 1, 3$ to $a$ and
the letters $2, 4$ to $b$. Then there is an infinite word $w = w(0)\,w(1)\,w(2) \cdots$ over this
alphabet that is the limit of the iterates $f_1^k(0)$ (each $f_1^k(0)$ is a prefix of $w$, and
their lengths are unbounded), and for every such $w$ and every $n \ge 0$, $g_1(w(a_n - 2)) = a$
and $g_1(w(b_n - 2)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^1$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 1$; indexing the letters of $w$ from $2$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 22 (`jis-2026-26.1.6-prop-22`). -/
public theorem wythoffTerminal_one_morphic (n : ℕ) :
    let f₁ : Fin 5 → List (Fin 5) := ![[0, 1], [2], [3, 4], [3, 1], [2]]
    let g₁ : Fin 5 → Bool := fun c => decide (c ∈ ({0, 1, 3} : Finset (Fin 5)))
    (∃ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w) ∧
      ∀ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w →
        g₁ (w (wythoffMexA 1 n - 2)) = true ∧ g₁ (w (wythoffMexB 1 n - 2)) = false := by
  change (∃ w : ℕ → Fin 5, IsOmegaLimit subst 0 w) ∧
    ∀ w : ℕ → Fin 5, IsOmegaLimit subst 0 w →
      code (w (wythoffMexA 1 n - 2)) = true ∧ code (w (wythoffMexB 1 n - 2)) = false
  refine ⟨omegaLimit, fun w hw => ?_⟩
  have ha : wythoffMexA 1 n = lower n := mex_eq n
  have hb : wythoffMexB 1 n = upper n := by rw [wythoffMexB, ha]; rfl
  have hlo := lower_least n
  have hup : 2 ≤ upper n := by unfold upper; omega
  rw [ha, hb]
  have hA := code_limit hw (lower n - 2)
  have hB := code_limit hw (upper n - 2)
  rw [Nat.sub_add_cancel hlo, show fibInf (lower n) = false from zero_at_start (n + 1)] at hA
  rw [Nat.sub_add_cancel hup, fibInf_upper] at hB
  exact ⟨by simpa [isB] using hA.symm, by simpa [isB] using hB.symm⟩

end MetaMathlibExt
