/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Eq

@[expose] public section

namespace MetaMathlibExt

/-- Weight of a composition symbol: the two colors `0` and `1` of part one both
weigh one, while symbol `i ≥ 2` weighs `i`. -/
private def tccWt (k : ℕ) (a : Fin (k + 1)) : ℕ :=
  if a.val ≤ 1 then 1 else a.val

private lemma tccWt_pos (k : ℕ) (a : Fin (k + 1)) : 1 ≤ tccWt k a := by
  unfold tccWt
  split <;> omega

/-- Total weight of a list of composition symbols. -/
private def tccW (k : ℕ) (l : List (Fin (k + 1))) : ℕ :=
  (l.map (tccWt k)).sum

private lemma tccW_cons (k : ℕ) (a : Fin (k + 1)) (l : List (Fin (k + 1))) :
    tccW k (a :: l) = tccWt k a + tccW k l := rfl

private lemma tccW_ge_length (k : ℕ) (l : List (Fin (k + 1))) : l.length ≤ tccW k l := by
  induction l with
  | nil => simp [tccW]
  | cons a t ih =>
    have h1 : 1 ≤ tccWt k a := tccWt_pos k a
    simp only [List.length_cons, tccW_cons]
    omega

/-- All symbol lists of length at most `N`. -/
private def tccAll (k N : ℕ) : Finset (List (Fin (k + 1))) :=
  (Finset.range (N + 1)).biUnion fun ℓ =>
    ((Fintype.piFinset fun _ : Fin ℓ => (Finset.univ : Finset (Fin (k + 1)))).map
      ⟨List.ofFn, List.ofFn_injective⟩)

private lemma tcc_mem_all (k N : ℕ) (l : List (Fin (k + 1))) :
    l ∈ tccAll k N ↔ l.length ≤ N := by
  constructor
  · intro h
    unfold tccAll at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨ℓ, hℓ, hf⟩ := h
    rw [Finset.mem_range] at hℓ
    rw [Finset.mem_map] at hf
    obtain ⟨f, _, hfl⟩ := hf
    simp only [Function.Embedding.coeFn_mk] at hfl
    subst l
    rw [List.length_ofFn]
    omega
  · intro h
    unfold tccAll
    rw [Finset.mem_biUnion]
    refine ⟨l.length, by rw [Finset.mem_range]; omega, ?_⟩
    rw [Finset.mem_map]
    exact ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

/-- Compositions of `n` as a finset of symbol lists. -/
private def tccFin (k n : ℕ) : Finset (List (Fin (k + 1))) :=
  (tccAll k n).filter fun l => tccW k l = n

private lemma tcc_mem_fin (k n : ℕ) (l : List (Fin (k + 1))) :
    l ∈ tccFin k n ↔ l.length ≤ n ∧ tccW k l = n := by
  unfold tccFin
  rw [Finset.mem_filter, tcc_mem_all]

private lemma tccFin_zero (k : ℕ) : tccFin k 0 = {[]} := by
  ext l
  rw [tcc_mem_fin]
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨hlen, hW⟩ := h
    have hlen0 : l.length = 0 := by
      have h1 := tccW_ge_length k l
      omega
    exact List.length_eq_zero_iff.mp hlen0
  · intro h
    subst h
    refine ⟨by simp, ?_⟩
    simp [tccW]

private lemma tccFin_zero_card (k : ℕ) (P : ℤ → ℕ) (hPone : P 1 = 1) :
    (tccFin k 0).card = P (((0 + 1 : ℕ)) : ℤ) := by
  rw [tccFin_zero, Finset.card_singleton]
  have e : (((0 + 1 : ℕ)) : ℤ) = 1 := by simp
  rw [e, hPone]

/-- Weight on plain naturals, matching `tccWt` on valid symbols. -/
private def tccWn : ℕ → ℕ := fun j => if j ≤ 1 then 1 else j

/-- Contribution of head value `j` to the count. -/
private def tccPiece (k N : ℕ) (j : ℕ) : ℕ :=
  if tccWn j ≤ N then (tccFin k (N - tccWn j)).card else 0

/-- Compositions of `N` whose head symbol has value `j`. -/
private def tccHead (k N : ℕ) (j : ℕ) : Finset (List (Fin (k + 1))) :=
  (tccFin k N).filter fun l => l.head?.map Fin.val = some j

private lemma tcc_mem_head (k N j : ℕ) (l : List (Fin (k + 1))) :
    l ∈ tccHead k N j ↔ l ∈ tccFin k N ∧ l.head?.map Fin.val = some j := by
  unfold tccHead
  rw [Finset.mem_filter]

private lemma tccHead_disjoint (k N i j : ℕ) (h : i ≠ j) :
    Disjoint (tccHead k N i) (tccHead k N j) := by
  unfold tccHead
  rw [Finset.disjoint_filter]
  intro x _ h1 h2
  exact h (Option.some_injective _ (h1.symm.trans h2))

private lemma tccHead_card (k N j : ℕ) (hj : j < k + 1) (hle : tccWn j ≤ N) :
    (tccHead k N j).card = (tccFin k (N - tccWn j)).card := by
  have haj : tccWt k (⟨j, hj⟩ : Fin (k + 1)) = tccWn j := rfl
  have hw1 : 1 ≤ tccWn j := by
    unfold tccWn
    split <;> omega
  symm
  apply Finset.card_bij (fun l _ => (⟨j, hj⟩ : Fin (k + 1)) :: l)
  · intro l hl
    show (⟨j, hj⟩ : Fin (k + 1)) :: l ∈ tccHead k N j
    rw [tcc_mem_fin] at hl
    obtain ⟨hlen, hW⟩ := hl
    rw [tcc_mem_head]
    refine ⟨(tcc_mem_fin k N _).mpr ⟨?_, ?_⟩, rfl⟩
    · rw [List.length_cons]
      omega
    · rw [tccW_cons, haj, hW]
      omega
  · intro a _ b _ h
    have h' : (⟨j, hj⟩ : Fin (k + 1)) :: a = (⟨j, hj⟩ : Fin (k + 1)) :: b := h
    exact congrArg List.tail h'
  · intro b hb
    rw [tcc_mem_head] at hb
    obtain ⟨hbC, hbhead⟩ := hb
    rw [tcc_mem_fin] at hbC
    obtain ⟨_, hW⟩ := hbC
    have hne : b ≠ [] := by
      rintro rfl
      simp at hbhead
    obtain ⟨bh, bt, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hbh : bh.val = j := by simpa using hbhead
    have hcw : tccWt k bh = tccWn j := by simp [tccWt, tccWn, hbh]
    have h2 : tccW k bt = N - tccWn j := by
      have e := hW
      rw [tccW_cons, hcw] at e
      omega
    refine ⟨bt, (tcc_mem_fin k (N - tccWn j) bt).mpr ⟨?_, h2⟩, ?_⟩
    · have h1 := tccW_ge_length k bt
      omega
    · show (⟨j, hj⟩ : Fin (k + 1)) :: bt = bh :: bt
      have e2 : (⟨j, hj⟩ : Fin (k + 1)) = bh := by
        rw [Fin.ext_iff]
        exact hbh.symm
      rw [e2]

private lemma tccHead_empty (k N j : ℕ) (h : N < tccWn j) : tccHead k N j = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  rw [tcc_mem_head] at hb
  obtain ⟨hbC, hbhead⟩ := hb
  rw [tcc_mem_fin] at hbC
  obtain ⟨_, hW⟩ := hbC
  have hne : b ≠ [] := by
    rintro rfl
    simp at hbhead
  obtain ⟨bh, bt, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hbh : bh.val = j := by simpa using hbhead
  have hcw : tccWt k bh = tccWn j := by simp [tccWt, tccWn, hbh]
  have e : tccW k (bh :: bt) = N := hW
  rw [tccW_cons, hcw] at e
  omega

private lemma tcc_biUnion (k N : ℕ) (hN : 1 ≤ N) :
    tccFin k N = (Finset.range (k + 1)).biUnion (tccHead k N) := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro hl
    rw [tcc_mem_fin] at hl
    obtain ⟨hlen, hW⟩ := hl
    have hne : l ≠ [] := by
      rintro rfl
      have h0 : tccW k ([] : List (Fin (k + 1))) = 0 := rfl
      omega
    obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨b.val, b.isLt, ?_⟩
    rw [tcc_mem_head]
    exact ⟨(tcc_mem_fin k N _).mpr ⟨hlen, hW⟩, rfl⟩
  · rintro ⟨j, _, hl⟩
    rw [tcc_mem_head] at hl
    exact hl.1

private lemma tcc_card_eq_sum (k N : ℕ) (hN : 1 ≤ N) :
    (tccFin k N).card = ∑ j ∈ Finset.range (k + 1), tccPiece k N j := by
  have hunion := tcc_biUnion k N hN
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint (tccHead k N) := by
    intro i _ j _ hne
    exact tccHead_disjoint k N i j hne
  have hpiece : ∀ j ∈ Finset.range (k + 1), (tccHead k N j).card = tccPiece k N j := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases h : tccWn j ≤ N
    · rw [tccHead_card k N j hj h]
      unfold tccPiece
      simp only [h, ite_true]
    · rw [tccHead_empty k N j (by omega)]
      unfold tccPiece
      simp only [h, ite_false, Finset.card_empty]
  rw [hunion, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl hpiece

private lemma tcc_range_split (k : ℕ) (hk : 2 ≤ k) (F : ℕ → ℕ) :
    ∑ j ∈ Finset.range (k + 1), F j
      = F 0 + F 1 + ∑ j ∈ Finset.range (k - 1), F (j + 2) := by
  have hem : Function.Injective (· + 2 : ℕ → ℕ) := by
    intro x y h
    have h2 : x + 2 = y + 2 := h
    omega
  have hde : Disjoint ({0, 1} : Finset ℕ)
      ((Finset.range (k - 1)).map ⟨(· + 2), hem⟩) := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_map]
    rintro ⟨x, _, hx⟩
    simp only [Function.Embedding.coeFn_mk] at hx
    omega
  have hunion : Finset.range (k + 1)
      = {0, 1} ∪ ((Finset.range (k - 1)).map ⟨(· + 2), hem⟩) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      by_cases j0 : j = 0
      · exact Or.inl (Or.inl j0)
      · by_cases j1 : j = 1
        · exact Or.inl (Or.inr j1)
        · exact Or.inr ⟨j - 2, by omega, by omega⟩
    · rintro ((rfl | rfl) | ⟨x, hx, rfl⟩)
      · omega
      · omega
      · omega
  rw [hunion, Finset.sum_union hde, Finset.sum_pair (by norm_num),
    Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]

/-- The list-count satisfies the generalized Pell recurrence. -/
private lemma tcc_card_aux (k : ℕ) (hk : 2 ≤ k) (P : ℤ → ℕ)
    (hPzero : ∀ m : ℤ, 2 - (k : ℤ) ≤ m → m ≤ 0 → P m = 0)
    (hPone : P 1 = 1)
    (hPrec : ∀ m : ℤ, 2 ≤ m →
      P m = 2 * P (m - 1) +
        ∑ i : Fin (k - 1), P (m - (((i : ℕ) : ℤ) + 2))) :
    ∀ N m : ℕ, m ≤ N → (tccFin k m).card = P (((m + 1 : ℕ)) : ℤ) := by
  intro N
  induction N with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    exact tccFin_zero_card k P hPone
  | succ N IH =>
    intro m hm
    cases m with
    | zero => exact tccFin_zero_card k P hPone
    | succ M =>
      have hM : M ≤ N := by omega
      have h1M : 1 ≤ M + 1 := by omega
      have hsum : (tccFin k (M + 1)).card
          = tccPiece k (M + 1) 0 + tccPiece k (M + 1) 1
            + ∑ j ∈ Finset.range (k - 1), tccPiece k (M + 1) (j + 2) := by
        have h1 := tcc_card_eq_sum k (M + 1) h1M
        rw [tcc_range_split k hk (tccPiece k (M + 1))] at h1
        exact h1
      have hp0 : tccPiece k (M + 1) 0 = P (((M + 1 : ℕ)) : ℤ) := by
        have hw : tccWn 0 = 1 := rfl
        have hle : (1 : ℕ) ≤ M + 1 := by omega
        unfold tccPiece
        simp only [hw, hle, ite_true, Nat.add_sub_cancel]
        exact IH M hM
      have hp1 : tccPiece k (M + 1) 1 = P (((M + 1 : ℕ)) : ℤ) := by
        have hw : tccWn 1 = 1 := rfl
        have hle : (1 : ℕ) ≤ M + 1 := by omega
        unfold tccPiece
        simp only [hw, hle, ite_true, Nat.add_sub_cancel]
        exact IH M hM
      have hP2 : (2 : ℤ) ≤ ((((M + 2 : ℕ))) : ℤ) := by omega
      have hrec := hPrec ((((M + 2 : ℕ))) : ℤ) hP2
      have hconv : (∑ i : Fin (k - 1), P ((((M + 2 : ℕ)) : ℤ) - ((((i : ℕ)) : ℤ) + 2)))
          = ∑ j ∈ Finset.range (k - 1), P ((((M + 2 : ℕ)) : ℤ) - ((((j : ℕ)) : ℤ) + 2)) := by
        apply Finset.sum_bij (fun i _ => (i.val : ℕ))
        · intro i _
          exact Finset.mem_range.mpr i.isLt
        · intro a _ b _ h
          exact Fin.ext h
        · intro j hj
          rw [Finset.mem_range] at hj
          exact ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
        · intro i _
          rfl
      have hpiece : (∑ j ∈ Finset.range (k - 1), P ((((M + 2 : ℕ)) : ℤ) - ((((j : ℕ)) : ℤ) + 2)))
          = ∑ j ∈ Finset.range (k - 1), tccPiece k (M + 1) (j + 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hw2 : tccWn (j + 2) = j + 2 := by
          unfold tccWn
          split <;> omega
        by_cases hle : j + 2 ≤ M + 1
        · unfold tccPiece
          simp only [hw2, hle, ite_true]
          have hmem : M + 1 - (j + 2) ≤ N := by omega
          have hIH := IH (M + 1 - (j + 2)) hmem
          rw [hIH]
          congr 1
          omega
        · unfold tccPiece
          simp only [hw2, hle, ite_false]
          apply hPzero
          · omega
          · omega
      have hPsum := hconv.trans hpiece
      have h2eq : P ((((M + 2 : ℕ)) : ℤ) - 1) = P (((M + 1 : ℕ)) : ℤ) := by
        congr 1
        omega
      have hgoal : ((((M + 1 + 1 : ℕ))) : ℤ) = ((((M + 2 : ℕ))) : ℤ) := by
        congr 1
      rw [hgoal, hsum]
      rw [hPsum, h2eq] at hrec
      omega

/--
**Generalized Pell numbers count compositions with two-colored ones.** Let $k \ge 2$ and
$n \ge 1$ be natural numbers, and let $(P_m)_{m \in \mathbb{Z}}$ be natural numbers with $P_m = 0$
for $2 - k \le m \le 0$, $P_1 = 1$, and $P_m = 2P_{m-1} + P_{m-2} + \dots + P_{m-k}$ for all
$m \ge 2$. Then the number of compositions of $n$ into parts from $\{1, \dots, k\}$, where each
part equal to $1$ carries one of two colors, equals $P_{n+1}$.

Source: Jhon J. Bravo, Jose L. Herrera, and José L. Ramírez, "Combinatorial
Interpretation of Generalized Pell Numbers," Journal of Integer Sequences 23
(2020), Article 20.2.1, theorem `C_k(n) = P_{n+1}^{(k)}` for `n ≥ 1`
(equation label Equation1), lines 441–447,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Bravo/bravo4.tex.
Proves `Wanted` entry `generalized_pell_eq_two_colored_compositions`.
-/
theorem generalized_pell_eq_two_colored_compositions
    (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (P : ℤ → ℕ)
    (hPzero : ∀ m : ℤ, 2 - (k : ℤ) ≤ m → m ≤ 0 → P m = 0)
    (hPone : P 1 = 1)
    (hPrec : ∀ m : ℤ, 2 ≤ m →
      P m = 2 * P (m - 1) +
        ∑ i : Fin (k - 1), P (m - (((i : ℕ) : ℤ) + 2))) :
    Set.ncard {
      c : Σ ℓ : Fin (n + 1), Fin ℓ → Fin (k + 1) |
        ∑ j : Fin c.1, (if (c.2 j).val ≤ 1 then 1 else (c.2 j).val) = n
    } = P ((n + 1 : ℕ) : ℤ) := by
  have _hn' := hn
  have key : ∀ m : ℕ, (tccFin k m).card = P (((m + 1 : ℕ)) : ℤ) := by
    have hkey := tcc_card_aux k hk P hPzero hPone hPrec
    intro m
    exact hkey m m le_rfl
  rw [← key n, ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun c _ => List.ofFn c.2)
  · intro c hc
    show List.ofFn c.2 ∈ (↑(tccFin k n) : Set (List (Fin (k + 1))))
    rw [Finset.mem_coe, tcc_mem_fin]
    refine ⟨?_, ?_⟩
    · rw [List.length_ofFn]
      have h := c.1.isLt
      omega
    · have e : tccW k (List.ofFn c.2) = ∑ j : Fin (↑c.1 : ℕ), tccWt k (c.2 j) := by
        unfold tccW
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      rw [e]
      exact hc
  · intro a b ha hb h
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [] at h
    have hlen : a1.val = b1.val := by
      have hL := congrArg List.length h
      simp only [List.length_ofFn] at hL
      exact hL
    have h1 : a1 = b1 := Fin.ext hlen
    subst h1
    have h2 : a2 = b2 := List.ofFn_injective h
    subst h2
    rfl
  · intro l hl
    rw [Finset.mem_coe, tcc_mem_fin] at hl
    obtain ⟨hlen, hW⟩ := hl
    have hfin : l.length < n + 1 := by omega
    refine ⟨⟨⟨l.length, hfin⟩, fun j => l.get (show Fin l.length from j)⟩, ?_, ?_⟩
    · change ∑ j : Fin l.length, tccWt k (l.get j) = n
      have e : tccW k l = ∑ j : Fin l.length, tccWt k (l.get j) := by
        conv_lhs => rw [← List.ofFn_get l]
        unfold tccW
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      rw [← e]
      exact hW
    · change List.ofFn (fun j : Fin l.length => l.get j) = l
      exact List.ofFn_get l

end MetaMathlibExt
