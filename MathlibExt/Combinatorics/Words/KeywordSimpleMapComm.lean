/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.KeywordSubstitutionClasses

/-!
# When two simple maps of a keyword commute

Two simple maps of a binary keyword commute exactly when their windows are disjoint or the
overlapping prefix of the keyword differs from the matching suffix and from its negation.

## References

* Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
  *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
  Journal of Integer Sequences 28 (2025), Article 25.6.6; arXiv:2503.11055, Proposition 3.3.
-/

namespace MetaMathlibExt
namespace keywordSimpleMap_comm_iff

variable {m n : ℕ}

-- A simple map changes no letter outside its window.
private theorem apply_of_not_mem (a : Fin (m + 1) → Bool) (i : ℕ) (u : Fin n → Bool)
    (k : Fin n) (hk : ¬ (i ≤ k.val ∧ k.val ≤ i + m)) : keywordSimpleMap a i u k = u k := by
  by_cases h : KeywordApplicable a i u
  · rw [keywordSimpleMap_apply_of_applicable a i u h, ite_eq_right hk]
  · rw [keywordSimpleMap_of_not_applicable a i u h]

-- Applicability says that the window reads the keyword, negated when `b` is `true`.
private theorem applicable_iff (a : Fin (m + 1) → Bool) (i : ℕ) (u : Fin n → Bool) :
    KeywordApplicable a i u ↔ i + m < n ∧ ∃ b : Bool,
      ∀ (k : Fin n) (t : Fin (m + 1)), k.val = i + t.val → u k = (b ^^ a t) := by
  constructor
  · rintro ⟨hin, hw⟩
    refine ⟨hin, ?_⟩
    rcases hw with hw | hw
    · refine ⟨false, fun k t hk => ?_⟩
      rw [show k = ⟨i + t, by have := t.isLt; omega⟩ from Fin.ext hk]
      simpa only [Bool.false_xor] using hw t
    · refine ⟨true, fun k t hk => ?_⟩
      rw [show k = ⟨i + t, by have := t.isLt; omega⟩ from Fin.ext hk]
      simpa only [Bool.true_xor] using hw t
  · rintro ⟨hin, b, hw⟩
    refine ⟨hin, ?_⟩
    cases b
    · exact Or.inl fun t => by simpa only [Bool.false_xor] using hw _ t rfl
    · exact Or.inr fun t => by simpa only [Bool.true_xor] using hw _ t rfl

-- Applicability only depends on the letters in the window.
private theorem applicable_congr (a : Fin (m + 1) → Bool) (i : ℕ) {u v : Fin n → Bool}
    (h : ∀ k : Fin n, i ≤ k.val → k.val ≤ i + m → v k = u k) :
    KeywordApplicable a i v ↔ KeywordApplicable a i u := by
  rw [applicable_iff, applicable_iff]
  refine and_congr_right fun _ => exists_congr fun b => forall_congr' fun k =>
    forall_congr' fun t => imp_congr_right fun hk => ?_
  rw [h k (by omega) (by have := t.isLt; omega)]

-- After a simple map acts, its window reads the other one of `a` and `!a`.
private theorem applicable_self (a : Fin (m + 1) → Bool) (i : ℕ) {u : Fin n → Bool}
    (h : KeywordApplicable a i u) : KeywordApplicable a i (keywordSimpleMap a i u) := by
  obtain ⟨hin, b, hu⟩ := (applicable_iff a i u).mp h
  refine (applicable_iff a i _).mpr ⟨hin, !b, fun k t hk => ?_⟩
  have hmem : i ≤ k.val ∧ k.val ≤ i + m := by have := t.isLt; omega
  rw [keywordSimpleMap_apply_of_applicable a i u h, ite_eq_left hmem, hu k t hk]
  cases b <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false,
    Bool.not_not]

-- Two simple maps that keep each other's applicability commute on that word.
private theorem comm_of_applicable_iff (a : Fin (m + 1) → Bool) (i j : ℕ) (u : Fin n → Bool)
    (hi : KeywordApplicable a i (keywordSimpleMap a j u) ↔ KeywordApplicable a i u)
    (hj : KeywordApplicable a j (keywordSimpleMap a i u) ↔ KeywordApplicable a j u) :
    keywordSimpleMap a i (keywordSimpleMap a j u) =
      keywordSimpleMap a j (keywordSimpleMap a i u) := by
  by_cases hai : KeywordApplicable a i u <;> by_cases haj : KeywordApplicable a j u
  · funext k
    rw [keywordSimpleMap_apply_of_applicable _ _ _ (hi.mpr hai),
      keywordSimpleMap_apply_of_applicable _ _ _ (hj.mpr haj),
      keywordSimpleMap_apply_of_applicable _ _ _ haj,
      keywordSimpleMap_apply_of_applicable _ _ _ hai]
    split_ifs <;> rfl
  · rw [keywordSimpleMap_of_not_applicable a j u haj,
      keywordSimpleMap_of_not_applicable a j _ (mt hj.mp haj)]
  · rw [keywordSimpleMap_of_not_applicable a i u hai,
      keywordSimpleMap_of_not_applicable a i _ (mt hi.mp hai)]
  · rw [keywordSimpleMap_of_not_applicable a j u haj, keywordSimpleMap_of_not_applicable a i u hai,
      keywordSimpleMap_of_not_applicable a j u haj]

-- The prefix of the keyword of length `m + 1 - d` equals the suffix of that length, negated when
-- `b` is `true`.
private def Overlap (a : Fin (m + 1) → Bool) (d : ℕ) (b : Bool) : Prop :=
  ∀ t : ℕ, ∀ ht : d + t ≤ m, a ⟨t, by omega⟩ = (b ^^ a ⟨d + t, by omega⟩)

private theorem take_eq_drop_iff (a : Fin (m + 1) → Bool) {d : ℕ} (hd : d ≤ m) :
    (List.ofFn a).take (m + 1 - d) = (List.ofFn a).drop d ↔ Overlap a d false := by
  rw [List.ext_getElem_iff]
  simp only [List.length_take, List.length_drop, List.length_ofFn, List.getElem_take,
    List.getElem_drop, List.getElem_ofFn, Overlap, Bool.false_xor]
  constructor
  · rintro ⟨-, h⟩ t ht
    exact h t (by omega) (by omega)
  · intro h
    exact ⟨by omega, fun t _ h2 => h t (by omega)⟩

private theorem take_eq_map_not_drop_iff (a : Fin (m + 1) → Bool) {d : ℕ} (hd : d ≤ m) :
    (List.ofFn a).take (m + 1 - d) = ((List.ofFn a).drop d).map not ↔ Overlap a d true := by
  rw [List.ext_getElem_iff]
  simp only [List.length_take, List.length_drop, List.length_map, List.length_ofFn,
    List.getElem_take, List.getElem_map, List.getElem_drop, List.getElem_ofFn, Overlap,
    Bool.true_xor]
  constructor
  · rintro ⟨-, h⟩ t ht
    exact h t (by omega) (by omega)
  · intro h
    exact ⟨by omega, fun t _ h2 => h t (by omega)⟩

-- Two readings of one letter determine the relative negation of the keyword letters they use.
private theorem xor_cancel {b c x y : Bool} (h : (b ^^ x) = (c ^^ y)) :
    y = ((b ^^ c) ^^ x) := by
  revert h
  cases b <;> cases c <;> cases x <;> cases y <;> decide

-- If both simple maps act on one word, the overlapping prefix and suffix agree up to negation.
private theorem overlap_of_applicable (a : Fin (m + 1) → Bool) {i j : ℕ} (hij : i < j)
    {u : Fin n → Bool} (hi : KeywordApplicable a i u) (hj : KeywordApplicable a j u) :
    ∃ b, Overlap a (j - i) b := by
  obtain ⟨-, b, hu⟩ := (applicable_iff a i u).mp hi
  obtain ⟨hjn, c, hv⟩ := (applicable_iff a j u).mp hj
  refine ⟨b ^^ c, fun t ht => ?_⟩
  have h1 := hu ⟨j + t, by omega⟩ ⟨j - i + t, by omega⟩ (by change j + t = i + (j - i + t); omega)
  have h2 := hv ⟨j + t, by omega⟩ ⟨t, by omega⟩ rfl
  exact xor_cancel (h1.symm.trans h2)

-- Negating a letter of the keyword is an involution.
private theorem xor_symm {b x y : Bool} (h : x = (b ^^ y)) : y = (b ^^ x) := by
  revert h
  cases b <;> cases x <;> cases y <;> decide

-- Conversely, an overlap gives a word on which both simple maps act.
private theorem exists_applicable_both (a : Fin (m + 1) → Bool) {i j : ℕ} (hij : i < j)
    (hd : j - i ≤ m) (hj : j + m < n) {b : Bool} (hov : Overlap a (j - i) b) :
    ∃ u : Fin n → Bool, KeywordApplicable a i u ∧ KeywordApplicable a j u := by
  let u : Fin n → Bool := fun k =>
    if h : k.val ≤ i + m then a ⟨k.val - i, by omega⟩
    else if h' : k.val ≤ j + m then (b ^^ a ⟨k.val - j, by omega⟩) else false
  refine ⟨u, (applicable_iff a i u).mpr ⟨by omega, false, fun k t hk => ?_⟩,
    (applicable_iff a j u).mpr ⟨hj, b, fun k t hk => ?_⟩⟩
  · have h : k.val ≤ i + m := by have := t.isLt; omega
    simp only [u, dite_eq_left h, Bool.false_xor]
    exact congrArg a (Fin.ext (by change k.val - i = t.val; omega))
  · by_cases h : k.val ≤ i + m
    · simp only [u, dite_eq_left h]
      have := xor_symm (hov t.val (by have := t.isLt; omega))
      exact (congrArg a (Fin.ext (by change k.val - i = j - i + t.val; omega))).trans this
    · have h' : k.val ≤ j + m := by have := t.isLt; omega
      simp only [u, dite_eq_right h, dite_eq_left h']
      exact congrArg (b ^^ ·) (congrArg a (Fin.ext (by change k.val - j = t.val; omega)))

-- Two readings of the keyword that agree on one letter cannot differ by a negation on another.
private theorem xor_flip {b c x y : Bool} (h0 : (c ^^ x) = (b ^^ x))
    (h1 : (!(b ^^ y)) = (c ^^ y)) : False := by
  revert h0 h1
  cases b <;> cases c <;> cases x <;> cases y <;> decide

-- When both simple maps act on a word, the second one stops the first from acting.
private theorem not_applicable_after (a : Fin (m + 1) → Bool) {i j : ℕ} (hij : i < j)
    (hd : j - i ≤ m) {u : Fin n → Bool} (hi : KeywordApplicable a i u)
    (hj : KeywordApplicable a j u) :
    ¬ KeywordApplicable a i (keywordSimpleMap a j u) := by
  obtain ⟨hin, b, hu⟩ := (applicable_iff a i u).mp hi
  rw [applicable_iff]
  rintro ⟨-, c, hv⟩
  have h0 := hv ⟨i, by omega⟩ 0 (by simp)
  have h0' := hu ⟨i, by omega⟩ 0 (by simp)
  have hl := hv ⟨i + m, hin⟩ (Fin.last m) (by simp)
  have hl' := hu ⟨i + m, hin⟩ (Fin.last m) (by simp)
  have hout : ¬ (j ≤ (⟨i, by omega⟩ : Fin n).val ∧ (⟨i, by omega⟩ : Fin n).val ≤ j + m) := by
    dsimp only
    omega
  have hmem : j ≤ (⟨i + m, hin⟩ : Fin n).val ∧ (⟨i + m, hin⟩ : Fin n).val ≤ j + m := by
    dsimp only
    omega
  rw [apply_of_not_mem a j u _ hout] at h0
  rw [keywordSimpleMap_apply_of_applicable a j u hj, ite_eq_left hmem, hl'] at hl
  exact xor_flip (h0.symm.trans h0') hl

-- An overlap makes the two simple maps disagree at the first letter of the left window.
private theorem not_comm_of_overlap (a : Fin (m + 1) → Bool) {i j : ℕ} (hij : i < j)
    (hd : j - i ≤ m) (hj : j + m < n) {b : Bool} (hov : Overlap a (j - i) b) :
    keywordSimpleMap (n := n) a i ∘ keywordSimpleMap a j ≠
      keywordSimpleMap a j ∘ keywordSimpleMap a i := by
  obtain ⟨u, hiu, hju⟩ := exists_applicable_both a hij hd hj hov
  intro h
  have hk := congrFun (congrFun h u) ⟨i, by omega⟩
  have hout : ¬ (j ≤ (⟨i, by omega⟩ : Fin n).val ∧ (⟨i, by omega⟩ : Fin n).val ≤ j + m) := by
    dsimp only
    omega
  have hmem : i ≤ (⟨i, by omega⟩ : Fin n).val ∧ (⟨i, by omega⟩ : Fin n).val ≤ i + m := by
    dsimp only
    omega
  simp only [Function.comp_apply] at hk
  rw [keywordSimpleMap_of_not_applicable a i _ (not_applicable_after a hij hd hiu hju),
    apply_of_not_mem a j u _ hout, apply_of_not_mem a j (keywordSimpleMap a i u) _ hout,
    keywordSimpleMap_apply_of_applicable a i u hiu, ite_eq_left hmem] at hk
  simp at hk

end keywordSimpleMap_comm_iff

open keywordSimpleMap_comm_iff in
/-- **When two simple maps commute.** Let $a$ be a keyword of length $m + 1$ and let $n$ be a
natural number. Let $i < j$ be natural numbers with $j + m < n$, and put $\Delta = j - i$. The
simple maps $\varphi_i$ and $\varphi_j$ of $a$ on binary words of length $n$ satisfy
$\varphi_i \circ \varphi_j = \varphi_j \circ \varphi_i$ if and only if $\Delta \ge m + 1$, or the
prefix of $a$ of length $m + 1 - \Delta$ differs both from the suffix of $a$ of length
$m + 1 - \Delta$ and from the letterwise negation of that suffix.

In the paper's numbering, which counts letters from $1$, the hypothesis reads $i < j \le n - m$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 12
(`jis-2025-25.6.6-prop-12`). -/
public theorem keywordSimpleMap_comm_iff {m n : ℕ} (a : Fin (m + 1) → Bool)
    (i j : ℕ) (hij : i < j) (hj : j + m < n) :
    (keywordSimpleMap (n := n) a i ∘ keywordSimpleMap a j =
        keywordSimpleMap a j ∘ keywordSimpleMap a i) ↔
      (((List.ofFn a).take (m + 1 - (j - i)) ≠ (List.ofFn a).drop (j - i) ∧
          (List.ofFn a).take (m + 1 - (j - i)) ≠ ((List.ofFn a).drop (j - i)).map not) ∨
        m + 1 ≤ j - i) := by
  by_cases hd : m + 1 ≤ j - i
  · -- Disjoint windows: neither map touches the other's window.
    refine iff_of_true (funext fun u => comm_of_applicable_iff a i j u ?_ ?_) (Or.inr hd)
    · exact applicable_congr a i fun k _ hk => apply_of_not_mem a j u k (by omega)
    · exact applicable_congr a j fun k hk _ => apply_of_not_mem a i u k (by omega)
  have hd' : j - i ≤ m := by omega
  rw [or_iff_left hd, ne_eq, ne_eq, take_eq_drop_iff a hd', take_eq_map_not_drop_iff a hd']
  constructor
  · intro hcomm
    exact ⟨fun hov => not_comm_of_overlap a hij hd' hj hov hcomm,
      fun hov => not_comm_of_overlap a hij hd' hj hov hcomm⟩
  · rintro ⟨h0, h1⟩
    -- No word lets both maps act, so each map keeps the other's applicability.
    have excl {u : Fin n → Bool} (hi : KeywordApplicable a i u)
        (hj : KeywordApplicable a j u) : False := by
      obtain ⟨b, hov⟩ := overlap_of_applicable a hij hi hj
      cases b
      · exact h0 hov
      · exact h1 hov
    refine funext fun u => comm_of_applicable_iff a i j u ?_ ?_
    · by_cases hJ : KeywordApplicable a j u
      · exact iff_of_false (fun h => excl h (applicable_self a j hJ)) (fun h => excl h hJ)
      · rw [keywordSimpleMap_of_not_applicable a j u hJ]
    · by_cases hI : KeywordApplicable a i u
      · exact iff_of_false (fun h => excl (applicable_self a i hI) h) (fun h => excl hI h)
      · rw [keywordSimpleMap_of_not_applicable a i u hI]

end MetaMathlibExt
