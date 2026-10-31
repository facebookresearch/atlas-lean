/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray
public import Mathlib.Data.Nat.Log

/-!
# Pattern search in a suffix array by binary search

Manber and Myers (1993) locate the occurrences of a pattern `P` in a text `s` with the suffix
array alone: the suffixes that start with `P` are consecutive in suffix-array order, so the
occurrences of `P` are one interval `[sp, ep)` of suffix-array rows, and two binary searches find
its ends.

Here `sp` is the number of rows whose suffix, truncated to `|P|` letters, is smaller than `P`, and
`ep` is the number of rows whose truncated suffix is at most `P`. Both predicates hold on an
initial segment of the rows (the truncation `List.take` is monotone for the lexicographic order),
so a binary search (`lowerBound`) finds each boundary.

## Main results

* `prefix_of_le_of_le`: in the lexicographic order, the lists with a given prefix form an
  interval: `x ≤ y ≤ z` with `P` a prefix of `x` and of `z` forces `P` to be a prefix of `y`.
* `prefix_suffixArray_of_le_of_le`: **the rows whose suffix starts with `P` are contiguous**.
* `lowerBound_spec`: binary search returns the boundary of a predicate that holds on an initial
  segment of `[lo, hi)`.
* `lowerBoundSteps_le`: binary search makes at most `⌊log₂ (hi - lo)⌋ + 1` probes.
* `saSearch_spec`: **the computed interval `[sp, ep)` is exactly the set of rows whose suffix
  starts with `P`**; `saSearch_bounds`: `sp ≤ ep ≤ |s|`.

## Cost model

Each probe of `saSearch` compares a suffix truncated to `|P|` letters with `P`, `O(|P|)` letter
comparisons, and each of the two binary searches makes at most `⌊log₂ |s|⌋ + 1` probes
(`lowerBoundSteps_le`): `O(|P| log |s|)` comparisons in total, given random access to the suffix
array. (`List.getD` is linear-time; the count is of probes and letter comparisons.) The
`O(|P| + log |s|)` refinement of Manber and Myers with longest-common-prefix tables is not
covered here.

## References

* U. Manber and G. Myers, *Suffix arrays: a new method for on-line string searches*, SIAM J.
  Comput. 22 (1993), 935–948.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Indexing.SuffixArraySearch

open Cslib.Algorithms.Lean.SuffixArray

private theorem take_mono {β : Type*} [LinearOrder β] {x y : List β}
    (h : x ≤ y) (m : ℕ) : x.take m ≤ y.take m := by
  induction m generalizing x y with
  | zero => simp
  | succ m ih =>
      cases x with
      | nil =>
          cases y with
          | nil => exact le_rfl
          | cons b ys => exact le_of_lt (List.Lex.nil)
      | cons a xs =>
          rcases lt_or_eq_of_le h with hlt | rfl
          · cases hlt with
            | rel hab => exact le_of_lt (List.Lex.rel hab)
            | cons htail => exact List.cons_le_cons a (ih (le_of_lt htail))
          · exact le_rfl

/-- **Prefix classes are lexicographic intervals**: if `x ≤ y ≤ z` and `P` is a prefix of both
`x` and `z`, then `P` is a prefix of `y`. -/
theorem prefix_of_le_of_le {β : Type*} [LinearOrder β] {P x y z : List β} (hxy : x ≤ y)
    (hyz : y ≤ z) (hx : P <+: x) (hz : P <+: z) : P <+: y := by
  apply List.prefix_iff_eq_take.mpr
  have hleft := take_mono hxy P.length
  have hright := take_mono hyz P.length
  rw [← List.prefix_iff_eq_take.mp hx] at hleft
  rw [← List.prefix_iff_eq_take.mp hz] at hright
  exact le_antisymm hleft hright

/-- Truncation is monotone for the lexicographic order: `x ≤ y → x.take m ≤ y.take m`. -/
theorem take_le_take {β : Type*} [LinearOrder β] {x y : List β} (h : x ≤ y) (m : ℕ) :
    x.take m ≤ y.take m := by
  exact take_mono h m

variable {α : Type*} [LinearOrder α]

private theorem suffix_row_mono {β : Type*} [LinearOrder β] (s : List β)
    {i j : ℕ} (hij : i ≤ j) (hj : j < s.length) :
    suffix s ((suffixArray s).getD i 0) ≤ suffix s ((suffixArray s).getD j 0) := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst j
    exact le_rfl
  · have hi : i < (suffixArray s).length := by rw [suffixArray_length]; omega
    have hj' : j < (suffixArray s).length := by rwa [suffixArray_length]
    have hp := List.pairwise_map.mp (pairwise_suffix_suffixArray s)
    have h := List.pairwise_iff_getElem.mp hp i j hi hj' hlt
    simpa only [List.getElem_eq_getD 0] using h

/-- **The occurrences of a pattern are contiguous in the suffix array**: if rows `r₁ ≤ r₂ ≤ r₃`
of the suffix array of `s` are in range and the suffixes of rows `r₁` and `r₃` start with `P`,
so does the suffix of row `r₂`. -/
theorem prefix_suffixArray_of_le_of_le (s P : List α) {r₁ r₂ r₃ : ℕ} (h₁₂ : r₁ ≤ r₂)
    (h₂₃ : r₂ ≤ r₃) (h₃ : r₃ < s.length)
    (hp₁ : P <+: suffix s ((suffixArray s).getD r₁ 0))
    (hp₃ : P <+: suffix s ((suffixArray s).getD r₃ 0)) :
    P <+: suffix s ((suffixArray s).getD r₂ 0) := by
  exact prefix_of_le_of_le (suffix_row_mono s h₁₂ (by omega))
    (suffix_row_mono s h₂₃ h₃) hp₁ hp₃

/-- Binary search for the boundary of a predicate on `[lo, hi)`: the first index at which `p`
is false, assuming `p` holds on an initial segment of `[lo, hi)` (`lowerBound_spec`). Each call
probes the midpoint and recurses on one half. -/
def lowerBound (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : lo < hi then
    if p ((lo + hi) / 2) then lowerBound p ((lo + hi) / 2 + 1) hi
    else lowerBound p lo ((lo + hi) / 2)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- The number of probes `lowerBound p lo hi` makes. -/
def lowerBoundSteps (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : lo < hi then
    if p ((lo + hi) / 2) then lowerBoundSteps p ((lo + hi) / 2 + 1) hi + 1
    else lowerBoundSteps p lo ((lo + hi) / 2) + 1
  else 0
termination_by hi - lo
decreasing_by all_goals omega

/-- **Binary search is correct**: if `p` holds on an initial segment of `[lo, hi)` (whenever it
holds at `j`, it holds at every `i` with `lo ≤ i ≤ j`), then `lowerBound p lo hi` is the end `k` of
that segment: `lo ≤ k ≤ hi`, `p` holds on `[lo, k)` and fails on `[k, hi)`. -/
theorem lowerBound_spec (p : ℕ → Bool) (lo hi : ℕ) (hlo : lo ≤ hi)
    (hmono : ∀ i j, lo ≤ i → i ≤ j → j < hi → p j = true → p i = true) :
    lo ≤ lowerBound p lo hi ∧ lowerBound p lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < lowerBound p lo hi → p i = true) ∧
      (∀ i, lowerBound p lo hi ≤ i → i < hi → p i = false) := by
  generalize hn : hi - lo = n
  induction n using Nat.strong_induction_on generalizing lo hi with
  | h n ih =>
      by_cases h : lo < hi
      · have hmidlo : lo ≤ (lo + hi) / 2 := by omega
        have hmidhi : (lo + hi) / 2 < hi := by omega
        rw [lowerBound, dite_eq_left h]
        split
        · rename_i hp
          have hs := ih (hi - ((lo + hi) / 2 + 1)) (by omega)
            ((lo + hi) / 2 + 1) hi (by omega)
            (fun i j hi' hij hj hpj => hmono i j (by omega) hij hj hpj) rfl
          refine ⟨by omega, hs.2.1, ?_, hs.2.2.2⟩
          intro i hi' hik
          by_cases him : i ≤ (lo + hi) / 2
          · exact hmono i ((lo + hi) / 2) hi' him hmidhi hp
          · exact hs.2.2.1 i (by omega) hik
        · rename_i hp
          have hs := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2)
            hmidlo (fun i j hi' hij hj hpj => hmono i j hi' hij (by omega) hpj) rfl
          refine ⟨hs.1, by omega, hs.2.2.1, ?_⟩
          intro i hki hih
          by_cases him : i < (lo + hi) / 2
          · exact hs.2.2.2 i hki him
          · cases hpi : p i with
            | false => rfl
            | true =>
                exact (hp (hmono ((lo + hi) / 2) i hmidlo (by omega) hih hpi)).elim
      · rw [lowerBound, dite_eq_right h]
        exact ⟨le_rfl, hlo, by intro i hi' hik; omega, by intro i hki hih; omega⟩

/-- **Binary search is logarithmic**: at most `⌊log₂ (hi - lo)⌋ + 1` probes, for any predicate. -/
theorem lowerBoundSteps_le (p : ℕ → Bool) (lo hi : ℕ) :
    lowerBoundSteps p lo hi ≤ Nat.log 2 (hi - lo) + 1 := by
  generalize hn : hi - lo = n
  induction n using Nat.strong_induction_on generalizing lo hi with
  | h n ih =>
      rw [← hn]
      by_cases h : lo < hi
      · rw [lowerBoundSteps, dite_eq_left h]
        by_cases hsmall : hi - lo < 2
        · have hleft : ¬lo < (lo + hi) / 2 := by omega
          have hright : ¬(lo + hi) / 2 + 1 < hi := by omega
          split <;> rw [lowerBoundSteps, dite_eq_right (by assumption)] <;> omega
        · have hlog := Nat.log_of_one_lt_of_le (by decide : 1 < 2)
            (by omega : 2 ≤ hi - lo)
          split
          · have hs := ih (hi - ((lo + hi) / 2 + 1)) (by omega)
              ((lo + hi) / 2 + 1) hi rfl
            have hm := Nat.log_mono_right (b := 2)
              (by omega : hi - ((lo + hi) / 2 + 1) ≤ (hi - lo) / 2)
            omega
          · have hs := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
            have hm := Nat.log_mono_right (b := 2)
              (by omega : (lo + hi) / 2 - lo ≤ (hi - lo) / 2)
            omega
      · rw [lowerBoundSteps, dite_eq_right h]
        omega

/-- The suffix of row `r` of the suffix array of `s`, truncated to `m` letters: the key compared
with the pattern during the search. -/
def rowKey (s : List α) (m r : ℕ) : List α :=
  (suffix s ((suffixArray s).getD r 0)).take m

private theorem rowKey_mono {β : Type*} [LinearOrder β] (s : List β) (m : ℕ)
    {i j : ℕ} (hij : i ≤ j) (hj : j < s.length) : rowKey s m i ≤ rowKey s m j := by
  exact take_le_take (suffix_row_mono s hij hj) m

private theorem rowKey_lt_initial {β : Type*} [LinearOrder β] (s P : List β)
    (i j : ℕ) (_hi : 0 ≤ i) (hij : i ≤ j) (hj : j < s.length)
    (hp : decide (rowKey s P.length j < P) = true) :
    decide (rowKey s P.length i < P) = true := by
  simp only [decide_eq_true_eq] at hp ⊢
  exact lt_of_le_of_lt (rowKey_mono s P.length hij hj) hp

private theorem rowKey_le_initial {β : Type*} [LinearOrder β] (s P : List β)
    (i j : ℕ) (_hi : 0 ≤ i) (hij : i ≤ j) (hj : j < s.length)
    (hp : decide (rowKey s P.length j ≤ P) = true) :
    decide (rowKey s P.length i ≤ P) = true := by
  simp only [decide_eq_true_eq] at hp ⊢
  exact le_trans (rowKey_mono s P.length hij hj) hp

/-- Suffix-array search (Manber and Myers 1993): the row interval `[sp, ep)` of the suffixes of
`s` that start with `P`, found by two binary searches over the rows `[0, |s|)`. -/
def saSearch (s P : List α) : ℕ × ℕ :=
  (lowerBound (fun r => decide (rowKey s P.length r < P)) 0 s.length,
    lowerBound (fun r => decide (rowKey s P.length r ≤ P)) 0 s.length)

/-- The search returns a genuine interval of rows: `sp ≤ ep ≤ |s|`. -/
theorem saSearch_bounds (s P : List α) :
    (saSearch s P).1 ≤ (saSearch s P).2 ∧ (saSearch s P).2 ≤ s.length := by
  have hsp := lowerBound_spec (fun r => decide (rowKey s P.length r < P))
    0 s.length (Nat.zero_le _) (rowKey_lt_initial s P)
  have hep := lowerBound_spec (fun r => decide (rowKey s P.length r ≤ P))
    0 s.length (Nat.zero_le _) (rowKey_le_initial s P)
  change _ ≤ _ ∧ _ ≤ s.length
  refine ⟨?_, hep.2.1⟩
  by_contra h
  have hlt := Nat.lt_of_not_ge h
  have hr := lt_of_lt_of_le hlt hsp.2.1
  have hp := hsp.2.2.1 _ (Nat.zero_le _) hlt
  have hn := hep.2.2.2 _ le_rfl hr
  simp only [decide_eq_true_eq] at hp
  have ht : decide (rowKey s P.length
      (lowerBound (fun r => decide (rowKey s P.length r ≤ P)) 0 s.length) ≤ P) = true :=
    decide_eq_true hp.le
  rw [ht] at hn
  contradiction

/-- **Suffix-array search is correct**: a row `r < |s|` lies in `[sp, ep)` exactly when the suffix
of row `r` starts with `P`. -/
theorem saSearch_spec (s P : List α) (r : ℕ) (hr : r < s.length) :
    (saSearch s P).1 ≤ r ∧ r < (saSearch s P).2 ↔
      P <+: suffix s ((suffixArray s).getD r 0) := by
  have hsp := lowerBound_spec (fun r => decide (rowKey s P.length r < P))
    0 s.length (Nat.zero_le _) (rowKey_lt_initial s P)
  have hep := lowerBound_spec (fun r => decide (rowKey s P.length r ≤ P))
    0 s.length (Nat.zero_le _) (rowKey_le_initial s P)
  rw [List.prefix_iff_eq_take]
  change _ ≤ r ∧ r < _ ↔ P = rowKey s P.length r
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn := hsp.2.2.2 r hlo hr
    have hp := hep.2.2.1 r (Nat.zero_le _) hhi
    simp only [decide_eq_false_iff_not] at hn
    simp only [decide_eq_true_eq] at hp
    exact (le_antisymm hp (le_of_not_gt hn)).symm
  · intro heq
    constructor
    · by_contra h
      have hp := hsp.2.2.1 r (Nat.zero_le _) (Nat.lt_of_not_ge h)
      simp [← heq] at hp
    · by_contra h
      have hn := hep.2.2.2 r (Nat.le_of_not_gt h) hr
      simp [← heq] at hn

end Cslib.Bioinformatics.Indexing.SuffixArraySearch
