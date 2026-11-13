/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray
public import CSLibExt.Bioinformatics.Indexing.BWT

/-!
# Suffix arrays and the Burrows–Wheeler transform; FM-index locate

With a unique sentinel smaller than every letter appended to the text, comparing two rotations of
`t$` is the same as comparing the suffixes they start with: the sentinel ends the comparison
before the rotations wrap around. Hence the sorted rotation matrix of Burrows and Wheeler (1994)
is the suffix array of `t$` (Manber and Myers 1993), the Burrows–Wheeler transform is read off
the suffix array as `bwt[r] = t$[SA[r] - 1]` (cyclically), and the row intervals of the
FM-index backward search (Ferragina and Manzini 2000) are suffix-array intervals: the occurrences
of a pattern are the text positions `SA[sp], …, SA[ep - 1]`.

The LF-mapping steps from a row to the row of the text position one to the left,
`SA[r] = SA[LF r] + 1` when `SA[r] > 0`. *Locate* with a sampled suffix array (Ferragina and
Manzini 2000) stores `SA[r]` only for some rows and walks the LF-mapping from row `r` until it
reaches a stored row, adding the number of steps.

Here `SA` is `suffixArray (withSentinel t)` from
`CSLibExt.Algorithms.Lean.DataStructures.SuffixArray`, applied to the text with the sentinel `⊥`
appended, and the transform, LF-mapping and backward search are those of
`CSLibExt.Bioinformatics.Indexing.BWT`.

## Main results

* `rotate_lt_rotate_iff`: rotations of `t$` compare as the suffixes they start with.
* `sortedRotations_eq_suffixArray`: **the Burrows–Wheeler matrix order is the suffix array of
  `t$`**.
* `bwt_eq_map_suffixArray`: **`bwt[r] = t$[SA[r] - 1]`**, cyclically.
* `backwardSearch_iff_prefix`: **backward-search intervals are suffix-array intervals**: row `r`
  lies in `[sp, ep)` exactly when `P` is a prefix of `t.drop SA[r]`.
* `mem_occurrences_iff`, `occurrences_nodup`, `occurrences_length`: the positions
  `SA[sp], …, SA[ep - 1]` are exactly the occurrences of `P`, each once.
* `suffixArray_getD_lf`, `suffixArray_getD_eq_lf_add_one`: `SA[LF r] = SA[r] - 1` (cyclically).
* `locate_eq`: **sampled-suffix-array locate is correct** when the samples are correct and every
  row of text position `0` is sampled; `locateSteps_le`: if every row whose position is a
  multiple of `s` is sampled, locate makes at most `SA[r] mod s` LF steps (at most `s - 1`).

## Cost model

No complexity is claimed for building the suffix array (`List.mergeSort` on whole suffixes).
Locate costs at most `s - 1` LF steps when the rows of the text positions that are multiples of
`s` are sampled (`locateSteps_le`), counted in LF steps only. No cost is claimed for a single
LF step: `locateAux` is hardwired to `BWT.lf`, whose `countLess`, `rank`, and `List.getD`
operations rescan the list, so this API cannot realize a directory-backed constant-time LF
step. A constant-time LF step would require parameterizing `locate` by an LF oracle/index
structure with the required correctness property.

## References

* M. Burrows and D. J. Wheeler, *A block-sorting lossless data compression algorithm*, Digital
  Systems Research Center Research Report 124, 1994.
* P. Ferragina and G. Manzini, *Opportunistic data structures with applications*, Proc. 41st
  IEEE Symposium on Foundations of Computer Science (FOCS 2000), 390–398.
* U. Manber and G. Myers, *Suffix arrays: a new method for on-line string searches*, SIAM J.
  Comput. 22 (1993), 935–948.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Indexing.SuffixArrayBWT

open Cslib.Algorithms.Lean.SuffixArray Cslib.Bioinformatics.Indexing.BWT

variable {α : Type*} [LinearOrder α]

omit [LinearOrder α] in
private theorem length_withSentinel (t : List α) : (withSentinel t).length = t.length + 1 := by
  simp [withSentinel]

omit [LinearOrder α] in
private theorem rotate_withSentinel (t : List α) (i : ℕ) (hi : i ≤ t.length) :
    (withSentinel t).rotate i = (t.drop i).map (↑) ++ ⊥ :: (t.take i).map (↑) := by
  rw [List.rotate_eq_drop_append_take (by simp [withSentinel]; omega)]
  unfold withSentinel
  have hm : i ≤ (t.map (WithBot.some)).length := by simpa using hi
  rw [List.drop_append_of_le_length hm, List.take_append_of_le_length hm]
  simp only [← List.map_drop, ← List.map_take, List.append_assoc, List.singleton_append]

omit [LinearOrder α] in
private theorem suffix_withSentinel (t : List α) (i : ℕ) (hi : i ≤ t.length) :
    suffix (withSentinel t) i = (t.drop i).map (↑) ++ [⊥] := by
  unfold suffix withSentinel
  have hm : i ≤ (t.map (WithBot.some)).length := by simpa using hi
  rw [List.drop_append_of_le_length hm, List.map_drop]

private theorem lt_sentinel_iff (u v : List α) (huv : u ≠ v) (X Y : List (WithBot α)) :
    u.map WithBot.some ++ ⊥ :: X < v.map WithBot.some ++ ⊥ :: Y ↔
      u.map WithBot.some ++ [⊥] < v.map WithBot.some ++ [(⊥ : WithBot α)] := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact absurd rfl huv
    | cons b v =>
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append]
      constructor <;> intro _ <;> exact List.Lex.rel (WithBot.bot_lt_coe b)
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append]
      constructor <;> intro h <;>
        exact absurd h (not_lt.mpr (le_of_lt (List.Lex.rel (WithBot.bot_lt_coe a))))
    | cons b v =>
      simp only [List.map_cons, List.cons_append, List.cons_lt_cons_iff]
      by_cases hab : a = b
      · subst hab
        have huv' : u ≠ v := fun h => huv (h ▸ rfl)
        simp [ih v huv']
      · have hab' : (a : WithBot α) ≠ b := fun h => hab (WithBot.coe_injective h)
        simp [hab']

/-- **Rotations of `t$` compare as suffixes**: for `i, j ≤ |t|`, rotation `i` of `withSentinel t`
is smaller than rotation `j` exactly when suffix `i` is smaller than suffix `j`. -/
theorem rotate_lt_rotate_iff (t : List α) {i j : ℕ} (hi : i ≤ t.length) (hj : j ≤ t.length) :
    (withSentinel t).rotate i < (withSentinel t).rotate j ↔
      suffix (withSentinel t) i < suffix (withSentinel t) j := by
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : t.drop i ≠ t.drop j := by
      intro h
      have := congrArg List.length h
      simp only [List.length_drop] at this
      omega
    rw [rotate_withSentinel t i hi, rotate_withSentinel t j hj, suffix_withSentinel t i hi,
      suffix_withSentinel t j hj]
    exact lt_sentinel_iff _ _ hne _ _

omit [LinearOrder α] in
private theorem suffix_injective (t : List α) {i j : ℕ} (hi : i ≤ t.length) (hj : j ≤ t.length)
    (h : suffix (withSentinel t) i = suffix (withSentinel t) j) : i = j := by
  have := congrArg List.length h
  simp only [suffix_length, length_withSentinel] at this
  omega

omit [LinearOrder α] in
private theorem getD_of_lt {β : Type*} (l : List β) (d : β) {r : ℕ} (h : r < l.length) :
    l.getD r d = l[r] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem length_bwt (t : List α) : (bwt t).length = t.length + 1 := by
  unfold bwt sortedRotations
  rw [List.length_map, (List.mergeSort_perm _ _).length_eq, List.length_range]

private theorem mem_sortedRotations (t : List α) {i : ℕ} :
    i ∈ sortedRotations t ↔ i ≤ t.length := by
  unfold sortedRotations
  rw [((List.mergeSort_perm _ _ : (sortedRotations t).Perm _)).mem_iff, List.mem_range]
  omega

private theorem mem_suffixArray_withSentinel (t : List α) {i : ℕ} :
    i ∈ suffixArray (withSentinel t) ↔ i ≤ t.length := by
  rw [mem_suffixArray_iff, length_withSentinel]
  omega

private theorem pairwise_sortedRotations (t : List α) :
    (sortedRotations t).Pairwise
      (fun i j => suffix (withSentinel t) i < suffix (withSentinel t) j) := by
  have hle : (sortedRotations t).Pairwise
      (fun i j => (withSentinel t).rotate i ≤ (withSentinel t).rotate j) := by
    have h := List.pairwise_mergeSort
      (le := fun i j => decide ((withSentinel t).rotate i ≤ (withSentinel t).rotate j))
      (fun i j k hij hjk => by
        simpa only [decide_eq_true_eq] using
          le_trans (of_decide_eq_true hij) (of_decide_eq_true hjk))
      (fun i j => by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using
          le_total ((withSentinel t).rotate i) ((withSentinel t).rotate j))
      (List.range (t.length + 1))
    unfold sortedRotations
    simpa only [decide_eq_true_eq] using h
  have hnd : (sortedRotations t).Nodup :=
    (List.mergeSort_perm _ _ : (sortedRotations t).Perm _).nodup_iff.mpr List.nodup_range
  refine (hle.and hnd).imp_of_mem fun {i j} hi hj ⟨h, hne⟩ => ?_
  have hi' := (mem_sortedRotations t).mp hi
  have hj' := (mem_sortedRotations t).mp hj
  rcases lt_trichotomy (suffix (withSentinel t) i) (suffix (withSentinel t) j) with hl | he | hg
  · exact hl
  · exact absurd (suffix_injective t hi' hj' he) hne
  · exact absurd h (not_le.mpr ((rotate_lt_rotate_iff t hj' hi').mpr hg))

private theorem pairwise_suffixArray_withSentinel (t : List α) :
    (suffixArray (withSentinel t)).Pairwise
      (fun i j => suffix (withSentinel t) i < suffix (withSentinel t) j) := by
  have hle := pairwise_suffix_suffixArray (withSentinel t)
  rw [List.pairwise_map] at hle
  refine (hle.and (suffixArray_nodup _)).imp_of_mem fun {i j} hi hj ⟨h, hne⟩ => ?_
  exact lt_of_le_of_ne h fun he => hne (suffix_injective t
    ((mem_suffixArray_withSentinel t).mp hi) ((mem_suffixArray_withSentinel t).mp hj) he)

/-- **The Burrows–Wheeler matrix is the suffix array of `t$`**: sorting the rotations of
`withSentinel t` orders the starting positions exactly as sorting its suffixes. -/
theorem sortedRotations_eq_suffixArray (t : List α) :
    sortedRotations t = suffixArray (withSentinel t) := by
  refine List.Perm.eq_of_pairwise (fun i j _ _ h₁ h₂ => absurd (h₁.trans h₂) (lt_irrefl _))
    (pairwise_sortedRotations t) (pairwise_suffixArray_withSentinel t) ?_
  refine (List.mergeSort_perm _ _).trans ?_
  rw [← length_withSentinel t]
  exact (suffixArray_perm _).symm

omit [LinearOrder α] in
private theorem getLastD_rotate (t : List α) (i : ℕ) (hi : i ≤ t.length) :
    ((withSentinel t).rotate i).getLastD ⊥ =
      (withSentinel t).getD ((i + t.length) % (t.length + 1)) ⊥ := by
  rw [rotate_withSentinel t i hi]
  cases i with
  | zero =>
    have hm : (0 + t.length) % (t.length + 1) = t.length := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_succ_self _)]
    rw [hm]
    simp [withSentinel, List.getD_eq_getElem?_getD]
  | succ k =>
    have hk : k < t.length := by omega
    have hm : (k + 1 + t.length) % (t.length + 1) = k := by
      rw [show k + 1 + t.length = k + (t.length + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hm, List.take_succ_eq_append_getElem hk]
    simp only [List.map_append, List.map_singleton]
    rw [← List.cons_append, ← List.append_assoc, List.getLastD_concat]
    rw [List.getD_eq_getElem?_getD, withSentinel,
      List.getElem?_append_left (by simpa using hk), List.getElem?_map,
      List.getElem?_eq_getElem hk]
    rfl

/-- **The transform from the suffix array**: `bwt[r] = t$[SA[r] - 1]`, the letter cyclically
before the suffix of row `r` (the sentinel for the row of the whole text, `SA[r] = 0`). -/
theorem bwt_eq_map_suffixArray (t : List α) :
    bwt t = (suffixArray (withSentinel t)).map
      fun i => (withSentinel t).getD ((i + t.length) % (t.length + 1)) ⊥ := by
  rw [bwt, sortedRotations_eq_suffixArray]
  exact List.map_congr_left fun i hi =>
    getLastD_rotate t i ((mem_suffixArray_withSentinel t).mp hi)

omit [LinearOrder α] in
private theorem prefix_map_sentinel (P u : List α) (v : List (WithBot α)) :
    P.map (↑) <+: u.map (↑) ++ ⊥ :: v ↔ P <+: u := by
  induction u generalizing P with
  | nil => cases P <;> simp
  | cons a u ih =>
    cases P with
    | nil => simp
    | cons c P => simpa using and_congr Iff.rfl (ih P)

private theorem getD_suffixArray_le (t : List α) {r : ℕ} (hr : r < t.length + 1) :
    (suffixArray (withSentinel t)).getD r 0 ≤ t.length := by
  have hr' : r < (suffixArray (withSentinel t)).length := by
    rwa [suffixArray_length, length_withSentinel]
  rw [getD_of_lt _ _ hr']
  exact (mem_suffixArray_withSentinel t).mp (List.getElem_mem hr')

/-- **Backward-search intervals are suffix-array intervals**: row `r ≤ |t|` lies in the interval
`[sp, ep)` computed by backward search on `bwt t` exactly when `P` is a prefix of the suffix of
`t` at position `SA[r]`. -/
theorem backwardSearch_iff_prefix (t P : List α) (r : ℕ) (hr : r < t.length + 1) :
    (backwardSearch (bwt t) P).1 ≤ r ∧ r < (backwardSearch (bwt t) P).2 ↔
      P <+: t.drop ((suffixArray (withSentinel t)).getD r 0) := by
  rw [backwardSearch_spec t P r hr, sortedRotations_eq_suffixArray,
    rotate_withSentinel t _ (getD_suffixArray_le t hr)]
  exact prefix_map_sentinel _ _ _

/-- The occurrences of `P` reported by the FM-index: the suffix-array entries
`SA[sp], …, SA[ep - 1]` of the backward-search interval. The BWT and the interval are
bound once with `let` and reused, so one query builds the BWT and runs the backward search
once, not three times. -/
def occurrences (t P : List α) : List ℕ :=
  let L := bwt t
  let interval := backwardSearch L P
  ((suffixArray (withSentinel t)).drop interval.1).take (interval.2 - interval.1)

/-- **The reported positions are exactly the occurrences**: `i` is reported for `P` exactly when
`i ≤ |t|` and `P` is a prefix of `t.drop i` (the empty pattern occurs at all `|t| + 1`
positions). -/
theorem mem_occurrences_iff (t P : List α) (i : ℕ) :
    i ∈ occurrences t P ↔ i ≤ t.length ∧ P <+: t.drop i := by
  have hb := backwardSearch_bounds (bwt t) P
  have hlen : (bwt t).length = t.length + 1 := length_bwt t
  rw [hlen] at hb
  set sp := (backwardSearch (bwt t) P).1
  set ep := (backwardSearch (bwt t) P).2
  set SA := suffixArray (withSentinel t)
  have hSA : SA.length = t.length + 1 := by simp [SA, length_withSentinel]
  have hlen' : (occurrences t P).length = ep - sp := by
    simp only [occurrences, List.length_take, List.length_drop]
    change min (ep - sp) (SA.length - sp) = ep - sp
    omega
  have hget : ∀ k (hk : k < (occurrences t P).length),
      (occurrences t P)[k] = SA.getD (sp + k) 0 := by
    intro k hk
    rw [getD_of_lt _ _ (by omega)]
    simp only [occurrences, List.getElem_take, List.getElem_drop]
    rfl
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem h
    have hr : sp + k < t.length + 1 := by omega
    have hspec := (backwardSearch_iff_prefix t P (sp + k) hr).mp ⟨by omega, by omega⟩
    rw [hget k hk] at he
    rw [← he]
    exact ⟨getD_suffixArray_le t hr, hspec⟩
  · rintro ⟨hi, hp⟩
    have hm : i ∈ SA := (mem_suffixArray_withSentinel t).mpr hi
    obtain ⟨r, hr, he⟩ := List.getElem_of_mem hm
    have hr' : r < t.length + 1 := by omega
    obtain ⟨hspr, hrep⟩ := (backwardSearch_iff_prefix t P r hr').mpr (by
      rw [getD_of_lt _ _ hr, he]
      exact hp)
    refine List.mem_iff_getElem.mpr ⟨r - sp, by omega, ?_⟩
    rw [hget _ (by omega), show sp + (r - sp) = r by omega, getD_of_lt _ _ hr, he]

/-- Each occurrence is reported once. -/
theorem occurrences_nodup (t P : List α) : (occurrences t P).Nodup :=
  ((suffixArray_nodup _).sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)

/-- The number of reported positions is the length `ep - sp` of the backward-search interval. -/
theorem occurrences_length (t P : List α) :
    (occurrences t P).length = (backwardSearch (bwt t) P).2 - (backwardSearch (bwt t) P).1 := by
  have hb := backwardSearch_bounds (bwt t) P
  have hlen : (bwt t).length = t.length + 1 := length_bwt t
  simp only [occurrences, List.length_take, List.length_drop, suffixArray_length,
    length_withSentinel]
  rw [hlen] at hb
  omega

/-- **LF in suffix-array terms**: for a row `r ≤ |t|`, `LF r` is a row and
`SA[LF r] = SA[r] - 1` cyclically (`SA[LF r] = |t|` when `SA[r] = 0`). -/
theorem suffixArray_getD_lf (t : List α) (r : ℕ) (hr : r < t.length + 1) :
    lf (bwt t) r < t.length + 1 ∧
      (suffixArray (withSentinel t)).getD (lf (bwt t) r) 0 =
        ((suffixArray (withSentinel t)).getD r 0 + t.length) % (t.length + 1) := by
  rw [← sortedRotations_eq_suffixArray]
  exact sortedRotations_getD_lf t r hr

/-- **The LF step moves one position left in the text**: `SA[r] = SA[LF r] + 1` when
`SA[r] > 0`. -/
theorem suffixArray_getD_eq_lf_add_one (t : List α) (r : ℕ) (hr : r < t.length + 1)
    (hpos : 0 < (suffixArray (withSentinel t)).getD r 0) :
    (suffixArray (withSentinel t)).getD r 0 =
      (suffixArray (withSentinel t)).getD (lf (bwt t) r) 0 + 1 := by
  rw [(suffixArray_getD_lf t r hr).2]
  have hle := getD_suffixArray_le t hr
  set i := (suffixArray (withSentinel t)).getD r 0
  rw [show i + t.length = (i - 1) + (t.length + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `k` steps of sampled-suffix-array locate from row `r`: return the stored value of the first
sampled row reached along the LF-mapping, plus the number of LF steps taken. `sample r` is the
stored value `SA[r]` of row `r`, if any. -/
def locateAux (L : List (WithBot α)) (sample : ℕ → Option ℕ) : ℕ → ℕ → ℕ
  | 0, r => (sample r).getD 0
  | k + 1, r =>
    match sample r with
    | some v => v
    | none => locateAux L sample k (lf L r) + 1

/-- Sampled-suffix-array locate (Ferragina and Manzini 2000): the text position of row `r` from
the last column `L` and the samples, with at most `|L|` LF steps. -/
def locate (L : List (WithBot α)) (sample : ℕ → Option ℕ) (r : ℕ) : ℕ :=
  locateAux L sample L.length r

/-- The number of LF steps `locateAux L sample k r` takes. -/
def locateSteps (L : List (WithBot α)) (sample : ℕ → Option ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, r =>
    match sample r with
    | some _ => 0
    | none => locateSteps L sample k (lf L r) + 1

private theorem locateAux_eq (t : List α) (sample : ℕ → Option ℕ)
    (hsound : ∀ r v, r < t.length + 1 → sample r = some v →
      v = (suffixArray (withSentinel t)).getD r 0)
    (hzero : ∀ r, r < t.length + 1 → (suffixArray (withSentinel t)).getD r 0 = 0 →
      (sample r).isSome) :
    ∀ k r, r < t.length + 1 → (suffixArray (withSentinel t)).getD r 0 ≤ k →
      locateAux (bwt t) sample k r = (suffixArray (withSentinel t)).getD r 0 := by
  intro k
  induction k with
  | zero =>
    intro r hr hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hzero r hr (by omega))
    simp [locateAux, hv, hsound r v hr hv]
  | succ k ih =>
    intro r hr hk
    cases hs : sample r with
    | some v => simp [locateAux, hs, hsound r v hr hs]
    | none =>
      have hpos : 0 < (suffixArray (withSentinel t)).getD r 0 := by
        by_contra h
        have := hzero r hr (by omega)
        simp [hs] at this
      have hl := suffixArray_getD_lf t r hr
      have he := suffixArray_getD_eq_lf_add_one t r hr hpos
      simp only [locateAux, hs]
      rw [ih _ hl.1 (by omega)]
      exact he.symm

/-- **Sampled-suffix-array locate is correct**: if every stored value is correct
(`sample r = some v → v = SA[r]` for rows `r ≤ |t|`) and every row of text position `0` is
sampled, then `locate` returns `SA[r]` for every row `r ≤ |t|`. -/
theorem locate_eq (t : List α) (sample : ℕ → Option ℕ)
    (hsound : ∀ r v, r < t.length + 1 → sample r = some v →
      v = (suffixArray (withSentinel t)).getD r 0)
    (hzero : ∀ r, r < t.length + 1 → (suffixArray (withSentinel t)).getD r 0 = 0 →
      (sample r).isSome)
    (r : ℕ) (hr : r < t.length + 1) :
    locate (bwt t) sample r = (suffixArray (withSentinel t)).getD r 0 := by
  have hlen : (bwt t).length = t.length + 1 := length_bwt t
  rw [locate, hlen]
  exact locateAux_eq t sample hsound hzero _ r hr (by have := getD_suffixArray_le t hr; omega)

private theorem succ_mod_of_ne_zero (m s : ℕ) (h : (m + 1) % s ≠ 0) :
    (m + 1) % s = m % s + 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · have hlt := Nat.mod_lt m hs
    have hm : m + 1 = (m % s + 1) + s * (m / s) := by
      have := Nat.mod_add_div m s
      omega
    rw [hm, Nat.add_mul_mod_self_left] at h ⊢
    rcases Nat.lt_or_ge (m % s + 1) s with h1 | h1
    · exact Nat.mod_eq_of_lt h1
    · exfalso
      apply h
      rw [show m % s + 1 = s by omega, Nat.mod_self]

/-- **Locate takes at most `s - 1` steps**: for `0 < s`, if every row whose text position is
a multiple of `s` is sampled, then from row `r ≤ |t|` locate makes at most `SA[r] mod s` LF
steps (for any amount of fuel `k`). At `s = 0` the `s - 1` bound would be `0` while the
proof only gives `SA[r] mod 0 = SA[r]` steps. -/
theorem locateSteps_le (t : List α) (sample : ℕ → Option ℕ) (s : ℕ) (_hs : 0 < s)
    (hsample : ∀ r, r < t.length + 1 → (suffixArray (withSentinel t)).getD r 0 % s = 0 →
      (sample r).isSome) :
    ∀ k r, r < t.length + 1 →
      locateSteps (bwt t) sample k r ≤ (suffixArray (withSentinel t)).getD r 0 % s := by
  intro k
  induction k with
  | zero => intro r _; simp [locateSteps]
  | succ k ih =>
    intro r hr
    cases hs : sample r with
    | some v => simp [locateSteps, hs]
    | none =>
      have hns : (suffixArray (withSentinel t)).getD r 0 % s ≠ 0 := by
        intro h
        have := hsample r hr h
        simp [hs] at this
      have hpos : 0 < (suffixArray (withSentinel t)).getD r 0 := by
        by_contra h
        apply hns
        rw [show (suffixArray (withSentinel t)).getD r 0 = 0 by omega, Nat.zero_mod]
      have hl := suffixArray_getD_lf t r hr
      have he := suffixArray_getD_eq_lf_add_one t r hr hpos
      simp only [locateSteps, hs]
      have ih' := ih _ hl.1
      rw [he] at hns ⊢
      rw [succ_mod_of_ne_zero _ _ hns]
      omega

end Cslib.Bioinformatics.Indexing.SuffixArrayBWT
