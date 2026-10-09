/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.ZAlgorithm

import Batteries.Data.Vector.Lemmas

/-!
# Boyer-Moore strong-shift preprocessing

Finite indexed bad-character shifts and strong good-suffix shifts are computed once.
The suffix lengths reuse the canonical Z algorithm on one reversed pattern.

Retained Lean is authored by Codex at Adam Kiezun's explicit selection.

## References

Robert S. Boyer and J Strother Moore, *A Fast String Searching Algorithm*, CACM20(10),
1977, pages762-772. The all-occurrences table fills follow Charras and Lecroq:
<http://www-igm.univ-mlv.fr/~lecroq/string/node14.html>.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StringMatching.BoyerMoore

@[no_expose] private def badScan {σ m : Nat} (p : Vector (Fin σ) m)
    (i : Nat) (table : Vector Nat σ) : TimeM Nat (Vector Nat σ) :=
  if hi : i + 1 < m then do
    TimeM.tick 1
    badScan p (i + 1) (table.set p[i].val (m - 1 - i))
  else
    pure table
termination_by m - i

@[no_expose] private def prefixFill {m : Nat} (cutoff j : Nat)
    (table : Vector Nat m) : TimeM Nat (Nat × Vector Nat m) :=
  if hj : j < min cutoff m then do
    TimeM.tick 1
    let table := if table[j] = m then table.set j cutoff else table
    prefixFill cutoff (j + 1) table
  else
    pure (j, table)
termination_by min cutoff m - j

@[no_expose] private def borderScan {m : Nat} (suffix : Vector Nat m)
    (remaining : Nat) (hremaining : remaining ≤ m) (j : Nat) (table : Vector Nat m) :
    TimeM Nat (Nat × Vector Nat m) :=
  match remaining with
  | 0 => pure (j, table)
  | i + 1 => do
      TimeM.tick 1
      let filled ← if suffix[i] = i + 1 then prefixFill (m - 1 - i) j table
        else pure (j, table)
      borderScan suffix i (by omega) filled.1 filled.2

@[no_expose] private def suffixScan {m : Nat} (suffix : Vector Nat m)
    (i : Nat) (table : Vector Nat m) : TimeM Nat (Vector Nat m) :=
  if hi : i + 1 < m then do
    TimeM.tick 1
    suffixScan suffix (i + 1) (table.set (m - 1 - suffix[i]) (m - 1 - i))
  else
    pure table
termination_by m - i

/-- Compute indexed bad-character and strong good-suffix tables for a finite alphabet.
The event cost includes table slots, copies, fill iterations and canonical Z events;
it does not count machine instructions or unbounded-integer bit operations. -/
public def preprocess {σ m : Nat} (p : Vector (Fin σ) m) :
    TimeM Nat (Vector Nat σ × Vector Nat m) := do
  TimeM.tick σ
  let bad := Vector.replicate σ m
  if hm : 0 < m then do
    let bad ← badScan p 0 bad
    TimeM.tick m
    let reversed := p.reverse
    let z ← computeZ reversed
    TimeM.tick m
    let suffix := z.reverse
    TimeM.tick m
    let filled ← borderScan suffix m (by omega) 0 (Vector.replicate m m)
    let good ← suffixScan suffix 0 filled.2
    pure (bad, good)
  else
    pure (bad, Vector.replicate m m)

private lemma badScan_time {σ m : Nat} (p : Vector (Fin σ) m) (i : Nat)
    (table : Vector Nat σ) : (badScan p i table).time = m - 1 - i := by
  rw [badScan]
  split
  · simp only [TimeM.time_bind, TimeM.time_tick]
    rw [badScan_time]
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by m - i

private lemma prefixFill_time {m : Nat} (cutoff j : Nat) (table : Vector Nat m) :
    (prefixFill cutoff j table).time = min cutoff m - j := by
  rw [prefixFill]
  split
  · simp only [TimeM.time_bind, TimeM.time_tick]
    rw [prefixFill_time]
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by min cutoff m - j

private lemma prefixFill_index {m : Nat} (cutoff j : Nat) (table : Vector Nat m) :
    (prefixFill cutoff j table).ret.1 = max j (min cutoff m) := by
  rw [prefixFill]
  split
  · simp only [TimeM.ret_bind]
    rw [prefixFill_index]
    omega
  · simp only [TimeM.ret_pure]
    omega
termination_by min cutoff m - j

private lemma suffixScan_time {m : Nat} (suffix : Vector Nat m) (i : Nat)
    (table : Vector Nat m) : (suffixScan suffix i table).time = m - 1 - i := by
  rw [suffixScan]
  split
  · simp only [TimeM.time_bind, TimeM.time_tick]
    rw [suffixScan_time]
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by m - i

private lemma borderScan_stats {m : Nat} (suffix : Vector Nat m)
    (remaining : Nat) (hremaining : remaining ≤ m) (j : Nat) (table : Vector Nat m) :
    j ≤ (borderScan suffix remaining hremaining j table).ret.1 ∧
    (borderScan suffix remaining hremaining j table).ret.1 ≤ max j (m - 1) ∧
    (borderScan suffix remaining hremaining j table).time =
      remaining + (borderScan suffix remaining hremaining j table).ret.1 - j := by
  induction remaining generalizing j table with
  | zero => simp only [borderScan, TimeM.ret_pure, TimeM.time_pure]; omega
  | succ i ih =>
      rw [borderScan]
      simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick]
      split
      · simp only [TimeM.ret_bind, TimeM.time_bind]
        have hf := prefixFill_index (m - 1 - i) j table
        have ht := prefixFill_time (m - 1 - i) j table
        have hh := ih (by omega) (prefixFill (m - 1 - i) j table).ret.1
          (prefixFill (m - 1 - i) j table).ret.2
        simp only [hf, ht] at hh ⊢
        omega
      · simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.ret_pure, TimeM.time_pure]
        have hh := ih (by omega) j table
        omega

private lemma preprocess_time_le_z {σ m : Nat} (p : Vector (Fin σ) m) (hm : 0 < m) :
    (preprocess p).time ≤ σ + 7 * m - 3 + (computeZ p.reverse).time := by
  rw [preprocess]
  simp only [TimeM.time_bind, TimeM.time_tick, dite_eq_left hm, TimeM.time_pure,
    badScan_time, suffixScan_time]
  have hs := borderScan_stats (computeZ p.reverse).ret.reverse m (Nat.le_refl m) 0
    (Vector.replicate m m)
  omega

/-- The executed preprocessor's selected-event cost, including alphabet-table
initialization. This is not a word-RAM or bit-cost bound. -/
public theorem preprocess_time_le {σ m : Nat} (p : Vector (Fin σ) m) :
    (preprocess p).time ≤ if m = 0 then σ else σ + 10 * m - 6 := by
  by_cases hm : m = 0
  · simp [preprocess, hm]
  · have hpos : 0 < m := by omega
    have ht := preprocess_time_le_z p hpos
    have hz := computeZ_time_le p.reverse
    simp only [ite_eq_right hm]
    omega

private lemma badScan_spec {σ m : Nat} (p : Vector (Fin σ) m) (i : Nat)
    (table : Vector Nat σ) (c : Fin σ) :
    ((badScan p i table).ret[c.val] = table[c.val] ∧
      ∀ (k : Nat) (hk : k + 1 < m), i ≤ k → p[k] ≠ c) ∨
    ∃ (j : Nat) (hj : j + 1 < m), i ≤ j ∧ p[j] = c ∧
      (badScan p i table).ret[c.val] = m - 1 - j ∧
      ∀ (k : Nat) (hk : k + 1 < m), i ≤ k → p[k] = c → k ≤ j := by
  rw [badScan]
  split
  · rename_i hi
    simp only [TimeM.ret_bind]
    rcases badScan_spec p (i + 1) (table.set p[i].val (m - 1 - i)) c with h | h
    · rcases h with ⟨hr, hn⟩
      by_cases he : p[i] = c
      · right
        refine ⟨i, hi, Nat.le_refl i, he, ?_, ?_⟩
        · simpa only [he, Vector.getElem_set_self] using hr
        · intro k hk hik hpc
          by_contra hgt
          exact hn k hk (by omega) hpc
      · left
        have hne : p[i].val ≠ c.val := fun h => he (Fin.ext h)
        refine ⟨?_, ?_⟩
        · simpa only [Vector.getElem_set_ne (p[i].isLt) c.isLt hne] using hr
        · intro k hk hik hpc
          by_cases hki : k = i
          · subst k
            exact he hpc
          · exact hn k hk (by omega) hpc
    · rcases h with ⟨j, hj, hij, hp, hr, hmax⟩
      right
      refine ⟨j, hj, by omega, hp, hr, ?_⟩
      intro k hk hik hpc
      by_cases hki : k = i
      · omega
      · exact hmax k hk (by omega) hpc
  · left
    simp only [TimeM.ret_pure]
    refine ⟨by trivial, ?_⟩
    intro k hk hik
    omega
termination_by m - i

private lemma preprocess_bad_ret {σ m : Nat} (p : Vector (Fin σ) m) :
    (preprocess p).ret.1 = (badScan p 0 (Vector.replicate σ m)).ret := by
  rw [preprocess]
  simp only [TimeM.ret_bind]
  split
  · simp only [TimeM.ret_bind, TimeM.ret_pure]
  · rename_i hm
    rw [badScan]
    simp only [show ¬0 + 1 < m by omega, ↓reduceDIte, TimeM.ret_pure]

/-- A bad-character slot is the distance from the last pattern position to the
rightmost occurrence before that position, or the pattern length if absent. -/
public theorem preprocess_badCharacter {σ m : Nat} (p : Vector (Fin σ) m) (c : Fin σ) :
    ((preprocess p).ret.1[c.val] = m ∧
      ∀ (k : Nat) (hk : k + 1 < m), p[k] ≠ c) ∨
    ∃ (j : Nat) (hj : j + 1 < m), p[j] = c ∧
      (preprocess p).ret.1[c.val] = m - 1 - j ∧
      ∀ (k : Nat) (hk : k + 1 < m), p[k] = c → k ≤ j := by
  rw [preprocess_bad_ret]
  rcases badScan_spec p 0 (Vector.replicate σ m) c with ⟨hr, hn⟩ | ⟨j, hj, _, hp, hr, hh⟩
  · left
    refine ⟨?_, ?_⟩
    · simpa only [Vector.getElem_replicate] using hr
    · intro k hk
      exact hn k hk (Nat.zero_le k)
  · right
    exact ⟨j, hj, hp, hr, fun k hk => hh k hk (Nat.zero_le k)⟩

private lemma reverseZ_prefix {σ m : Nat} (p : Vector (Fin σ) m) (i : Fin m) (q : Nat) :
    q ≤ (computeZ p.reverse).ret.reverse[i.val] ↔
      q ≤ i.val + 1 ∧ ∀ (k : Nat) (_hk : k < q),
        p[i.val - k] = p[m - 1 - k]'(by have := i.isLt; omega) := by
  have hi := i.isLt
  have hr : m - 1 - i.val < m := by omega
  rw [Vector.getElem_reverse i.isLt]
  have hc := computeZ_prefix_iff p.reverse ⟨m - 1 - i.val, hr⟩ q
  dsimp only at hc
  change q ≤ (computeZ p.reverse).ret[m - 1 - i.val] ↔ _
  rw [hc]
  constructor
  · rintro ⟨hq, he⟩
    refine ⟨by omega, ?_⟩
    intro k hk
    have hkm : k < m := by omega
    have hrkm : m - 1 - i.val + k < m := by omega
    have he' := congrArg (fun xs : List (Fin σ) => xs[k]?) he
    simp only [List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
      Vector.getElem?_toList, Vector.getElem?_eq_getElem hkm,
      Vector.getElem?_eq_getElem hrkm, Option.some.injEq] at he'
    rw [Vector.getElem_reverse hkm, Vector.getElem_reverse hrkm] at he'
    have ha : m - 1 - (m - 1 - i.val + k) = i.val - k := by omega
    simpa only [ha] using he'.symm
  · rintro ⟨hq, he⟩
    refine ⟨by omega, ?_⟩
    apply List.ext_getElem?
    intro k
    by_cases hk : k < q
    · have hkm : k < m := by omega
      have hrkm : m - 1 - i.val + k < m := by omega
      simp only [List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
        Vector.getElem?_toList, Vector.getElem?_eq_getElem hkm,
        Vector.getElem?_eq_getElem hrkm, Option.some.injEq]
      rw [Vector.getElem_reverse hkm, Vector.getElem_reverse hrkm]
      have ha : m - 1 - (m - 1 - i.val + k) = i.val - k := by omega
      simpa only [ha] using (he k hk).symm
    · simp only [List.getElem?_take, ite_eq_right hk]

private lemma reverseZ_isSuffix {σ m : Nat} (p : Vector (Fin σ) m) (i : Fin m) :
    let s := (computeZ p.reverse).ret.reverse[i.val]
    s ≤ i.val + 1 ∧
      (∀ (k : Nat) (_hk : k < s), p[i.val - k] = p[m - 1 - k]'(by have := i.isLt; omega)) ∧
      (s = i.val + 1 ∨ p[i.val - s] ≠ p[m - 1 - s]'(by have := i.isLt; omega)) := by
  dsimp only
  let s := (computeZ p.reverse).ret.reverse[i.val]
  have hs := (reverseZ_prefix p i s).mp (Nat.le_refl s)
  refine ⟨hs.1, hs.2, ?_⟩
  by_cases hlast : s = i.val + 1
  · exact Or.inl hlast
  · right
    intro he
    have hext : s + 1 ≤ (computeZ p.reverse).ret.reverse[i.val] := by
      apply (reverseZ_prefix p i (s + 1)).mpr
      refine ⟨by omega, ?_⟩
      intro k hk
      by_cases hks : k < s
      · exact hs.2 k hks
      · have hkseq : k = s := by omega
        subst k
        exact he
    change s + 1 ≤ s at hext
    omega

private lemma prefixFill_get {m : Nat} (cutoff j : Nat)
    (table : Vector Nat m) (k : Fin m) :
    (prefixFill cutoff j table).ret.2[k.val] =
      if j ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m then cutoff else table[k.val] := by
  rw [prefixFill]
  split
  · rename_i hj
    simp only [TimeM.ret_bind]
    rw [prefixFill_get]
    by_cases htable : table[j] = m
    · simp only [htable, ↓reduceIte]
      by_cases hjk : j = k.val
      · subst j
        simp only [Vector.getElem_set_self]
        simp [hj, htable]
      · have hne := Vector.getElem_set_ne (xs := table) (x := cutoff)
          (by omega : j < m) k.isLt hjk
        simp only [hne]
        have hc : (j + 1 ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m) ↔
            (j ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m) := by omega
        simp only [hc]
    · simp only [htable, ↓reduceIte]
      by_cases hjk : j = k.val
      · subst j
        simp [htable]
      · have hc : (j + 1 ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m) ↔
            (j ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m) := by omega
        simp only [hc]
  · simp only [TimeM.ret_pure]
    simp only [show ¬(j ≤ k.val ∧ k.val < min cutoff m ∧ table[k.val] = m) by omega,
      ↓reduceIte]
termination_by min cutoff m - j

@[no_expose] private def Fallback {m : Nat} (suffix : Vector Nat m)
    (r : Nat) (k : Fin m) (d : Nat) : Prop :=
  d = m ∨ ∃ (hd : d < m), r ≤ m - 1 - d ∧ k.val < d ∧
    suffix[m - 1 - d]'(by have := k.isLt; omega) = m - d

private lemma fallback_step {m : Nat} (suffix : Vector Nat m) (i : Nat)
    (hi : i < m) (k : Fin m) (d : Nat) :
    Fallback suffix i k d ↔ Fallback suffix (i + 1) k d ∨
      (d = m - 1 - i ∧ k.val < d ∧ suffix[i] = i + 1) := by
  constructor
  · rintro (he | ⟨hd, hir, hk, hs⟩)
    · exact Or.inl (Or.inl he)
    · by_cases hir' : i + 1 ≤ m - 1 - d
      · exact Or.inl (Or.inr ⟨hd, hir', hk, hs⟩)
      · have he : m - 1 - d = i := by omega
        right
        refine ⟨by omega, hk, ?_⟩
        simpa only [he, show m - d = i + 1 by omega] using hs
  · rintro (h | ⟨he, hk, hs⟩)
    · rcases h with he | ⟨hd, hir, hk, hs⟩
      · exact Or.inl he
      · exact Or.inr ⟨hd, by omega, hk, hs⟩
    · right
      have hd : d < m := by omega
      refine ⟨hd, by omega, hk, ?_⟩
      have he' : m - 1 - d = i := by omega
      simpa only [he', show m - d = i + 1 by omega] using hs

@[no_expose] private def LeastFallback {m : Nat} (suffix : Vector Nat m)
    (r : Nat) (k : Fin m) (value : Nat) : Prop :=
  Fallback suffix r k value ∧ ∀ d, Fallback suffix r k d → value ≤ d

private lemma fallback_min_fill {m : Nat} (suffix : Vector Nat m) (i : Nat)
    (hi : i < m) (hs : suffix[i] = i + 1) (k : Fin m) (old : Nat)
    (hold : LeastFallback suffix (i + 1) k old) :
    LeastFallback suffix i k
      (if k.val < m - 1 - i ∧ old = m then m - 1 - i else old) := by
  change Fallback suffix (i + 1) k old ∧ _ at hold
  change Fallback suffix i k _ ∧ _
  by_cases he : k.val < m - 1 - i ∧ old = m
  · simp only [ite_eq_left he]
    refine ⟨(fallback_step suffix i hi k _).mpr (Or.inr ⟨rfl, he.1, hs⟩), ?_⟩
    intro d hd
    rcases (fallback_step suffix i hi k d).mp hd with hprev | ⟨hd, _, _⟩
    · have hh := hold.2 d hprev
      omega
    · omega
  · simp only [ite_eq_right he]
    refine ⟨(fallback_step suffix i hi k _).mpr (Or.inl hold.1), ?_⟩
    intro d hd
    rcases (fallback_step suffix i hi k d).mp hd with hprev | ⟨hd, hk, _⟩
    · exact hold.2 d hprev
    · by_cases hm : old = m
      · exfalso
        apply he
        exact ⟨by omega, hm⟩
      · rcases hold.1 with hm' | ⟨hbound, hindex, _, _⟩
        · exact False.elim (hm hm')
        · omega

private lemma borderScan_min {m : Nat} (suffix : Vector Nat m)
    (remaining : Nat) (hremaining : remaining ≤ m) (j : Nat) (table : Vector Nat m)
    (hj : j ≤ m - remaining)
    (hfilled : ∀ k : Fin m, k.val < j → table[k.val] ≠ m)
    (hleast : ∀ k : Fin m, LeastFallback suffix remaining k table[k.val]) :
    ∀ k : Fin m, LeastFallback suffix 0 k
      (borderScan suffix remaining hremaining j table).ret.2[k.val] := by
  induction remaining generalizing j table with
  | zero =>
      simpa only [borderScan, TimeM.ret_pure] using hleast
  | succ i ih =>
      rw [borderScan]
      simp only [TimeM.ret_bind]
      split
      · rename_i hs
        simp only [TimeM.ret_bind]
        have hi : i < m := by omega
        have hcut : min (m - 1 - i) m = m - 1 - i := by omega
        have hindex : (prefixFill (m - 1 - i) j table).ret.1 = m - 1 - i := by
          rw [prefixFill_index, hcut]
          omega
        have hget (k : Fin m) :
            (prefixFill (m - 1 - i) j table).ret.2[k.val] =
              if k.val < m - 1 - i ∧ table[k.val] = m then m - 1 - i else table[k.val] := by
          rw [prefixFill_get, hcut]
          by_cases he : table[k.val] = m
          · have hjk : j ≤ k.val := by
              by_contra hn
              exact hfilled k (by omega) he
            simp [he, hjk]
          · simp [he]
        apply ih (by omega) (prefixFill (m - 1 - i) j table).ret.1
          (prefixFill (m - 1 - i) j table).ret.2
        · omega
        · intro k hk
          rw [hget]
          have hkcut : k.val < m - 1 - i := by omega
          by_cases he : table[k.val] = m
          · simp only [ite_eq_left (show k.val < m - 1 - i ∧ table[k.val] = m from ⟨hkcut, he⟩)]
            omega
          · simp [he]
        · intro k
          rw [hget]
          exact fallback_min_fill suffix i hi hs k table[k.val] (hleast k)
      · rename_i hs
        simp only [TimeM.ret_bind, TimeM.ret_pure]
        apply ih (by omega) j table (by omega) hfilled
        intro k
        refine ⟨(fallback_step suffix i (by omega) k _).mpr (Or.inl (hleast k).1), ?_⟩
        intro d hd
        rcases (fallback_step suffix i (by omega) k d).mp hd with hprev | ⟨_, _, hnew⟩
        · exact (hleast k).2 d hprev
        · exact False.elim (hs hnew)

private lemma borderScan_initial_least {m : Nat} (suffix : Vector Nat m) :
    ∀ k : Fin m, LeastFallback suffix 0 k
      (borderScan suffix m (Nat.le_refl m) 0 (Vector.replicate m m)).ret.2[k.val] := by
  apply borderScan_min suffix m (Nat.le_refl m) 0 (Vector.replicate m m)
  · omega
  · intro k hk
    omega
  · intro k
    simp only [Vector.getElem_replicate]
    refine ⟨Or.inl rfl, ?_⟩
    intro d hd
    rcases hd with he | ⟨hbound, hindex, _, _⟩
    · omega
    · omega

@[no_expose] private def ShiftCandidate {m : Nat} (suffix : Vector Nat m)
    (stop : Nat) (k : Fin m) (d : Nat) : Prop :=
  Fallback suffix 0 k d ∨ ∃ (j : Nat) (hj : j + 1 < m),
    j < stop ∧ suffix[j] = m - 1 - k.val ∧ d = m - 1 - j

@[no_expose] private def LeastShift {m : Nat} (suffix : Vector Nat m)
    (stop : Nat) (k : Fin m) (value : Nat) : Prop :=
  ShiftCandidate suffix stop k value ∧ ∀ d, ShiftCandidate suffix stop k d → value ≤ d

private lemma shiftCandidate_step {m : Nat} (suffix : Vector Nat m)
    (i : Nat) (hi : i + 1 < m) (k : Fin m) (d : Nat) :
    ShiftCandidate suffix (i + 1) k d ↔ ShiftCandidate suffix i k d ∨
      (suffix[i] = m - 1 - k.val ∧ d = m - 1 - i) := by
  constructor
  · rintro (hf | ⟨j, hj, hji, hs, hd⟩)
    · exact Or.inl (Or.inl hf)
    · by_cases hjlt : j < i
      · exact Or.inl (Or.inr ⟨j, hj, hjlt, hs, hd⟩)
      · have hjeq : j = i := by omega
        subst j
        exact Or.inr ⟨hs, hd⟩
  · rintro (h | ⟨hs, hd⟩)
    · rcases h with hf | ⟨j, hj, hji, hs, hd⟩
      · exact Or.inl hf
      · exact Or.inr ⟨j, hj, by omega, hs, hd⟩
    · exact Or.inr ⟨i, hi, by omega, hs, hd⟩

private lemma suffixScan_min {m : Nat} (suffix : Vector Nat m) (i : Nat)
    (table : Vector Nat m) (hbound : ∀ j : Fin m, suffix[j.val] ≤ j.val + 1)
    (hleast : ∀ k : Fin m, LeastShift suffix i k table[k.val]) :
    ∀ k : Fin m, LeastShift suffix (m - 1) k (suffixScan suffix i table).ret[k.val] := by
  rw [suffixScan]
  split
  · rename_i hi
    simp only [TimeM.ret_bind]
    apply suffixScan_min suffix (i + 1) _ hbound
    intro k
    have hb := hbound ⟨i, by omega⟩
    dsimp only at hb
    by_cases he : m - 1 - suffix[i] = k.val
    · have hmatch : suffix[i] = m - 1 - k.val := by have := k.isLt; omega
      have hget : (table.set (m - 1 - suffix[i]) (m - 1 - i))[k.val] = m - 1 - i := by
        simpa only [he] using Vector.getElem_set_self (xs := table) (x := m - 1 - i) k.isLt
      rw [hget]
      refine ⟨(shiftCandidate_step suffix i hi k _).mpr (Or.inr ⟨hmatch, rfl⟩), ?_⟩
      intro d hd
      rcases (shiftCandidate_step suffix i hi k d).mp hd with hprev | ⟨_, hd⟩
      · rcases hprev with hf | ⟨j, hj, hji, _, hd⟩
        · rcases hf with hd | ⟨_, _, hk, _⟩ <;> omega
        · omega
      · omega
    · have hget := Vector.getElem_set_ne (xs := table) (x := m - 1 - i)
        (by omega : m - 1 - suffix[i] < m) k.isLt he
      rw [hget]
      refine ⟨(shiftCandidate_step suffix i hi k _).mpr (Or.inl (hleast k).1), ?_⟩
      intro d hd
      rcases (shiftCandidate_step suffix i hi k d).mp hd with hprev | ⟨hmatch, _⟩
      · exact (hleast k).2 d hprev
      · exfalso
        apply he
        have := k.isLt
        omega
  · simp only [TimeM.ret_pure]
    intro k
    refine ⟨?_, ?_⟩
    · rcases (hleast k).1 with hf | ⟨j, hj, _, hs, hd⟩
      · exact Or.inl hf
      · exact Or.inr ⟨j, hj, by omega, hs, hd⟩
    · intro d hd
      apply (hleast k).2 d
      rcases hd with hf | ⟨j, hj, _, hs, hd⟩
      · exact Or.inl hf
      · exact Or.inr ⟨j, hj, by omega, hs, hd⟩
termination_by m - i

private lemma preprocess_leastShift {σ m : Nat} (p : Vector (Fin σ) m) (k : Fin m) :
    LeastShift (computeZ p.reverse).ret.reverse (m - 1) k (preprocess p).ret.2[k.val] := by
  have hm : 0 < m := by have := k.isLt; omega
  rw [preprocess]
  simp only [TimeM.ret_bind, dite_eq_left hm, TimeM.ret_pure]
  apply suffixScan_min _ 0 _ ?_ ?_
  · intro j
    exact (reverseZ_isSuffix p j).1
  · intro j
    have hb := borderScan_initial_least (computeZ p.reverse).ret.reverse j
    refine ⟨Or.inl hb.1, ?_⟩
    intro d hd
    rcases hd with hf | ⟨i, _, hlt, _, _⟩
    · exact hb.2 d hf
    · omega

private lemma shiftCandidate_bounds {m : Nat} (suffix : Vector Nat m)
    (stop : Nat) (k : Fin m) (d : Nat) (hd : ShiftCandidate suffix stop k d) :
    0 < d ∧ d ≤ m := by
  rcases hd with hf | ⟨j, hj, _, _, he⟩
  · rcases hf with he | ⟨hb, _, hk, _⟩
    · have := k.isLt
      omega
    · omega
  · omega

@[no_expose] private def Strong {σ m : Nat} (p : Vector (Fin σ) m) (k : Fin m) (d : Nat) :
    Prop :=
  0 < d ∧
    (∀ t : Fin m, k.val < t.val → d ≤ t.val → p[t.val - d] = p[t.val]) ∧
    (d ≤ k.val → p[k.val - d] ≠ p[k.val])

private lemma shiftCandidate_strong {σ m : Nat} (p : Vector (Fin σ) m) (k : Fin m)
    (d : Nat) (hd : ShiftCandidate (computeZ p.reverse).ret.reverse (m - 1) k d) :
    Strong p k d := by
  have hbounds := shiftCandidate_bounds _ (m - 1) k d hd
  refine ⟨hbounds.1, ?_, ?_⟩
  · intro t hkt hdt
    rcases hd with hf | ⟨j, hj, _, hs, he⟩
    · rcases hf with he | ⟨hdm, _, hkd, hs⟩
      · have := t.isLt
        omega
      · let j : Fin m := ⟨m - 1 - d, by have := k.isLt; omega⟩
        have hj := reverseZ_isSuffix p j
        dsimp only at hj
        have hu : m - 1 - t.val < (computeZ p.reverse).ret.reverse[j.val] := by
          dsimp only [j]
          rw [hs]
          have := t.isLt
          omega
        have hh := hj.2.1 (m - 1 - t.val) hu
        have ha : j.val - (m - 1 - t.val) = t.val - d := by
          dsimp only [j]
          have := t.isLt
          omega
        have hb : m - 1 - (m - 1 - t.val) = t.val := by have := t.isLt; omega
        simpa only [ha, hb] using hh
    · have hs' := reverseZ_isSuffix p ⟨j, by omega⟩
      dsimp only at hs'
      have hu : m - 1 - t.val < (computeZ p.reverse).ret.reverse[j] := by
        rw [hs]
        have := t.isLt
        omega
      have hh := hs'.2.1 (m - 1 - t.val) hu
      have ha : j - (m - 1 - t.val) = t.val - d := by have := t.isLt; omega
      have hb : m - 1 - (m - 1 - t.val) = t.val := by have := t.isLt; omega
      simpa only [ha, hb] using hh
  · intro hdk
    rcases hd with hf | ⟨j, hj, _, hs, he⟩
    · rcases hf with he | ⟨_, _, hkd, _⟩
      · have := k.isLt
        omega
      · omega
    · have hs' := reverseZ_isSuffix p ⟨j, by omega⟩
      dsimp only at hs'
      rcases hs'.2.2 with hend | hne
      · rw [hs] at hend
        have := k.isLt
        omega
      · have ha : j - (computeZ p.reverse).ret.reverse[j] = k.val - d := by
          rw [hs]
          have := k.isLt
          omega
        have hb : m - 1 - (computeZ p.reverse).ret.reverse[j] = k.val := by
          rw [hs]
          have := k.isLt
          omega
        simpa only [ha, hb] using hne

private lemma strong_shiftCandidate {σ m : Nat} (p : Vector (Fin σ) m) (k : Fin m)
    (d : Nat) (hdm : d ≤ m) (hd : Strong p k d) :
    ShiftCandidate (computeZ p.reverse).ret.reverse (m - 1) k d := by
  have hk := k.isLt
  by_cases hlast : d = m
  · exact Or.inl (Or.inl hlast)
  have hdlt : d < m := by omega
  let j : Fin m := ⟨m - 1 - d, by omega⟩
  have hprefix (ell : Nat) (hell : ell ≤ m - d) (hlo : k.val < m - ell) :
      ell ≤ (computeZ p.reverse).ret.reverse[j.val] := by
    apply (reverseZ_prefix p j ell).mpr
    refine ⟨by dsimp only [j]; omega, ?_⟩
    intro u hu
    let t : Fin m := ⟨m - 1 - u, by omega⟩
    have hkt : k.val < t.val := by dsimp only [t]; omega
    have hdt : d ≤ t.val := by dsimp only [t]; omega
    have hh := hd.2.1 t hkt hdt
    have ha : j.val - u = t.val - d := by dsimp only [j, t]; omega
    have hb : m - 1 - u = t.val := rfl
    simpa only [ha, hb] using hh
  by_cases hkd : k.val < d
  · have hp := hprefix (m - d) (Nat.le_refl _) (by omega)
    have hb := (reverseZ_isSuffix p j).1
    have he : (computeZ p.reverse).ret.reverse[j.val] = m - d := by
      dsimp only [j] at hp hb ⊢
      omega
    exact Or.inl (Or.inr ⟨hdlt, Nat.zero_le _, hkd, he⟩)
  · have hdk : d ≤ k.val := by omega
    have hp := hprefix (m - 1 - k.val) (by omega) (by omega)
    have he : (computeZ p.reverse).ret.reverse[j.val] = m - 1 - k.val := by
      by_contra hne
      have hu : m - 1 - k.val < (computeZ p.reverse).ret.reverse[j.val] := by omega
      have hh := (reverseZ_isSuffix p j).2.1 (m - 1 - k.val) hu
      have ha : j.val - (m - 1 - k.val) = k.val - d := by dsimp only [j]; omega
      have hb : m - 1 - (m - 1 - k.val) = k.val := by omega
      apply hd.2.2 hdk
      simpa only [ha, hb] using hh
    right
    refine ⟨j.val, ?_, ?_, he, ?_⟩
    · dsimp only [j]
      have hp := hd.1
      omega
    · dsimp only [j]
      have hp := hd.1
      omega
    · dsimp only [j]
      omega

/-- A good-suffix slot is the least positive shift preserving the matched suffix
and, when its predecessor overlaps, a different predecessor symbol. -/
public theorem preprocess_goodSuffix {σ m : Nat} (p : Vector (Fin σ) m) (i : Fin m) :
    let d := (preprocess p).ret.2[i.val]
    0 < d ∧ d ≤ m ∧
      (∀ t : Fin m, i.val < t.val → d ≤ t.val → p[t.val - d] = p[t.val]) ∧
      (d ≤ i.val → p[i.val - d] ≠ p[i.val]) ∧
      ∀ e, 0 < e →
        (∀ t : Fin m, i.val < t.val → e ≤ t.val → p[t.val - e] = p[t.val]) →
        (e ≤ i.val → p[i.val - e] ≠ p[i.val]) → d ≤ e := by
  dsimp only
  have hl := preprocess_leastShift p i
  have hb := shiftCandidate_bounds _ (m - 1) i _ hl.1
  have hs := shiftCandidate_strong p i _ hl.1
  refine ⟨hb.1, hb.2, hs.2.1, hs.2.2, ?_⟩
  intro e he hmatch hpred
  by_cases hem : e ≤ m
  · exact hl.2 e (strong_shiftCandidate p i e hem ⟨he, hmatch, hpred⟩)
  · omega

/-- The full-match shift is the least positive period of the pattern, so later
matcher stages may continue without discarding overlapping occurrences. -/
public theorem preprocess_fullMatch {σ m : Nat} (p : Vector (Fin σ) m) (hm : 0 < m) :
    let d := (preprocess p).ret.2[0]
    0 < d ∧ d ≤ m ∧
      (∀ t : Fin m, d ≤ t.val → p[t.val - d] = p[t.val]) ∧
      ∀ e, 0 < e → (∀ t : Fin m, e ≤ t.val → p[t.val - e] = p[t.val]) → d ≤ e := by
  have hg := preprocess_goodSuffix p ⟨0, hm⟩
  dsimp only at hg ⊢
  refine ⟨hg.1, hg.2.1, ?_, ?_⟩
  · intro t hdt
    exact hg.2.2.1 t (by omega) hdt
  · intro e he hperiod
    apply hg.2.2.2.2 e he
    · intro t _ ht
      exact hperiod t ht
    · intro hzero
      omega

end Cslib.Algorithms.Lean.StringMatching.BoyerMoore
