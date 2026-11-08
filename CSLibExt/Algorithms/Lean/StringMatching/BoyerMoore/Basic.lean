/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Preprocessing
public import CSLibExt.Algorithms.Lean.StringMatching.Naive

import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

/-!
# All-overlapping Boyer-Moore matching

The matcher compares from right to left and advances by the maximum of the signed
bad-character proposal and the strong good-suffix shift. Full matches continue with
the least positive period. Preprocessing reuses the canonical reverse Z computation.

The selected-event model charges conversions, inherited preprocessing events,
alignment visits, character tests, shifts, output conses and the final reverse.
Length queries, guards, scalar arithmetic, vector accesses, allocation and private
counter bookkeeping are not charged. These counts are not RAM or bit complexity.

Retained Lean is authored by Codex at Adam Kiezun's explicit selection.

## References

Robert S. Boyer and J Strother Moore, *A Fast String Searching Algorithm*, CACM20(10),
1977, pages762-772. The all-occurrences algorithm follows Charras and Lecroq:
<http://www-igm.univ-mlv.fr/~lecroq/string/node14.html>.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open StringMatching.BoyerMoore

private structure Comparison (m : Nat) where
  mismatch : Option (Fin m)
  comparisons : Nat

@[no_expose] private def compareRight {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s : Nat) (hs : s + m ≤ n) :
    (r : Nat) → r ≤ m → TimeM Nat (Comparison m)
  | 0, _ => pure ⟨none, 0⟩
  | r + 1, hr => do
    tick 1
    if p[r] = t[s + r] then
      let rest ← compareRight p t s hs r (by omega)
      pure ⟨rest.mismatch, rest.comparisons + 1⟩
    else
      pure ⟨some ⟨r, by omega⟩, 1⟩

@[no_expose] private def mismatchShift {σ m : Nat} (bc : Vector Nat σ)
    (gs : Vector Nat m) (i : Fin m) (c : Fin σ) : Nat :=
  (max (gs[i.val] : Int) ((bc[c.val] : Int) - (m : Int) + 1 + (i.val : Int))).toNat

private theorem mismatchShift_pos {σ m : Nat} (bc : Vector Nat σ)
    (gs : Vector Nat m) (i : Fin m) (c : Fin σ) (h : 0 < gs[i.val]) :
    0 < mismatchShift bc gs i c := by
  unfold mismatchShift
  have hmax := le_max_left (gs[i.val] : Int)
    ((bc[c.val] : Int) - (m : Int) + 1 + (i.val : Int))
  omega

private structure SearchResult where
  reverseMatches : List Nat
  attempts : Nat
  comparisons : Nat
  outputs : Nat

@[no_expose] private def search {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (hm : 0 < m) (bc : Vector Nat σ) (gs : Vector Nat m)
    (hgs : ∀ i : Fin m, 0 < gs[i.val]) (s : Nat) (acc : List Nat) :
    TimeM Nat SearchResult :=
  if hs : s + m ≤ n then do
    tick 1
    let compared ← compareRight p t s hs m (by omega)
    match compared.mismatch with
    | none =>
      tick 1
      tick 1
      let rest ← search p t hm bc gs hgs (s + gs[0]) (s :: acc)
      pure ⟨rest.reverseMatches, rest.attempts + 1,
        rest.comparisons + compared.comparisons, rest.outputs + 1⟩
    | some i =>
      let d := mismatchShift bc gs i t[s + i.val]
      tick 1
      let rest ← search p t hm bc gs hgs (s + d) acc
      pure ⟨rest.reverseMatches, rest.attempts + 1,
        rest.comparisons + compared.comparisons, rest.outputs⟩
  else
    pure ⟨acc, 0, 0, 0⟩
termination_by n + 1 - (s + m)
decreasing_by
  · have hpos : 0 < gs[0] := hgs ⟨0, hm⟩
    simp_wf
    omega
  · have := mismatchShift_pos bc gs i t[s + i.val] (hgs i)
    simp_wf
    omega

@[no_expose] private def matchWithCounts {σ : Nat} (pattern text : List (Fin σ)) :
    TimeM Nat (List Nat × Nat × Nat × Nat) :=
  let m := pattern.length
  let n := text.length
  if hm : m = 0 then
    ⟨(List.range (n + 1), 0, 0, n + 1), n + 1⟩
  else if hn : n < m then
    pure ([], 0, 0, 0)
  else do
    tick (m + n)
    let p : Vector (Fin σ) m := pattern.toArray.toVector.cast (by simp [m])
    let t : Vector (Fin σ) n := text.toArray.toVector.cast (by simp [n])
    let prepared := preprocess p
    tick prepared.time
    have hgs : ∀ i : Fin m, 0 < prepared.ret.2[i.val] := fun i =>
      (preprocess_goodSuffix p i).1
    let scanned ← search p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []
    tick scanned.outputs
    pure (scanned.reverseMatches.reverse, scanned.attempts,
      scanned.comparisons, scanned.outputs)

/-- Return every occurrence in increasing order, including overlaps.
The cost counts the documented selected events, not machine instructions. -/
public def boyerMooreMatches {σ : Nat} (pattern text : List (Fin σ)) :
    TimeM Nat (List Nat) :=
  Prod.fst <$> matchWithCounts pattern text

private def vectorMatch {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s : Nat) : Prop :=
  ∃ hs : s + m ≤ n, ∀ i : Fin m, p[i.val] = t[s + i.val]

private theorem vectorMatch_iff {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s : Nat) :
    vectorMatch p t s ↔ StringMatching.MatchAt p.toList t.toList s := by
  constructor
  · rintro ⟨hs, hmatch⟩
    refine ⟨by simpa using (show s ≤ n by omega), ?_⟩
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · simp
      omega
    · intro i hi hj
      have hmi : i < m := by simpa using hi
      simpa only [Vector.length_toList, List.getElem_take, List.getElem_drop,
        Vector.getElem_toList] using hmatch ⟨i, hmi⟩
  · rintro ⟨hs, hpref⟩
    have hlength := hpref.length_le
    simp only [Vector.length_toList, List.length_drop] at hs hlength
    have hbound : s + m ≤ n := by omega
    refine ⟨hbound, ?_⟩
    intro i
    have h := hpref.getElem (i := i.val) (by simpa only [Vector.length_toList] using i.isLt)
    simpa only [List.getElem_drop, Vector.getElem_toList] using h

private theorem badCharacter_le {σ m : Nat} (p : Vector (Fin σ) m) (c : Fin σ) :
    (preprocess p).ret.1[c.val] ≤ m := by
  rcases preprocess_badCharacter p c with ⟨h, _⟩ | ⟨j, hj, _, h, _⟩ <;>
    omega

private theorem bad_proposal_le {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s e : Nat) (hs : s + m ≤ n) (he : 0 < e)
    (i : Fin m) (hfuture : vectorMatch p t (s + e)) :
    ((preprocess p).ret.1[t[s + i.val].val] : Int) - (m : Int) + 1 + i.val ≤ e := by
  by_cases hei : e ≤ i.val
  · rcases hfuture with ⟨hfutureBound, hfutureMatch⟩
    have hindex : s + e + (i.val - e) = s + i.val := by omega
    have hchar : p[i.val - e] = t[s + i.val] := by
      simpa only [hindex] using hfutureMatch ⟨i.val - e, by omega⟩
    rcases preprocess_badCharacter p t[s + i.val] with
      ⟨_, habsent⟩ | ⟨j, hj, _, hvalue, hrightmost⟩
    · exact False.elim ((habsent (i.val - e) (by omega)) hchar)
    · have hjk := hrightmost (i.val - e) (by omega) hchar
      rw [hvalue]
      omega
  · have hbound := badCharacter_le p t[s + i.val]
    omega

private theorem good_shift_le {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s e : Nat) (hs : s + m ≤ n) (he : 0 < e)
    (i : Fin m) (hmismatch : p[i.val] ≠ t[s + i.val])
    (hsuffix : ∀ j : Fin m, i.val < j.val → p[j.val] = t[s + j.val])
    (hfuture : vectorMatch p t (s + e)) : (preprocess p).ret.2[i.val] ≤ e := by
  rcases hfuture with ⟨hfutureBound, hfutureMatch⟩
  apply (preprocess_goodSuffix p i).2.2.2.2 e he
  · intro j hij hej
    have hindex : s + e + (j.val - e) = s + j.val := by omega
    have h : p[j.val - e] = t[s + j.val] := by
      simpa only [hindex] using hfutureMatch ⟨j.val - e, by omega⟩
    exact h.trans (hsuffix j hij).symm
  · intro hei
    have hindex : s + e + (i.val - e) = s + i.val := by omega
    have h : p[i.val - e] = t[s + i.val] := by
      simpa only [hindex] using hfutureMatch ⟨i.val - e, by omega⟩
    intro heq
    exact hmismatch (heq.symm.trans h)

private theorem full_shift_le {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s e : Nat) (hm : 0 < m) (he : 0 < e)
    (hcurrent : vectorMatch p t s) (hfuture : vectorMatch p t (s + e)) :
    (preprocess p).ret.2[0] ≤ e := by
  rcases hcurrent with ⟨hs, hcurrentMatch⟩
  rcases hfuture with ⟨hfutureBound, hfutureMatch⟩
  apply (preprocess_fullMatch p hm).2.2.2 e he
  intro j hej
  have hindex : s + e + (j.val - e) = s + j.val := by omega
  have h : p[j.val - e] = t[s + j.val] := by
    simpa only [hindex] using hfutureMatch ⟨j.val - e, by omega⟩
  exact h.trans (hcurrentMatch j).symm

private theorem mismatch_shift_le {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s e : Nat) (hs : s + m ≤ n) (he : 0 < e)
    (i : Fin m) (hmismatch : p[i.val] ≠ t[s + i.val])
    (hsuffix : ∀ j : Fin m, i.val < j.val → p[j.val] = t[s + j.val])
    (hfuture : vectorMatch p t (s + e)) :
    mismatchShift (preprocess p).ret.1 (preprocess p).ret.2 i t[s + i.val] ≤ e := by
  have hgood := good_shift_le p t s e hs he i hmismatch hsuffix hfuture
  have hbad := bad_proposal_le p t s e hs he i hfuture
  unfold mismatchShift
  rw [max_def]
  split <;> omega

private theorem mismatch_shift_le_length {σ m : Nat} (p : Vector (Fin σ) m)
    (i : Fin m) (c : Fin σ) :
    mismatchShift (preprocess p).ret.1 (preprocess p).ret.2 i c ≤ m := by
  have hgood := (preprocess_goodSuffix p i).2.1
  have hbad := badCharacter_le p c
  unfold mismatchShift
  rw [max_def]
  split <;> omega

private theorem compareRight_spec {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s : Nat) (hs : s + m ≤ n) (r : Nat) (hr : r ≤ m) :
    let q := (compareRight p t s hs r hr).ret
    (q.mismatch = none → ∀ i : Fin m, i.val < r → p[i.val] = t[s + i.val]) ∧
      ∀ i, q.mismatch = some i → i.val < r ∧ p[i.val] ≠ t[s + i.val] ∧
        ∀ j : Fin m, i.val < j.val → j.val < r → p[j.val] = t[s + j.val] := by
  induction r with
  | zero => simp [compareRight]
  | succ r ih =>
    have ih := ih (by omega)
    by_cases heq : p[r] = t[s + r]
    · simp only [compareRight, heq, ↓reduceIte, ret_bind, ret_pure]
      constructor
      · intro hnone i hi
        by_cases hir : i.val < r
        · exact ih.1 hnone i hir
        · have hieq : i.val = r := by omega
          simpa only [hieq] using heq
      · intro i hsome
        rcases ih.2 i hsome with ⟨hir, hneq, hafter⟩
        refine ⟨by omega, hneq, ?_⟩
        intro j hij hjr
        by_cases hj : j.val < r
        · exact hafter j hij hj
        · have hjeq : j.val = r := by omega
          simpa only [hjeq] using heq
    · simp only [compareRight, heq, ↓reduceIte, ret_bind, ret_pure]
      constructor
      · intro hnone
        contradiction
      · intro i hsome
        have hi : i = ⟨r, by omega⟩ := Option.some.inj hsome.symm
        subst i
        refine ⟨by simp, heq, ?_⟩
        intro j hij hjr
        change r < j.val at hij
        omega

private theorem compareRight_cost {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (s : Nat) (hs : s + m ≤ n) (r : Nat) (hr : r ≤ m) :
    let q := compareRight p t s hs r hr
    q.time = q.ret.comparisons ∧ q.ret.comparisons ≤ r ∧
      (q.ret.mismatch = none → q.ret.comparisons = r) ∧
      ∀ i, q.ret.mismatch = some i → q.ret.comparisons = r - i.val := by
  induction r with
  | zero => simp [compareRight]
  | succ r ih =>
    have ih := ih (by omega)
    by_cases heq : p[r] = t[s + r]
    · simp only [compareRight, heq, ↓reduceIte, ret_bind, ret_pure,
        time_bind, time_tick, time_pure]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro hnone
        have := ih.2.2.1 hnone
        omega
      · intro i hsome
        have := ih.2.2.2 i hsome
        have := (compareRight_spec p t s hs r (by omega)).2 i hsome
        omega
    · simp only [compareRight, heq, ↓reduceIte, ret_bind, ret_pure,
        time_bind, time_tick, time_pure]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro hnone
        contradiction
      · intro i hsome
        have hi : i = ⟨r, by omega⟩ := Option.some.inj hsome.symm
        subst i
        simp

private theorem search_mem {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (hm : 0 < m) (s : Nat) (acc : List Nat) (k : Nat) :
    let prepared := preprocess p
    let hgs : ∀ i : Fin m, 0 < prepared.ret.2[i.val] := fun i =>
      (preprocess_goodSuffix p i).1
    k ∈ (search p t hm prepared.ret.1 prepared.ret.2 hgs s acc).ret.reverseMatches ↔
      k ∈ acc ∨ s ≤ k ∧ vectorMatch p t k := by
  by_cases hs : s + m ≤ n
  · have hcompare := compareRight_spec p t s hs m (by omega)
    cases hcmp : (compareRight p t s hs m (by omega)).ret.mismatch with
    | none =>
      have hcurrent : vectorMatch p t s := ⟨hs, fun i => hcompare.1 hcmp i i.isLt⟩
      have ih := search_mem p t hm (s + (preprocess p).ret.2[0]) (s :: acc) k
      dsimp only at ih
      dsimp only
      rw [search]
      simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp]
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | hmem) | ⟨hnext, hmatch⟩)
        · exact Or.inr ⟨by omega, hcurrent⟩
        · exact Or.inl hmem
        · exact Or.inr ⟨by omega, hmatch⟩
      · rintro (hmem | ⟨hk, hmatch⟩)
        · exact Or.inl (Or.inr hmem)
        · by_cases hks : k = s
          · exact Or.inl (Or.inl hks)
          · have he : 0 < k - s := by omega
            have hindex : s + (k - s) = k := by omega
            have hfuture : vectorMatch p t (s + (k - s)) := by
              simpa only [hindex] using hmatch
            have hd := full_shift_le p t s (k - s) hm he hcurrent hfuture
            exact Or.inr ⟨by omega, hmatch⟩
    | some i =>
      rcases hcompare.2 i hcmp with ⟨_, hneq, hsuffix⟩
      have hsuffix' : ∀ j : Fin m, i.val < j.val → p[j.val] = t[s + j.val] :=
        fun j hij => hsuffix j hij j.isLt
      let d := mismatchShift (preprocess p).ret.1 (preprocess p).ret.2 i t[s + i.val]
      have ih := search_mem p t hm (s + d) acc k
      dsimp only at ih
      dsimp only
      rw [search]
      simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp]
      rw [ih]
      constructor
      · rintro (hmem | ⟨hnext, hmatch⟩)
        · exact Or.inl hmem
        · exact Or.inr ⟨by omega, hmatch⟩
      · rintro (hmem | ⟨hk, hmatch⟩)
        · exact Or.inl hmem
        · have hks : k ≠ s := by
            intro hks
            subst k
            exact hneq (hmatch.choose_spec i)
          have he : 0 < k - s := by omega
          have hindex : s + (k - s) = k := by omega
          have hfuture : vectorMatch p t (s + (k - s)) := by
            simpa only [hindex] using hmatch
          have hd := mismatch_shift_le p t s (k - s) hs he i hneq hsuffix' hfuture
          exact Or.inr ⟨by omega, hmatch⟩
  · dsimp only
    rw [search]
    simp only [hs, ↓reduceDIte, ret_pure]
    constructor
    · exact fun h => Or.inl h
    · rintro (hmem | ⟨hk, hmatch⟩)
      · exact hmem
      · have := hmatch.choose
        omega
termination_by n + 1 - (s + m)
decreasing_by
  · have hpos : 0 < (preprocess p).ret.2[0] :=
      (preprocess_fullMatch p hm).1
    omega
  · have hpos := mismatchShift_pos (preprocess p).ret.1 (preprocess p).ret.2 i
      t[s + i.val] (preprocess_goodSuffix p i).1
    omega

private theorem search_cost {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (hm : 0 < m) (bc : Vector Nat σ) (gs : Vector Nat m)
    (hgs : ∀ i : Fin m, 0 < gs[i.val]) (s : Nat) (acc : List Nat) :
    let q := search p t hm bc gs hgs s acc
    q.time = 2 * q.ret.attempts + q.ret.comparisons + q.ret.outputs ∧
      q.ret.attempts ≤ n + 1 - (s + m) ∧ q.ret.comparisons ≤ m * q.ret.attempts ∧
      q.ret.outputs ≤ q.ret.attempts ∧
      q.ret.reverseMatches.length = acc.length + q.ret.outputs := by
  dsimp only
  by_cases hs : s + m ≤ n
  · have hcompare := compareRight_cost p t s hs m (by omega)
    cases hcmp : (compareRight p t s hs m (by omega)).ret.mismatch with
    | none =>
      have ih := search_cost p t hm bc gs hgs (s + gs[0]) (s :: acc)
      dsimp only at ih
      unfold search
      simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp,
        time_bind, time_tick, time_pure]
      have hpos : 0 < gs[0] := hgs ⟨0, hm⟩
      refine ⟨by omega, by omega, ?_, by omega, ?_⟩
      · nlinarith [hcompare.2.1, ih.2.2.1]
      · have hlength := ih.2.2.2.2
        simp only [List.length_cons] at hlength
        omega
    | some i =>
      let d := mismatchShift bc gs i t[s + i.val]
      have ih := search_cost p t hm bc gs hgs (s + d) acc
      dsimp only [d] at ih
      unfold search
      simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp,
        time_bind, time_tick, time_pure]
      have hpos := mismatchShift_pos bc gs i t[s + i.val] (hgs i)
      refine ⟨by omega, by omega, ?_, by omega, ih.2.2.2.2⟩
      nlinarith [hcompare.2.1, ih.2.2.1]
  · unfold search
    simp only [hs, ↓reduceDIte, ret_pure, time_pure]
    simp
termination_by n + 1 - (s + m)
decreasing_by
  · have hpos : 0 < gs[0] := hgs ⟨0, hm⟩
    omega
  · have hpos := mismatchShift_pos bc gs i t[s + i.val] (hgs i)
    omega

private theorem search_pairwise {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (hm : 0 < m) (bc : Vector Nat σ) (gs : Vector Nat m)
    (hgs : ∀ i : Fin m, 0 < gs[i.val]) (s : Nat) (acc : List Nat)
    (hacc : acc.Pairwise (fun x y => y < x)) (hbound : ∀ k ∈ acc, k < s) :
    (search p t hm bc gs hgs s acc).ret.reverseMatches.Pairwise (fun x y => y < x) := by
  by_cases hs : s + m ≤ n
  · cases hcmp : (compareRight p t s hs m (by omega)).ret.mismatch with
    | none =>
      have hpos : 0 < gs[0] := hgs ⟨0, hm⟩
      have hcons : (s :: acc).Pairwise (fun x y => y < x) :=
        List.pairwise_cons.mpr ⟨hbound, hacc⟩
      have hnext : ∀ k ∈ s :: acc, k < s + gs[0] := by
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · have := hbound k hk
          omega
      have ih := search_pairwise p t hm bc gs hgs (s + gs[0]) (s :: acc) hcons hnext
      rw [search]
      simpa only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp] using ih
    | some i =>
      let d := mismatchShift bc gs i t[s + i.val]
      have hpos : 0 < d := mismatchShift_pos bc gs i t[s + i.val] (hgs i)
      have hnext : ∀ k ∈ acc, k < s + d := by
        intro k hk
        have := hbound k hk
        omega
      have ih := search_pairwise p t hm bc gs hgs (s + d) acc hacc hnext
      rw [search]
      simpa only [hs, ↓reduceDIte, ret_bind, ret_pure, hcmp] using ih
  · rw [search]
    simpa only [hs, ↓reduceDIte, ret_pure] using hacc
termination_by n + 1 - (s + m)
decreasing_by
  all_goals omega

/-- An empty pattern occurs at every bounded text boundary. -/
@[simp] public theorem boyerMooreMatches_nil_pattern {σ : Nat} (text : List (Fin σ)) :
    boyerMooreMatches [] text = ⟨List.range (text.length + 1), text.length + 1⟩ := by
  rfl

/-- Overlength patterns return immediately, without preprocessing or search events. -/
@[simp] public theorem boyerMooreMatches_of_length_lt {σ : Nat}
    (pattern text : List (Fin σ)) (h : text.length < pattern.length) :
    boyerMooreMatches pattern text = pure [] := by
  have hm : pattern.length ≠ 0 := by omega
  apply TimeM.ext <;> simp [boyerMooreMatches, matchWithCounts, hm, h]

/-- The matcher returns exactly the canonical occurrences, including overlaps. -/
public theorem mem_boyerMooreMatches_iff {σ : Nat} (pattern text : List (Fin σ))
    (offset : Nat) : offset ∈ (boyerMooreMatches pattern text).ret ↔
    StringMatching.MatchAt pattern text offset := by
  by_cases hm : pattern.length = 0
  · have hp : pattern = [] := by simpa using hm
    subst pattern
    simp only [boyerMooreMatches_nil_pattern, List.mem_range,
      StringMatching.MatchAt, List.nil_prefix, and_true]
    omega
  · by_cases hn : text.length < pattern.length
    · rw [boyerMooreMatches_of_length_lt pattern text hn]
      simp only [ret_pure, List.not_mem_nil, false_iff]
      rintro ⟨hbound, hprefix⟩
      have hlength := hprefix.length_le
      simp only [List.length_drop] at hlength
      omega
    · let p : Vector (Fin σ) pattern.length :=
        pattern.toArray.toVector.cast (by simp)
      let t : Vector (Fin σ) text.length := text.toArray.toVector.cast (by simp)
      have hmem := search_mem p t (by omega) 0 [] offset
      dsimp only at hmem
      simp only [boyerMooreMatches, matchWithCounts, hm, hn, ↓reduceDIte,
        ret_map, ret_bind, ret_pure]
      rw [List.mem_reverse]
      have hcanonical : vectorMatch p t offset ↔ StringMatching.MatchAt pattern text offset := by
        simpa [p, t] using vectorMatch_iff p t offset
      simp only [List.not_mem_nil, Nat.zero_le, true_and, false_or] at hmem
      exact hmem.trans hcanonical

/-- All returned offsets are strictly increasing. -/
public theorem boyerMooreMatches_pairwise {σ : Nat} (pattern text : List (Fin σ)) :
    (boyerMooreMatches pattern text).ret.Pairwise (· < ·) := by
  by_cases hm : pattern.length = 0
  · have hp : pattern = [] := by simpa using hm
    subst pattern
    simpa only [boyerMooreMatches_nil_pattern] using List.pairwise_lt_range
  · by_cases hn : text.length < pattern.length
    · simp [boyerMooreMatches_of_length_lt pattern text hn]
    · let p : Vector (Fin σ) pattern.length :=
        pattern.toArray.toVector.cast (by simp)
      let t : Vector (Fin σ) text.length := text.toArray.toVector.cast (by simp)
      let prepared := preprocess p
      have hgs : ∀ i : Fin pattern.length, 0 < prepared.ret.2[i.val] :=
        fun i => (preprocess_goodSuffix p i).1
      have horder := search_pairwise p t (by omega) prepared.ret.1 prepared.ret.2
        hgs 0 [] (by simp) (by simp)
      simp only [boyerMooreMatches, matchWithCounts, hm, hn, ↓reduceDIte,
        ret_map, ret_bind, ret_pure]
      exact List.Pairwise.reverse horder

/-- Boyer-Moore and the canonical naive matcher return the same ordered list.
This is a result specification bridge, not a naive execution path. -/
public theorem boyerMooreMatches_eq_naiveMatches {σ : Nat} (pattern text : List (Fin σ)) :
    (boyerMooreMatches pattern text).ret = (naiveMatches pattern text).ret := by
  apply List.Pairwise.eq_of_mem_iff (boyerMooreMatches_pairwise pattern text)
    (naiveMatches_pairwise pattern text)
  intro offset
  exact (mem_boyerMooreMatches_iff pattern text offset).trans
    (mem_naiveMatches_iff pattern text offset).symm

/-- Quadratic worst-case selected-event bound for all-occurrences matching.
This does not assert linear all-match comparison complexity or machine runtime. -/
public theorem boyerMooreMatches_time_le {σ : Nat} (pattern text : List (Fin σ)) :
    (boyerMooreMatches pattern text).time ≤
      if pattern.length = 0 then text.length + 1
      else if text.length < pattern.length then 0
      else σ + text.length + 11 * pattern.length - 6 +
        (pattern.length + 4) * (text.length - pattern.length + 1) := by
  by_cases hm : pattern.length = 0
  · have hp : pattern = [] := by simpa using hm
    subst pattern
    simp
  · by_cases hn : text.length < pattern.length
    · simp [hm, hn]
    · let p : Vector (Fin σ) pattern.length :=
        pattern.toArray.toVector.cast (by simp)
      let t : Vector (Fin σ) text.length := text.toArray.toVector.cast (by simp)
      let prepared := preprocess p
      have hgs : ∀ i : Fin pattern.length, 0 < prepared.ret.2[i.val] :=
        fun i => (preprocess_goodSuffix p i).1
      let scanned := search p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []
      have hcost := search_cost p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []
      dsimp only at hcost
      have hprep := preprocess_time_le p
      simp only [hm, ↓reduceIte] at hprep
      have hproduct : pattern.length * scanned.ret.attempts ≤
          pattern.length * (text.length - pattern.length + 1) := by
        dsimp only [scanned]
        apply Nat.mul_le_mul_left
        have := hcost.2.1
        omega
      simp only [boyerMooreMatches, matchWithCounts, hm, hn, ↓reduceDIte, ↓reduceIte,
        time_map, time_bind, time_tick, time_pure]
      change pattern.length + text.length + (prepared.time + (scanned.time +
        (scanned.ret.outputs + 0))) ≤ σ + text.length + 11 * pattern.length - 6 +
          (pattern.length + 4) * (text.length - pattern.length + 1)
      dsimp only [scanned, prepared] at hproduct hcost ⊢
      have hremaining : text.length + 1 - (0 + pattern.length) =
          text.length - pattern.length + 1 := by omega
      rw [hremaining] at hcost
      have hprepSub : σ + 10 * pattern.length - 6 + 6 = σ + 10 * pattern.length := by
        omega
      have hboundSub : σ + text.length + 11 * pattern.length - 6 + 6 =
          σ + text.length + 11 * pattern.length := by omega
      nlinarith [hcost.1, hcost.2.1, hcost.2.2.1, hcost.2.2.2.1]

end Cslib.Algorithms.Lean.TimeM
