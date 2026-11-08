/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Basic
import all CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Basic

import Mathlib.Tactic.Linarith

/-!
# Boyer-Moore comparison and selected-event witness families

Repeated-symbol matches use every alignment and compare every pattern character.
A distinct repeated prefix against the last symbol makes two tests per attempt
and advances by the pattern length. The private counts refer to the executed scanner.
Public formulas include the documented other events, not RAM or bit operations.

Retained Lean is authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open StringMatching.BoyerMoore

private theorem compareRight_constant {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (x : Fin σ) (hp : ∀ i : Fin m, p[i.val] = x)
    (ht : ∀ j : Fin n, t[j.val] = x) (s : Nat) (hs : s + m ≤ n) :
    (compareRight p t s hs m (by omega)).ret.mismatch = none ∧
      (compareRight p t s hs m (by omega)).ret.comparisons = m := by
  have hspec := compareRight_spec p t s hs m (by omega)
  have hnone : (compareRight p t s hs m (by omega)).ret.mismatch = none := by
    cases hcmp : (compareRight p t s hs m (by omega)).ret.mismatch with
    | none => rfl
    | some i =>
      have hneq := (hspec.2 i hcmp).2.1
      exact False.elim (hneq ((hp i).trans (ht ⟨s + i.val, by omega⟩).symm))
  exact ⟨hnone, (compareRight_cost p t s hs m (by omega)).2.2.1 hnone⟩

private theorem full_shift_constant {σ m : Nat} (p : Vector (Fin σ) m)
    (x : Fin σ) (hp : ∀ i : Fin m, p[i.val] = x) (hm : 0 < m) :
    (preprocess p).ret.2[0] = 1 := by
  have hfull := preprocess_fullMatch p hm
  have hle := hfull.2.2.2 1 (by omega) (fun i hi =>
    (hp ⟨i.val - 1, by omega⟩).trans (hp i).symm)
  omega

private theorem search_constant_counts {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (x : Fin σ) (hp : ∀ i : Fin m, p[i.val] = x)
    (ht : ∀ j : Fin n, t[j.val] = x) (hm : 0 < m) (s : Nat) (acc : List Nat) :
    let prepared := preprocess p
    let hgs : ∀ i : Fin m, 0 < prepared.ret.2[i.val] := fun i =>
      (preprocess_goodSuffix p i).1
    let q := search p t hm prepared.ret.1 prepared.ret.2 hgs s acc
    q.ret.attempts = n + 1 - (s + m) ∧
      q.ret.comparisons = m * (n + 1 - (s + m)) ∧
      q.ret.outputs = n + 1 - (s + m) := by
  dsimp only
  by_cases hs : s + m ≤ n
  · have hcompare := compareRight_constant p t x hp ht s hs
    have hshift := full_shift_constant p x hp hm
    have ih := search_constant_counts p t x hp ht hm (s + 1) (s :: acc)
    dsimp only at ih
    unfold search
    simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcompare.1, hshift]
    refine ⟨by omega, ?_, by omega⟩
    have hremaining : n + 1 - (s + m) = (n + 1 - (s + 1 + m)) + 1 := by omega
    nlinarith [hcompare.2, ih.2.1, hremaining]
  · unfold search
    simp only [hs, ↓reduceDIte, ret_pure]
    have hremaining : n + 1 - (s + m) = 0 := by omega
    simp [hremaining]
termination_by n + 1 - (s + m)
decreasing_by omega

private theorem best_badCharacter {σ m : Nat} (p : Vector (Fin σ) m)
    (a b : Fin σ) (hab : a ≠ b)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) :
    (preprocess p).ret.1[b.val] = m := by
  rcases preprocess_badCharacter p b with ⟨hvalue, _⟩ | ⟨j, hj, hchar, _, _⟩
  · exact hvalue
  · exact False.elim (hab ((hp ⟨j, by omega⟩ hj).symm.trans hchar))

private theorem best_goodSuffix {σ m : Nat} (p : Vector (Fin σ) m)
    (a b : Fin σ) (hab : a ≠ b) (hm : 2 ≤ m)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) (hlast : p[m - 1] = b) :
    (preprocess p).ret.2[m - 2] = m := by
  let i : Fin m := ⟨m - 2, by omega⟩
  have hgood := preprocess_goodSuffix p i
  have hpos := hgood.1
  have hbound := hgood.2.1
  by_contra hne
  have hd : (preprocess p).ret.2[i.val] ≤ m - 1 := by
    dsimp only [i] at hbound ⊢
    omega
  have hcompat := hgood.2.2.1 ⟨m - 1, by omega⟩ (by dsimp [i]; omega) hd
  have hindex : m - 1 - (preprocess p).ret.2[i.val] + 1 < m := by omega
  have hprefix := hp ⟨m - 1 - (preprocess p).ret.2[i.val], by omega⟩ hindex
  exact hab (hprefix.symm.trans (hcompat.trans hlast))

private theorem best_shift {σ m : Nat} (p : Vector (Fin σ) m)
    (a b : Fin σ) (hab : a ≠ b) (hm : 2 ≤ m)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) (hlast : p[m - 1] = b) :
    mismatchShift (preprocess p).ret.1 (preprocess p).ret.2 ⟨m - 2, by omega⟩ b = m := by
  unfold mismatchShift
  have hbad := best_badCharacter p a b hab hp
  have hgood := best_goodSuffix p a b hab hm hp hlast
  simp only [hbad, hgood]
  rw [max_def]
  split <;> omega

private theorem compareRight_best {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (a b : Fin σ) (hab : a ≠ b) (hm : 2 ≤ m)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) (hlast : p[m - 1] = b)
    (ht : ∀ j : Fin n, t[j.val] = b) (s : Nat) (hs : s + m ≤ n) :
    (compareRight p t s hs m (by omega)).ret.mismatch = some ⟨m - 2, by omega⟩ ∧
      (compareRight p t s hs m (by omega)).ret.comparisons = 2 := by
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ r =>
      have hlast' : p[r + 1] = b := by simpa using hlast
      have hprefix : p[r] = a := hp ⟨r, by omega⟩ (by change r + 1 < r + 2; omega)
      have hyes : p[r + 1] = t[s + (r + 1)] :=
        hlast'.trans (ht ⟨s + (r + 1), by omega⟩).symm
      have hno : p[r] ≠ t[s + r] := by
        rw [hprefix, ht ⟨s + r, by omega⟩]
        exact hab
      simp only [compareRight, hyes, hno, ↓reduceIte, ret_bind, ret_pure]
      simp

private theorem search_best_counts {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (a b : Fin σ) (hab : a ≠ b) (hm : 2 ≤ m)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) (hlast : p[m - 1] = b)
    (ht : ∀ j : Fin n, t[j.val] = b) (s : Nat) (acc : List Nat) :
    let prepared := preprocess p
    let hgs : ∀ i : Fin m, 0 < prepared.ret.2[i.val] := fun i =>
      (preprocess_goodSuffix p i).1
    let q := search p t (by omega) prepared.ret.1 prepared.ret.2 hgs s acc
    q.ret.attempts * m ≤ n - s ∧ n - s < (q.ret.attempts + 1) * m ∧
      q.ret.comparisons = 2 * q.ret.attempts ∧ q.ret.outputs = 0 := by
  dsimp only
  by_cases hs : s + m ≤ n
  · have hcompare := compareRight_best p t a b hab hm hp hlast ht s hs
    have hshift := best_shift p a b hab hm hp hlast
    have htchar : t[s + (m - 2)] = b := ht ⟨s + (m - 2), by omega⟩
    have ih := search_best_counts p t a b hab hm hp hlast ht (s + m) acc
    dsimp only at ih
    unfold search
    simp only [hs, ↓reduceDIte, ret_bind, ret_pure, hcompare.1,
      htchar, hshift]
    have hremaining : n - s = n - (s + m) + m := by omega
    refine ⟨?_, ?_, ?_, ih.2.2.2⟩
    · nlinarith [ih.1, hremaining]
    · nlinarith [ih.2.1, hremaining]
    · nlinarith [ih.2.2.1, hcompare.2]
  · unfold search
    simp only [hs, ↓reduceDIte, ret_pure]
    simpa using (show n - s < m by omega)
termination_by n + 1 - (s + m)
decreasing_by omega

private theorem preprocess_cast_time {σ m k : Nat} (p : Vector (Fin σ) m) (h : m = k) :
    (preprocess (p.cast h)).time = (preprocess p).time := by
  cases h
  rfl

/-- Repeated-symbol inputs realize `m * (n - m + 1)` actual character tests.
The formula also includes conversions, preprocessing and the other selected events. -/
public theorem boyerMooreMatches_time_replicate {σ : Nat} (x : Fin σ) (m n : Nat)
    (hm : 0 < m) (hlen : m ≤ n) :
    (boyerMooreMatches (List.replicate m x) (List.replicate n x)).time =
      m + n + (preprocess (List.replicate m x).toArray.toVector).time +
        (m + 4) * (n - m + 1) := by
  let p : Vector (Fin σ) (List.replicate m x).length :=
    (List.replicate m x).toArray.toVector.cast (by simp)
  let t : Vector (Fin σ) (List.replicate n x).length :=
    (List.replicate n x).toArray.toVector.cast (by simp)
  have hp : ∀ i : Fin (List.replicate m x).length, p[i.val] = x := by
    intro i
    change (List.replicate m x).toArray[i.val]'(by simpa using i.isLt) = x
    rw [List.getElem_toArray]
    exact List.getElem_replicate (a := x) (n := m) (i := i.val) i.isLt
  have ht : ∀ j : Fin (List.replicate n x).length, t[j.val] = x := by
    intro j
    change (List.replicate n x).toArray[j.val]'(by simpa using j.isLt) = x
    rw [List.getElem_toArray]
    exact List.getElem_replicate (a := x) (n := n) (i := j.val) j.isLt
  have hm' : 0 < (List.replicate m x).length := by simpa using hm
  let prepared := preprocess p
  have hgs : ∀ i : Fin (List.replicate m x).length, 0 < prepared.ret.2[i.val] :=
    fun i => (preprocess_goodSuffix p i).1
  have hcounts := search_constant_counts p t x hp ht hm' 0 []
  dsimp only at hcounts
  have hcost := search_cost p t hm' prepared.ret.1 prepared.ret.2 hgs 0 []
  dsimp only [prepared] at hcost
  have hprep : (preprocess p).time =
      (preprocess (List.replicate m x).toArray.toVector).time :=
    preprocess_cast_time _ _
  have hmlen : (List.replicate m x).length = m := by simp
  have hnlen : (List.replicate n x).length = n := by simp
  have hm0 : (List.replicate m x).length ≠ 0 := by omega
  have hn0 : ¬(List.replicate n x).length < (List.replicate m x).length := by omega
  simp only [boyerMooreMatches, matchWithCounts, hm0, hn0,
    ↓reduceDIte, time_map, time_bind, time_tick, time_pure]
  change (List.replicate m x).length + (List.replicate n x).length + ((preprocess p).time +
    ((search p t hm' prepared.ret.1 prepared.ret.2 hgs 0 []).time +
      ((search p t hm' prepared.ret.1 prepared.ret.2 hgs 0 []).ret.outputs + 0))) = _
  dsimp only [prepared]
  rw [← hprep]
  have hremaining : (List.replicate n x).length + 1 - (0 + (List.replicate m x).length) =
      n - m + 1 := by omega
  rw [hremaining] at hcounts
  nlinarith [hcost.1, hcounts.1, hcounts.2.1, hcounts.2.2]

private theorem search_best_comparisons {σ m n : Nat} (p : Vector (Fin σ) m)
    (t : Vector (Fin σ) n) (a b : Fin σ) (hab : a ≠ b) (hm : 2 ≤ m)
    (hp : ∀ i : Fin m, i.val + 1 < m → p[i.val] = a) (hlast : p[m - 1] = b)
    (ht : ∀ j : Fin n, t[j.val] = b) :
    let prepared := preprocess p
    let hgs : ∀ i : Fin m, 0 < prepared.ret.2[i.val] := fun i =>
      (preprocess_goodSuffix p i).1
    let q := search p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []
    q.ret.attempts = n / m ∧ q.ret.comparisons = 2 * (n / m) ∧ q.ret.outputs = 0 := by
  have hcounts := search_best_counts p t a b hab hm hp hlast ht 0 []
  dsimp only at hcounts ⊢
  simp only [Nat.sub_zero] at hcounts
  have hdiv := Nat.div_eq_of_lt_le hcounts.1 hcounts.2.1
  exact ⟨hdiv.symm, hcounts.2.2.1.trans (congrArg (2 * ·) hdiv.symm), hcounts.2.2.2⟩

/-- A repeated text symbol and a distinct repeated pattern prefix realize two tests
per attempt and pattern-length shifts. Costs are the documented selected events. -/
public theorem boyerMooreMatches_time_replicate_append {σ : Nat} (a b : Fin σ)
    (m n : Nat) (hab : a ≠ b) (hm : 2 ≤ m) (hlen : m ≤ n) :
    (boyerMooreMatches (List.replicate (m - 1) a ++ [b]) (List.replicate n b)).time =
      m + n + (preprocess (List.replicate (m - 1) a ++ [b]).toArray.toVector).time +
        4 * (n / m) := by
  let p : Vector (Fin σ) (List.replicate (m - 1) a ++ [b]).length :=
    (List.replicate (m - 1) a ++ [b]).toArray.toVector.cast (by simp)
  let t : Vector (Fin σ) (List.replicate n b).length :=
    (List.replicate n b).toArray.toVector.cast (by simp)
  have hlength : (List.replicate (m - 1) a ++ [b]).length = m := by simp; omega
  have hnlen : (List.replicate n b).length = n := by simp
  have hp : ∀ i : Fin (List.replicate (m - 1) a ++ [b]).length,
      i.val + 1 < (List.replicate (m - 1) a ++ [b]).length → p[i.val] = a := by
    intro i hi
    simp [p, show i.val < m - 1 by omega]
  have hlast : p[(List.replicate (m - 1) a ++ [b]).length - 1] = b := by simp [p]
  have ht : ∀ j : Fin (List.replicate n b).length, t[j.val] = b := by
    intro j
    change (List.replicate n b).toArray[j.val]'(by simpa using j.isLt) = b
    rw [List.getElem_toArray]
    exact List.getElem_replicate (a := b) (n := n) (i := j.val) j.isLt
  have hm' : 2 ≤ (List.replicate (m - 1) a ++ [b]).length := by omega
  let prepared := preprocess p
  have hgs : ∀ i : Fin (List.replicate (m - 1) a ++ [b]).length,
      0 < prepared.ret.2[i.val] :=
    fun i => (preprocess_goodSuffix p i).1
  have hcounts := search_best_comparisons p t a b hab hm' hp hlast ht
  dsimp only at hcounts
  have hcost := search_cost p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []
  dsimp only [prepared] at hcost
  have hprep : (preprocess p).time =
      (preprocess (List.replicate (m - 1) a ++ [b]).toArray.toVector).time :=
    preprocess_cast_time _ _
  have hm0 : (List.replicate (m - 1) a ++ [b]).length ≠ 0 := by omega
  have hn0 : ¬(List.replicate n b).length < (List.replicate (m - 1) a ++ [b]).length := by
    omega
  simp only [boyerMooreMatches, matchWithCounts, hm0, hn0, ↓reduceDIte,
    time_map, time_bind, time_tick, time_pure]
  change (List.replicate (m - 1) a ++ [b]).length + (List.replicate n b).length +
    ((preprocess p).time +
    ((search p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []).time +
      ((search p t (by omega) prepared.ret.1 prepared.ret.2 hgs 0 []).ret.outputs + 0))) = _
  dsimp only [prepared]
  rw [← hprep]
  have hdivision : (List.replicate n b).length /
      (List.replicate (m - 1) a ++ [b]).length = n / m := by rw [hlength, hnlen]
  rw [hdivision] at hcounts
  nlinarith [hcost.1, hcounts.1, hcounts.2.1, hcounts.2.2]

end Cslib.Algorithms.Lean.TimeM
