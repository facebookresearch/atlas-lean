/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import Cslib.Computability.Languages.RegularLanguage

/-!
# The pumping lemma for regular languages

This file lifts the automaton-level pumping lemma to a language-level interface and packages its
contrapositive as a reusable criterion for proving that a language is not regular.

## Main definitions

* `Cslib.Language.pump`: repeat the middle part of a word decomposition.
* `Cslib.Language.IsPumpingLength`: a natural number is a pumping length for a language.

## Main results

* `Cslib.Language.IsRegular.exists_isPumpingLength`: every regular language has a pumping length.
* `Cslib.Language.not_isRegular_of_pumping`: a language is not regular if every proposed pumping
  length admits a word for which every legal decomposition can be pumped outside the language.
-/

@[expose] public section

namespace Cslib.Language

open scoped Computability

variable {Symbol : Type*}

/-- Repeat the middle word `y` in the decomposition `x ++ y ++ z` exactly `i` times. -/
def pump (x y z : List Symbol) (i : ℕ) : List Symbol :=
  x ++ (List.replicate i y).flatten ++ z

@[simp]
theorem pump_zero (x y z : List Symbol) : pump x y z 0 = x ++ z := by
  simp [pump]

@[simp]
theorem pump_one (x y z : List Symbol) : pump x y z 1 = x ++ y ++ z := by
  simp [pump]

theorem pump_succ (x y z : List Symbol) (i : ℕ) :
    pump x y z (i + 1) = x ++ y ++ (List.replicate i y).flatten ++ z := by
  simp [pump, List.replicate_succ, List.append_assoc]

/-- `n` is a pumping length for `l` if every word in `l` of length at least `n` has a nonempty
middle part, contained in its first `n` symbols, that can be repeated any number of times while
remaining in `l`. -/
def IsPumpingLength (l : Language Symbol) (n : ℕ) : Prop :=
  ∀ w ∈ l, n ≤ w.length →
    ∃ x y z,
      w = x ++ y ++ z ∧
      x.length + y.length ≤ n ∧
      y ≠ [] ∧
      ∀ i, pump x y z i ∈ l

/-- Any larger number is also a pumping length. -/
theorem IsPumpingLength.mono {l : Language Symbol} {n m : ℕ}
    (hn : IsPumpingLength l n) (hnm : n ≤ m) : IsPumpingLength l m := by
  intro w hw hlen
  obtain ⟨x, y, z, hxyz, hprefix, hy, hpump⟩ := hn w hw (hnm.trans hlen)
  exact ⟨x, y, z, hxyz, hprefix.trans hnm, hy, hpump⟩

/-- The property of being a pumping length is upward closed. -/
theorem isPumpingLength_iff_forall_ge {l : Language Symbol} {n : ℕ} :
    IsPumpingLength l n ↔ ∀ m ≥ n, IsPumpingLength l m := by
  constructor
  · exact fun hn m hnm ↦ hn.mono hnm
  · exact fun h ↦ h n le_rfl

/-- A bound strictly above the lengths of all words in a language is vacuously a pumping length. -/
theorem IsPumpingLength.of_forall_length_lt {l : Language Symbol} {n : ℕ}
    (h : ∀ w ∈ l, w.length < n) : IsPumpingLength l n := by
  intro w hw hlen
  exfalso
  exact (Nat.not_succ_le_self w.length) ((h w hw).trans_le hlen)

/-- Zero is a pumping length exactly for the empty language. -/
theorem isPumpingLength_zero_iff {l : Language Symbol} :
    IsPumpingLength l 0 ↔ l = 0 := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨x, y, z, _, hprefix, hy, _⟩ := h w hw (Nat.zero_le _)
    have : y.length = 0 := by omega
    exact hy (List.length_eq_zero_iff.mp this)
  · rintro rfl
    exact IsPumpingLength.of_forall_length_lt (by simp)

/-- The automaton pumping decomposition yields membership of every explicitly pumped word. -/
theorem mem_of_pumping_language_le {l : Language Symbol} {x y z : List Symbol}
    (h : {x} * ({y} : Language Symbol)∗ * {z} ≤ l) (i : ℕ) : pump x y z i ∈ l := by
  apply h
  apply Language.append_mem_mul
  · apply Language.append_mem_mul (by simp)
    apply Language.join_mem_kstar
    simp
  · simp

/-- Every regular language has a pumping length. -/
theorem IsRegular.exists_isPumpingLength {l : Language Symbol} (hl : l.IsRegular) :
    ∃ n, IsPumpingLength l n := by
  rcases hl with ⟨State, hState, M, rfl⟩
  let _ : Fintype State := hState
  refine ⟨Fintype.card State, ?_⟩
  intro w hw hlen
  obtain ⟨x, y, z, hxyz, hprefix, hy, hpump⟩ := M.pumping_lemma hw hlen
  exact ⟨x, y, z, hxyz, hprefix, hy, fun i ↦ mem_of_pumping_language_le hpump i⟩

/-- The least pumping length of a regular language, selected from the nonempty set supplied by the
pumping lemma. -/
noncomputable def IsRegular.pumpingLength {l : Language Symbol} (hl : l.IsRegular) : ℕ :=
  by
    classical
    exact Nat.find (IsRegular.exists_isPumpingLength hl)

/-- The selected least pumping length is a pumping length. -/
theorem IsRegular.pumpingLength_spec {l : Language Symbol} (hl : l.IsRegular) :
    IsPumpingLength l (IsRegular.pumpingLength hl) := by
  classical
  exact Nat.find_spec (IsRegular.exists_isPumpingLength hl)

/-- No smaller number than `pumpingLength` is a pumping length. -/
theorem IsRegular.not_isPumpingLength_of_lt {l : Language Symbol} (hl : l.IsRegular) {n : ℕ}
    (hn : n < IsRegular.pumpingLength hl) : ¬IsPumpingLength l n := by
  classical
  exact Nat.find_min (IsRegular.exists_isPumpingLength hl) hn

/-- A regular language has least pumping length zero exactly when it is empty. -/
theorem IsRegular.pumpingLength_eq_zero_iff {l : Language Symbol} (hl : l.IsRegular) :
    IsRegular.pumpingLength hl = 0 ↔ l = 0 := by
  classical
  constructor
  · intro hzero
    apply isPumpingLength_zero_iff.mp
    simpa [hzero] using IsRegular.pumpingLength_spec hl
  · intro hlzero
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min'
    exact isPumpingLength_zero_iff.mpr hlzero

/-- A convenient elimination form of the pumping lemma for regular languages. -/
theorem IsRegular.pumping {l : Language Symbol} (hl : l.IsRegular) :
    ∃ n, ∀ w ∈ l, n ≤ w.length →
      ∃ x y z,
        w = x ++ y ++ z ∧
        x.length + y.length ≤ n ∧
        y ≠ [] ∧
        ∀ i, pump x y z i ∈ l :=
  IsRegular.exists_isPumpingLength hl

/-- If every proposed pumping length has a long word such that every legal decomposition can be
pumped outside the language, then the language is not regular. -/
theorem not_isRegular_of_pumping {l : Language Symbol}
    (h : ∀ n, ∃ w ∈ l, n ≤ w.length ∧
      ∀ x y z,
        w = x ++ y ++ z →
        x.length + y.length ≤ n →
        y ≠ [] →
        ∃ i, pump x y z i ∉ l) :
    ¬l.IsRegular := by
  intro hl
  obtain ⟨n, hn⟩ := IsRegular.exists_isPumpingLength hl
  obtain ⟨w, hw, hlen, hbad⟩ := h n
  obtain ⟨x, y, z, hxyz, hprefix, hy, hpump⟩ := hn w hw hlen
  obtain ⟨i, hi⟩ := hbad x y z hxyz hprefix hy
  exact hi (hpump i)

/-- It suffices to choose one fixed pump count for each proposed pumping length and legal
decomposition. -/
theorem not_isRegular_of_fixed_pump {l : Language Symbol}
    (h : ∀ n, ∃ w ∈ l, n ≤ w.length ∧ ∃ i,
      ∀ x y z,
        w = x ++ y ++ z →
        x.length + y.length ≤ n →
        y ≠ [] →
        pump x y z i ∉ l) :
    ¬l.IsRegular := by
  apply not_isRegular_of_pumping
  intro n
  obtain ⟨w, hw, hlen, i, hi⟩ := h n
  exact ⟨w, hw, hlen, fun x y z hxyz hprefix hy ↦ ⟨i, hi x y z hxyz hprefix hy⟩⟩

/-- The common special case in which deleting the middle part always leaves the language. -/
theorem not_isRegular_of_pump_zero {l : Language Symbol}
    (h : ∀ n, ∃ w ∈ l, n ≤ w.length ∧
      ∀ x y z,
        w = x ++ y ++ z →
        x.length + y.length ≤ n →
        y ≠ [] →
        x ++ z ∉ l) :
    ¬l.IsRegular := by
  apply not_isRegular_of_fixed_pump
  intro n
  obtain ⟨w, hw, hlen, hdelete⟩ := h n
  refine ⟨w, hw, hlen, 0, ?_⟩
  intro x y z hxyz hprefix hy
  simpa using hdelete x y z hxyz hprefix hy

end Cslib.Language
