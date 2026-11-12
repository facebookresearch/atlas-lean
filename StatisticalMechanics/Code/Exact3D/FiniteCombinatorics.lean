/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.Data.Fin.Tuple.Sort








namespace StatMech
namespace Exact3D

set_option linter.style.longLine false in


theorem card_le_card_of_injective_rankedPrefix
    {Slot : Type*}
    (target : Finset Slot)
    {n k : ℕ}
    (slotAt : Fin n → Slot)
    (hk : k ≤ n)
    (hinj : Function.Injective slotAt)
    (hprefix : ∀ i : Fin n, (i : ℕ) < k → slotAt i ∈ target) :
    k ≤ target.card := by
  let route : Fin k → {slot // slot ∈ target} := fun i =>
    ⟨slotAt ⟨i.1, lt_of_lt_of_le i.2 hk⟩,
      hprefix ⟨i.1, lt_of_lt_of_le i.2 hk⟩ i.2⟩
  have hrouteInj : Function.Injective route := by
    intro i j hij
    have hslotEq :
        slotAt ⟨i.1, lt_of_lt_of_le i.2 hk⟩ =
          slotAt ⟨j.1, lt_of_lt_of_le j.2 hk⟩ := by
      exact congrArg Subtype.val hij
    have hidxEq :
        (⟨i.1, lt_of_lt_of_le i.2 hk⟩ : Fin n) =
          ⟨j.1, lt_of_lt_of_le j.2 hk⟩ :=
      hinj hslotEq
    apply Fin.ext
    exact congrArg (fun x : Fin n => (x : ℕ)) hidxEq
  have hcard : Fintype.card (Fin k) ≤ Fintype.card {slot // slot ∈ target} :=
    Fintype.card_le_of_injective route hrouteInj
  simpa using hcard

set_option linter.style.longLine false in



theorem exists_sortedFinsetEnumeration
    {α : Type*}
    (s : Finset α)
    (score : α → ℝ) :
    ∃ itemAt : Fin s.card → α,
      (∀ i, itemAt i ∈ s) ∧
        Function.Injective itemAt ∧
          (∀ x, x ∈ s → ∃ i, itemAt i = x) ∧
            (∀ i j : Fin s.card, (i : ℕ) ≤ (j : ℕ) →
              score (itemAt j) ≤ score (itemAt i)) := by
  classical
  let Sub := {x // x ∈ s}
  let e : Sub ≃ Fin (Fintype.card Sub) := Fintype.equivFin Sub
  have hcard : Fintype.card Sub = s.card := by
    simp [Sub]
  let base : Fin s.card → Sub := fun i => e.symm (Fin.cast hcard.symm i)
  have hbaseInj : Function.Injective base := by
    intro i j hij
    have hcastEq : Fin.cast hcard.symm i = Fin.cast hcard.symm j := by
      apply Equiv.injective e.symm
      simpa [base] using hij
    apply Fin.ext
    exact congrArg (fun x : Fin (Fintype.card Sub) => (x : ℕ)) hcastEq
  let key : Fin s.card → ℝ := fun i => -score (base i).1
  let perm := Tuple.sort key
  let itemAt : Fin s.card → α := fun i => (base (perm i)).1
  refine ⟨itemAt, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (base (perm i)).2
  · intro i j hij
    have hbaseEq : base (perm i) = base (perm j) := Subtype.ext hij
    have hpermEq : perm i = perm j := hbaseInj hbaseEq
    exact Equiv.injective perm hpermEq
  · intro x hx
    let p : Sub := ⟨x, hx⟩
    let raw : Fin s.card := Fin.cast hcard (e p)
    refine ⟨perm.symm raw, ?_⟩
    have hperm : perm (perm.symm raw) = raw := by simp [perm]
    have hbase : base raw = p := by
      apply Equiv.injective e
      simp [base, raw]
    calc
      itemAt (perm.symm raw) = (base (perm (perm.symm raw))).1 := rfl
      _ = (base raw).1 := by rw [hperm]
      _ = x := by rw [hbase]
  · intro i j hij
    have hmono : key (perm i) ≤ key (perm j) :=
      Tuple.monotone_sort key hij
    change -score (base (perm i)).1 ≤ -score (base (perm j)).1 at hmono
    change score (base (perm j)).1 ≤ score (base (perm i)).1
    linarith

set_option linter.style.longLine false in






theorem sortedEnumeration_mem_thresholdTail_of_lt_filter_card
    {α : Type*}
    (s : Finset α)
    (score : α → ℝ)
    (itemAt : Fin s.card → α)
    (hitemSurj : ∀ x, x ∈ s → ∃ i, itemAt i = x)
    (hitemSorted : ∀ (i j : Fin s.card), (i : ℕ) ≤ (j : ℕ) →
      score (itemAt j) ≤ score (itemAt i))
    {threshold : ℝ}
    (i : Fin s.card)
    (hi : (i : ℕ) < (s.filter (fun x => threshold ≤ score x)).card) :
    threshold ≤ score (itemAt i) := by
  classical
  let tail := s.filter (fun x => threshold ≤ score x)
  by_contra hnot
  let idx : {x // x ∈ tail} → Fin s.card := fun x =>
    Classical.choose
      (hitemSurj x.1 (Finset.mem_filter.mp x.2).1)
  have hidxSpec : ∀ x : {x // x ∈ tail}, itemAt (idx x) = x.1 := by
    intro x
    exact Classical.choose_spec
      (hitemSurj x.1 (Finset.mem_filter.mp x.2).1)
  have hidxLt : ∀ x : {x // x ∈ tail}, (idx x : ℕ) < (i : ℕ) := by
    intro x
    have hxThreshold : threshold ≤ score (itemAt (idx x)) := by
      have hxTail : threshold ≤ score x.1 := (Finset.mem_filter.mp x.2).2
      simpa [hidxSpec x] using hxTail
    have hnotGe : ¬ (i : ℕ) ≤ (idx x : ℕ) := by
      intro hge
      have hle := hitemSorted i (idx x) hge
      exact hnot (hxThreshold.trans hle)
    exact Nat.lt_of_not_ge hnotGe
  let route : {x // x ∈ tail} → Fin (i : ℕ) := fun x =>
    ⟨(idx x : ℕ), hidxLt x⟩
  have hrouteInj : Function.Injective route := by
    intro x y hxy
    have hidxEq : idx x = idx y := by
      apply Fin.ext
      exact congrArg (fun z : Fin (i : ℕ) => (z : ℕ)) hxy
    apply Subtype.ext
    calc
      x.1 = itemAt (idx x) := (hidxSpec x).symm
      _ = itemAt (idx y) := by rw [hidxEq]
      _ = y.1 := hidxSpec y
  have hcardLeFin :
      Fintype.card {x // x ∈ tail} ≤ Fintype.card (Fin (i : ℕ)) :=
    Fintype.card_le_of_injective route hrouteInj
  have hcardLe : tail.card ≤ (i : ℕ) := by
    simpa [tail] using hcardLeFin
  exact (not_lt_of_ge hcardLe) (by simpa [tail] using hi)

end Exact3D
end StatMech
