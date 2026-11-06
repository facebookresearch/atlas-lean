/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMaskG0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMaskG1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMaskG2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMaskG3

/-! # The short transport check with the certified mask table

`shortCheckM` is `shortCheckF` with both preferred masks of every term read from the certified
mask table (`identMaskG_eq`), which is much cheaper in the kernel than computing them.
`shortCheckM_sound` gives `shortCheckF`, and `shortCheckM_split` splits a long check into two
checks, so that long lists can be checked in separate declarations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-- The mask table is the preferred mask on every flat short label. -/
theorem identMaskG_eq (j : ℕ) (hj : j < 98280) : identMaskG j = shortMaskF j := by
  have hc : j % 24576 / 64 < 384 := by omega
  have he : j % 24576 % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hj' : j = 24576 * (j / 24576) + 64 * (j % 24576 / 64) + j % 24576 % 64 := by omega
  have hr : j / 24576 < 4 := by omega
  interval_cases hq : j / 24576
  · have h := identMaskG_ok0 ⟨_, hc⟩ ⟨_, he⟩
    simp only at h
    rw [hj']
    simpa using h
  · have h := identMaskG_ok1 ⟨_, hc⟩ ⟨_, he⟩
    simp only at h
    rw [hj']
    simpa using h
  · have h := identMaskG_ok2 ⟨_, hc⟩ ⟨_, he⟩
    simp only at h
    rw [hj']
    simpa using h
  · have h := identMaskG_ok3 ⟨_, hc⟩ ⟨_, he⟩ (by simp only; omega)
    simp only at h
    rw [hj']
    simpa using h

/-- The check of one term with table masks. -/
def shortTermCheckM (d : QMaskP) (s t : ℕ × ℤ) : Bool :=
  Nat.blt s.1 98280 && Nat.blt t.1 98280 &&
    (d.stepP (identMaskG s.1, false)).1 == identMaskG t.1 &&
    t.2 == (if (d.stepP (identMaskG s.1, false)).2 then -s.2 else s.2)

/-- The check of a transported list with table masks. -/
def shortCheckM (d : QMaskP) : List (ℕ × ℤ) → List (ℕ × ℤ) → Bool
  | [], [] => true
  | s :: L, t :: L' => shortTermCheckM d s t && shortCheckM d L L'
  | _, _ => false

/-- A table check of one term is the fast check of the term. -/
theorem shortTermCheckM_sound (d : QMaskP) (s t : ℕ × ℤ) (h : shortTermCheckM d s t = true) :
    shortTermCheckF d s t = true := by
  simp only [shortTermCheckM, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hs, ht⟩, h1⟩, h2⟩ := h
  rw [identMaskG_eq _ hs, identMaskG_eq _ ht] at h1
  rw [identMaskG_eq _ hs] at h2
  simp only [shortTermCheckF, Bool.and_eq_true]
  exact ⟨h1, h2⟩

/-- A table check of a list is the fast check of the list. -/
theorem shortCheckM_sound (d : QMaskP) :
    ∀ S T : List (ℕ × ℤ), shortCheckM d S T = true → shortCheckF d S T = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [shortCheckM] at h
  | _ :: _, [], h => by simp [shortCheckM] at h
  | s :: S, t :: T, h => by
    simp only [shortCheckM, Bool.and_eq_true] at h
    simp only [shortCheckF, Bool.and_eq_true]
    exact ⟨shortTermCheckM_sound d s t h.1, shortCheckM_sound d S T h.2⟩

/-- A table check splits at any position. -/
theorem shortCheckM_split (d : QMaskP) :
    ∀ (n : ℕ) (S T : List (ℕ × ℤ)), shortCheckM d (S.take n) (T.take n) = true →
      shortCheckM d (S.drop n) (T.drop n) = true → shortCheckM d S T = true
  | 0, S, T, _, h2 => by simpa using h2
  | n + 1, [], [], _, _ => rfl
  | n + 1, [], _ :: _, h1, _ => by simp [shortCheckM] at h1
  | n + 1, _ :: _, [], h1, _ => by simp [shortCheckM] at h1
  | n + 1, s :: S, t :: T, h1, h2 => by
    simp only [List.take_succ_cons, shortCheckM, Bool.and_eq_true] at h1
    simp only [List.drop_succ_cons] at h2
    simp only [shortCheckM, Bool.and_eq_true]
    exact ⟨h1.1, shortCheckM_split d n S T h1.2 h2⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
