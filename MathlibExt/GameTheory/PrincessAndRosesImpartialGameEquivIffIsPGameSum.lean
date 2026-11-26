/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SpragueGrundy

/-!
# Equivalence of impartial games via their sum

Two finite impartial games are equivalent exactly when the position of their sum in which
both games are at their starting positions is a P-position.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 5 (`integers-2026-G4-lem-5`).
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace impartialGame_equiv_iff_isP_gameSum

private theorem sum_mem_left (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (a' : G.Pos) (h : a' ∈ G.moves a) :
    ((a', b) : (gameSum G H).Pos) ∈
      (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a', b) : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨a', h, rfl⟩

private theorem sum_mem_right (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (b' : H.Pos) (h : b' ∈ H.moves b) :
    ((a, b') : (gameSum G H).Pos) ∈
      (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a, b') : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨b', h, rfl⟩

private theorem sum_cases (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
    (q : (gameSum G H).Pos)
    (h : q ∈ (gameSum G H).moves ((a, b) : (gameSum G H).Pos)) :
    (∃ a', ∃ _ : a' ∈ G.moves a, q = ((a', b) : (gameSum G H).Pos)) ∨
      (∃ b', ∃ _ : b' ∈ H.moves b, q = ((a, b') : (gameSum G H).Pos)) := by
  let := (gameSum G H).eqDec
  have hdisj := Finset.mem_union.mp h
  cases hdisj with
  | inl hl =>
    obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hl
    exact Or.inl ⟨a', ha', heq.symm⟩
  | inr hr =>
    obtain ⟨b', hb', heq⟩ := Finset.mem_image.mp hr
    exact Or.inr ⟨b', hb', heq.symm⟩

private theorem isP_sum_self_diag (G : ImpartialGame) (a : G.Pos) :
    IsP (gameSum G G) ((a, a) : (gameSum G G).Pos) := by
  induction a using (wfRel G).induction with
  | h a ih =>
    refine (isP_iff _ _).mpr ?_
    intro q hq
    rcases sum_cases G G a a q hq with ⟨a', ha', rfl⟩ | ⟨a', ha', rfl⟩
    · intro hCon
      exact (isP_iff _ _).mp hCon _ (sum_mem_right G G a' a a' ha') (ih a' ha')
    · intro hCon
      exact (isP_iff _ _).mp hCon _ (sum_mem_left G G a a' a' ha') (ih a' ha')

private theorem isP_sum_symm (G H : ImpartialGame) (a : G.Pos) (b : H.Pos) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      IsP (gameSum H G) ((b, a) : (gameSum H G).Pos) := by
  revert b
  induction a using (wfRel G).induction with
  | h a iha =>
    intro b
    induction b using (wfRel H).induction with
    | h b ihb =>
      refine (isP_iff _ _).trans (Iff.trans ?_ (isP_iff _ _).symm)
      constructor
      · intro hall q hq
        rcases sum_cases H G b a q hq with ⟨b', hb', rfl⟩ | ⟨a', ha', rfl⟩
        · rw [← ihb b' hb']
          exact hall _ (sum_mem_right G H a b b' hb')
        · rw [← iha a' ha' b]
          exact hall _ (sum_mem_left G H a b a' ha')
      · intro hall q hq
        rcases sum_cases G H a b q hq with ⟨a', ha', rfl⟩ | ⟨b', hb', rfl⟩
        · rw [iha a' ha' b]
          exact hall _ (sum_mem_right H G b a a' ha')
        · rw [ihb b' hb']
          exact hall _ (sum_mem_left H G b a b' hb')

private theorem nim_mem (n : ℕ) (k j : Fin (n + 1)) :
    j ∈ (nimHeap n).moves k ↔ j.val < k.val := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩

private theorem isP_nim_sum_diag (n m v : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1))
    (hi : i.val ≤ v) (hj : j.val ≤ v) (heq : i.val = j.val) :
    IsP (gameSum (nimHeap n) (nimHeap m))
      ((i, j) : (gameSum (nimHeap n) (nimHeap m)).Pos) := by
  induction v generalizing i j with
  | zero =>
    clear hj
    have hi0 : i.val = 0 := Nat.le_zero.mp hi
    refine (isP_iff _ _).mpr ?_
    intro q hq
    rcases sum_cases _ _ _ _ q hq with ⟨i', hi', rfl⟩ | ⟨j', hj', rfl⟩
    · have hlt : i'.val < i.val := (nim_mem n i i').mp hi'
      rw [hi0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    · have hlt : j'.val < j.val := (nim_mem m j j').mp hj'
      rw [← heq, hi0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
  | succ v ih =>
    refine (isP_iff _ _).mpr ?_
    intro q hq
    rcases sum_cases _ _ _ _ q hq with ⟨i', hi', rfl⟩ | ⟨j', hj', rfl⟩
    · have hlt : i'.val < i.val := (nim_mem n i i').mp hi'
      have hle : i'.val ≤ v := by omega
      have hltm : i'.val < m + 1 := by
        have hjm : j.val < m + 1 := j.isLt
        omega
      have hmem : ((i', ⟨i'.val, hltm⟩) : (gameSum (nimHeap n) (nimHeap m)).Pos) ∈
          (gameSum (nimHeap n) (nimHeap m)).moves ((i', j) : _) :=
        sum_mem_right _ _ _ _ _ ((nim_mem m j ⟨i'.val, hltm⟩).mpr (by
          change i'.val < j.val
          omega))
      have hP : IsP (gameSum (nimHeap n) (nimHeap m))
          ((i', ⟨i'.val, hltm⟩) : _) := ih i' ⟨i'.val, hltm⟩ hle hle rfl
      intro hC
      exact (isP_iff _ _).mp hC _ hmem hP
    · have hlt : j'.val < j.val := (nim_mem m j j').mp hj'
      have hle : j'.val ≤ v := by omega
      have hltn : j'.val < n + 1 := by
        have him : i.val < n + 1 := i.isLt
        omega
      have hmem : ((⟨j'.val, hltn⟩, j') : (gameSum (nimHeap n) (nimHeap m)).Pos) ∈
          (gameSum (nimHeap n) (nimHeap m)).moves ((i, j') : _) :=
        sum_mem_left _ _ _ _ _ ((nim_mem n i ⟨j'.val, hltn⟩).mpr (by
          change j'.val < i.val
          omega))
      have hP : IsP (gameSum (nimHeap n) (nimHeap m))
          ((⟨j'.val, hltn⟩, j') : _) := ih ⟨j'.val, hltn⟩ j' hle hle rfl
      intro hC
      exact (isP_iff _ _).mp hC _ hmem hP

private theorem nim_sum_eq_of_isP (n m : ℕ)
    (h : IsP (gameSum (nimHeap n) (nimHeap m))
      (((nimHeap n).start, (nimHeap m).start) :
        (gameSum (nimHeap n) (nimHeap m)).Pos)) :
    n = m := by
  by_contra hne
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hnm : n < m + 1 := by omega
    have hmem : (((nimHeap n).start, ⟨n, hnm⟩) :
          (gameSum (nimHeap n) (nimHeap m)).Pos) ∈
        (gameSum (nimHeap n) (nimHeap m)).moves
          (((nimHeap n).start, (nimHeap m).start) : _) :=
      sum_mem_right _ _ _ _ _ ((nim_mem m _ _).mpr (by
        change n < m
        exact hlt))
    have hP : IsP (gameSum (nimHeap n) (nimHeap m))
        (((nimHeap n).start, ⟨n, hnm⟩) : _) :=
      isP_nim_sum_diag n m n _ _ (Nat.le_refl _) (Nat.le_refl _) rfl
    exact (isP_iff _ _).mp h _ hmem hP
  · exact absurd heq hne
  · have hmn : m < n + 1 := by omega
    have hmem : ((⟨m, hmn⟩, (nimHeap m).start) :
          (gameSum (nimHeap n) (nimHeap m)).Pos) ∈
        (gameSum (nimHeap n) (nimHeap m)).moves
          (((nimHeap n).start, (nimHeap m).start) : _) :=
      sum_mem_left _ _ _ _ _ ((nim_mem n _ _).mpr (by
        change m < n
        exact hgt))
    have hP : IsP (gameSum (nimHeap n) (nimHeap m))
        ((⟨m, hmn⟩, (nimHeap m).start) : _) :=
      isP_nim_sum_diag n m m _ _ (Nat.le_refl _) (Nat.le_refl _) rfl
    exact (isP_iff _ _).mp h _ hmem hP

end impartialGame_equiv_iff_isP_gameSum

open impartialGame_equiv_iff_isP_gameSum in
/-- **Equivalence of impartial games via their sum.** Two finite impartial games $G$ and $H$ are
equivalent if and only if their sum $G + H$ is a P-position, that is, the position of $G + H$ in
which both $G$ and $H$ are at their starting positions is a P-position.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 5 (`integers-2026-G4-lem-5`). -/
public theorem impartialGame_equiv_iff_isP_gameSum (G H : ImpartialGame) :
    Equiv G H ↔ IsP (gameSum G H) ((G.start, H.start) : (gameSum G H).Pos) := by
  constructor
  · intro hEquiv
    exact (hEquiv H).mpr (isP_sum_self_diag H H.start)
  · intro hP
    obtain ⟨n, hn⟩ := sprague_grundy G
    obtain ⟨m, hm⟩ := sprague_grundy H
    have hnm : IsP (gameSum (nimHeap n) (nimHeap m))
        (((nimHeap n).start, (nimHeap m).start) :
          (gameSum (nimHeap n) (nimHeap m)).Pos) :=
      (hn (nimHeap m)).mp ((isP_sum_symm G (nimHeap m) _ _).mpr
        ((hm G).mp ((isP_sum_symm H G _ _).mpr hP)))
    have heq : n = m := nim_sum_eq_of_isP n m hnm
    subst heq
    intro K
    exact (hn K).trans (hm K).symm

end MetaMathlibExt
