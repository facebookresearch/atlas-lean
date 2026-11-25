/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CubeNim
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.LawfulXor.Basic
import Mathlib.Tactic.FinCases
import MathlibExt.GameTheory.BoutonNim

/-!
# Misère face Nim on a cube

`cubeFaceNim_misere_pPositions` classifies the losing positions by their six-heap nim-sum,
with the misère parity rule when all heaps have size at most one.
-/

namespace MetaMathlibExt

namespace cubeFaceNim_misere_pPositions

open Function

private abbrev Position := Fin 6 → ℕ

private def nimSum (p : Position) := p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5

private abbrev Small (p : Position) := ∀ k, p k < 2

private def Losing (p : Position) := nimSum p = if Small p then 1 else 0

private theorem xor_small {a b : ℕ} (ha : a < 2) (hb : b < 2) : a ^^^ b < 2 :=
  Nat.xor_lt_two_pow (n := 1) ha hb

private theorem nimSum_small {p : Position} (hp : Small p) : nimSum p < 2 := by
  unfold nimSum
  repeat' apply xor_small
  all_goals apply hp

private theorem nimSum_update (p : Position) (i : Fin 6) (x : ℕ) :
    nimSum (update p i x) = nimSum (update p i 0) ^^^ x := by
  fin_cases i <;> simp [nimSum, Function.update] <;> ac_rfl

private theorem small_update (p : Position) (i : Fin 6) (x : ℕ) :
    Small (update p i x) ↔ Small (update p i 0) ∧ x < 2 := by
  have small_iff (y : ℕ) : Small (update p i y) ↔ y < 2 ∧ ∀ k ≠ i, p k < 2 := by
    change (∀ k, update p i y k < 2) ↔ _
    rw [← and_forall_ne i]
    simp +contextual
  simp [small_iff, and_comm]

-- With the other five heaps fixed, there is exactly one losing size for this heap.
private def target (p : Position) (i : Fin 6) : ℕ :=
  let rest := update p i 0
  if Small rest then nimSum rest ^^^ 1 else nimSum rest

private theorem losing_update (p : Position) (i : Fin 6) (x : ℕ) :
    Losing (update p i x) ↔ x = target p i := by
  simp only [Losing, nimSum_update p i x, small_update p i x, target]
  by_cases h : Small (update p i 0)
  · have hs := nimSum_small h
    have ht := xor_small hs (by decide : 1 < 2)
    by_cases hx : x < 2
    · rw [ite_eq_left h, ite_eq_left ⟨h, hx⟩, xor_eq_iff_right_eq]
    · rw [ite_eq_left h, ite_eq_right (fun H => hx H.2), xor_eq_zero_iff]
      omega
  · simp only [h, false_and, ite_false, xor_eq_zero_iff]
    exact eq_comm

private theorem losing_iff_target (p : Position) (i : Fin 6) :
    Losing p ↔ p i = target p i := by
  simpa using losing_update p i (p i)

private theorem move_iff {p q : Position} :
    CubeFaceMove p q ↔ ∃ i, q i < p i ∧ q = update p i (q i) := by
  constructor
  · rintro ⟨i, hle, hne, hfix⟩
    have hstrict : q i ≠ p i := fun he => hne (funext ((and_forall_ne i).mp ⟨he, hfix⟩))
    exact ⟨i, (hle i).lt_of_ne hstrict, eq_update_iff.mpr ⟨rfl, hfix⟩⟩
  · rintro ⟨i, hi, he⟩
    have hfix := (eq_update_iff.mp he).2
    exact ⟨i, (and_forall_ne i).mp ⟨hi.le, fun k hk => (hfix k hk).le⟩,
      fun h => hi.ne (congrFun h i), hfix⟩

private theorem move_update {p : Position} {i : Fin 6} {x : ℕ} (hx : x < p i) :
    CubeFaceMove p (update p i x) :=
  move_iff.mpr ⟨i, by simpa using hx, by simp⟩

private theorem losing_no_move {p q : Position} (hp : Losing p) (hm : CubeFaceMove p q) :
    ¬ Losing q := by
  obtain ⟨i, hi, he⟩ := move_iff.mp hm
  intro hq
  have ht := (losing_update p i (q i)).mp (he ▸ hq)
  exact hi.ne (ht.trans ((losing_iff_target p i).mp hp).symm)

-- Transport the ordinary Nim move supplied by Bouton's theorem to the six labeled faces.
private theorem move_to_zero {p : Position} (hp : nimSum p ≠ 0) :
    ∃ (i : Fin 6) (x : ℕ), x < p i ∧ nimSum (update p i x) = 0 := by
  let l := List.ofFn p
  have fold_eq (q : Position) : (List.ofFn q).foldl Nat.xor 0 = nimSum q := by
    change 0 ^^^ q 0 ^^^ q 1 ^^^ q 2 ^^^ q 3 ^^^ q 4 ^^^ q 5 = _
    rw [Nat.zero_xor]
    rfl
  obtain ⟨j, x, hx, hz⟩ := (BoutonNim.bouton_nim_p_positions l).2 (by rwa [fold_eq])
  let i : Fin 6 := ⟨j, by simpa [l] using j.isLt⟩
  refine ⟨i, x, by simpa only [l, List.get_eq_getElem, List.getElem_ofFn, i] using hx, ?_⟩
  have he : List.ofFn (update p i x) = l.set j.val x := by
    apply List.ext_getElem
    · simp [l]
    · intro k hk hk'
      by_cases h : k = j.val
      · subst k
        simp only [List.getElem_ofFn, List.getElem_set_self, update_self, i]
      · rw [List.getElem_set_ne (Ne.symm h)]
        simp only [l, List.getElem_ofFn]
        exact update_of_ne (Fin.ne_of_val_ne h) _ _
  rwa [← fold_eq, he]

private theorem move_of_losing {p : Position} (hp : Losing p) : ∃ q, CubeFaceMove p q := by
  have hne : p ≠ 0 := by
    rintro rfl
    exact (by unfold Losing nimSum; decide : ¬ Losing 0) hp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact ⟨_, move_update (Nat.pos_of_ne_zero hi)⟩

private theorem move_to_losing {p : Position} (hm : ∃ q, CubeFaceMove p q) (hp : ¬ Losing p) :
    ∃ q, CubeFaceMove p q ∧ Losing q := by
  -- If all other heaps are small, aim for odd parity among the remaining singletons.
  by_cases h : ∃ i, 0 < p i ∧ Small (update p i 0)
  · obtain ⟨i, hi, hs⟩ := h
    have ht : target p i < 2 := by
      unfold target
      rw [ite_eq_left hs]
      exact xor_small (nimSum_small hs) (by decide)
    have hne := (losing_iff_target p i).not.mp hp
    exact ⟨_, move_update (show target p i < p i by omega), (losing_update p i _).mpr rfl⟩
  -- Otherwise a large heap survives any move, so Bouton's zero-xor move suffices.
  · obtain ⟨q, hq⟩ := hm
    obtain ⟨j, hj, -⟩ := move_iff.mp hq
    have hs : ¬ Small p := by
      intro hall
      apply h
      exact ⟨j, by omega, ((small_update p j (p j)).mp (by simpa using hall)).1⟩
    obtain ⟨i, x, hx, hz⟩ := move_to_zero (p := p) (by simpa [Losing, ite_eq_right hs] using hp)
    refine ⟨_, move_update hx, ?_⟩
    have hlarge : ¬ Small (update p i x) := fun hall =>
      h ⟨i, by omega, ((small_update p i x).mp hall).1⟩
    simpa only [Losing, ite_eq_right hlarge] using hz

private theorem classification (P : Set Position)
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : Position) : p ∈ P ↔ Losing p := by
  have ih (q) (hm : CubeFaceMove p q) : q ∈ P ↔ Losing q := classification P hP q
  constructor
  · intro hmem
    obtain ⟨hm, hout⟩ := (hP p).mp hmem
    by_contra hp
    obtain ⟨q, hq, hlose⟩ := move_to_losing hm hp
    exact hout q hq ((ih q hq).mpr hlose)
  · intro hp
    exact (hP p).mpr ⟨move_of_losing hp,
      fun q hq hmem => losing_no_move hp hq ((ih q hq).mp hmem)⟩
termination_by ∑ k, p k
decreasing_by
  obtain ⟨i, hi, -⟩ := move_iff.mp hm
  exact Finset.sum_lt_sum (fun k _ => hm.choose_spec.1 k) ⟨i, Finset.mem_univ _, hi⟩

end cubeFaceNim_misere_pPositions

open cubeFaceNim_misere_pPositions in
set_option linter.unusedVariables false in
/-- **Misère P-positions of face Nim on a cube.** Write positions of the game $C_F$ (Nim with six
heaps) as tuples $p = (a, b, c, A, B, C)$ of numbers of tokens on the faces
$f_a, f_b, f_c, f_A, f_B, f_C$, where $f_A$, $f_B$, $f_C$ are opposite $f_a$, $f_b$, $f_c$, and let
$\oplus$ be the Nim-sum (bitwise exclusive or) of natural numbers. Let $\mathcal P$ be any set
of positions such that a position lies in $\mathcal P$ if and only if it has a face move and
every face move from it leads to a position outside $\mathcal P$; this is the set of
P-positions under misère play, where the player making the last move loses. Let $p$ be a
position in which every entry is at most $C$, and $a \le A$, $b \le B$ and $a \le b$. Then
$p \in \mathcal P$ if and only if either $C \ge 2$ and $a \oplus b \oplus c \oplus A \oplus B
\oplus C = 0$, or $C < 2$ and $a \oplus b \oplus c \oplus A \oplus B \oplus C = 1$.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 9 (`integers-2025-G2-thm-9`). -/
public theorem cubeFaceNim_misere_pPositions (P : Set (Fin 6 → ℕ))
    (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)
    (p : Fin 6 → ℕ) (hC : ∀ k, p k ≤ p 5) (ha : p 0 ≤ p 3) (hb : p 1 ≤ p 4) (hab : p 0 ≤ p 1) :
    p ∈ P ↔ (2 ≤ p 5 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 0) ∨
      (p 5 < 2 ∧ p 0 ^^^ p 1 ^^^ p 2 ^^^ p 3 ^^^ p 4 ^^^ p 5 = 1) := by
  rw [classification P hP]
  have hs : Small p ↔ p 5 < 2 := ⟨fun h => h 5, fun h k => lt_of_le_of_lt (hC k) h⟩
  by_cases h : p 5 < 2
  · simp [Losing, hs, nimSum, h, Nat.not_le.mpr h]
  · simp [Losing, hs, nimSum, h, Nat.le_of_not_gt h]

end MetaMathlibExt
