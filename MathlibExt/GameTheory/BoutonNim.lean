/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.LawfulXor.Basic
import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace MetaMathlibExt.BoutonNim

/-- `foldl` with `Nat.xor` splits off the initial accumulator. -/
private theorem foldl_xor_init (l : List ℕ) (init : ℕ) :
    List.foldl Nat.xor init l = init ^^^ List.foldl Nat.xor 0 l := by
  revert init
  induction l with
  | nil =>
    intro init
    exact (Nat.xor_zero init).symm
  | cons a t ih =>
    intro init
    have hz : Nat.xor 0 a = a := Nat.zero_xor a
    have e3 : List.foldl Nat.xor 0 (a :: t) = (a ^^^ List.foldl Nat.xor 0 t) := by
      calc List.foldl Nat.xor 0 (a :: t)
          = List.foldl Nat.xor (Nat.xor 0 a) t := rfl
        _ = List.foldl Nat.xor a t := by rw [hz]
        _ = (a ^^^ List.foldl Nat.xor 0 t) := ih a
    calc List.foldl Nat.xor init (a :: t)
        = List.foldl Nat.xor (Nat.xor init a) t := rfl
      _ = (Nat.xor init a) ^^^ List.foldl Nat.xor 0 t := ih _
      _ = init ^^^ (a ^^^ List.foldl Nat.xor 0 t) := Nat.xor_assoc _ _ _
      _ = init ^^^ List.foldl Nat.xor 0 (a :: t) := by rw [e3]

/-- `foldl` with `Nat.xor` over a cons cell. -/
private theorem cons_fold (a : ℕ) (s : List ℕ) :
    List.foldl Nat.xor 0 (a :: s) = (a ^^^ List.foldl Nat.xor 0 s) := by
  have hz : Nat.xor 0 a = a := Nat.zero_xor a
  calc List.foldl Nat.xor 0 (a :: s)
      = List.foldl Nat.xor (Nat.xor 0 a) s := rfl
    _ = List.foldl Nat.xor a s := by rw [hz]
    _ = (a ^^^ List.foldl Nat.xor 0 s) := foldl_xor_init s a

/-- Replacing heap `idx` by `y` xors out the old heap and xors in `y`. -/
private theorem foldl_set (pos : List ℕ) (idx y : ℕ) (h : idx < pos.length) :
    List.foldl Nat.xor 0 (pos.set idx y)
      = (List.foldl Nat.xor 0 pos ^^^ pos[idx]'h ^^^ y) := by
  revert h
  revert idx
  induction pos with
  | nil =>
    intro idx h
    simp at h
  | cons a t ih =>
    intro idx h
    cases idx with
    | zero =>
      have hs : (a :: t).set 0 y = y :: t := rfl
      have hg : (a :: t)[0]'h = a := List.getElem_cons_zero _ _ _
      simp only [hs, hg, cons_fold]
      have key : ((a ^^^ List.foldl Nat.xor 0 t) ^^^ a)
          = List.foldl Nat.xor 0 t := by
        calc ((a ^^^ List.foldl Nat.xor 0 t) ^^^ a)
            = a ^^^ (List.foldl Nat.xor 0 t ^^^ a) := Nat.xor_assoc _ _ _
          _ = a ^^^ (a ^^^ List.foldl Nat.xor 0 t) := by
              rw [Nat.xor_comm (List.foldl Nat.xor 0 t) a]
          _ = (a ^^^ a) ^^^ List.foldl Nat.xor 0 t := (Nat.xor_assoc _ _ _).symm
          _ = List.foldl Nat.xor 0 t := by rw [Nat.xor_self, Nat.zero_xor]
      rw [key]
      exact Nat.xor_comm _ _
    | succ n =>
      have hlen : (a :: t).length = t.length + 1 := rfl
      have h' : n < t.length := by
        rw [hlen] at h
        exact Nat.lt_of_succ_lt_succ h
      have hs : (a :: t).set (n + 1) y = a :: (t.set n y) := rfl
      have hg : (a :: t)[n + 1]'h = t[n]'h' := List.getElem_cons_succ _ _ _ _
      have ih' := ih n h'
      simp only [hs, hg, cons_fold, ih']
      rw [Nat.xor_assoc a _ _, ← Nat.xor_assoc a _ _]

/-- Bit `k` of the nim-sum is false when every heap has bit `k` false. -/
private theorem foldl_testBit_false : ∀ (l : List ℕ) (k : ℕ),
    (∀ x ∈ l, x.testBit k = false) →
    (List.foldl Nat.xor 0 l).testBit k = false := by
  intro l k
  induction l with
  | nil =>
    intro hall
    exact Nat.zero_testBit k
  | cons a t ih =>
    intro hall
    have ha : a.testBit k = false := hall a (by simp)
    have ht : ∀ x ∈ t, x.testBit k = false :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have e := ih ht
    rw [cons_fold a t, Nat.testBit_xor, ha, e, Bool.false_xor]

/-- `Nat.xor` vanishes exactly on equal arguments. -/
private theorem xor_eq_zero_iff (a b : ℕ) : (a ^^^ b = 0) ↔ a = b := by
  constructor
  · intro h
    have h2 : (a ^^^ b) ^^^ b = a := by
      calc (a ^^^ b) ^^^ b
          = a ^^^ (b ^^^ b) := Nat.xor_assoc _ _ _
        _ = a := by rw [Nat.xor_self, Nat.xor_zero]
    rw [h, Nat.zero_xor] at h2
    exact h2.symm
  · intro h
    subst h
    exact Nat.xor_self _

/-- The `Fin`-indexed version of `foldl_set`, for the main theorem. -/
private theorem foldl_set_fin (pos : List ℕ) (i : Fin pos.length) (y : ℕ) :
    List.foldl Nat.xor 0 (pos.set i.val y)
      = (List.foldl Nat.xor 0 pos ^^^ pos.get i ^^^ y) := by
  have h := foldl_set pos i.val y i.isLt
  rw [List.get_eq_getElem]
  exact h

/-- **Bouton's move properties in Nim.** Let a Nim position be a finite list of heap sizes
$a_1, \dots, a_n \in \mathbb{N}$, with nim-sum $a_1 \oplus \cdots \oplus a_n$, where $\oplus$
is bitwise exclusive or and the empty list has nim-sum $0$. A move chooses an index $i$ and
replaces $a_i$ by a natural number $y < a_i$. Then: (i) if the position has nim-sum $0$, every
move leads to a position with nonzero nim-sum; (ii) if the position has nonzero nim-sum, some
move leads to a position with nim-sum $0$.

Positions with no move (the empty list and the all-zero lists) have nim-sum $0$, so the two
properties determine the normal-play labelling by induction on the game: the positions with
nim-sum $0$ are exactly the P-positions (previous player wins) and the others are the
N-positions.

Source: Tanya Khovanova and Joshua Xiong, "Nim Fractals", Journal of Integer
Sequences 17 (2014), theorem lines 155–159,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex
complete-source SHA-256
`6f8be9d461ff98b5a7c878830eb169e69ba8dd7540948d9149527fdb5ca7783a`,
normalized theorem lines 157–159 SHA-256
`d0cc29c58096c58f4d34f2b9e3d199a1316f13e98b5170e9c316c5385ce6e43f`.
Proves `Wanted` entry `bouton_nim_p_positions`.
-/
theorem bouton_nim_p_positions
    (pos : List ℕ) :
    (List.foldl Nat.xor 0 pos = 0 →
      ∀ (i : Fin pos.length) (y : ℕ), y < pos.get i →
        List.foldl Nat.xor 0 (pos.set i.val y) ≠ 0) ∧
    (List.foldl Nat.xor 0 pos ≠ 0 →
      ∃ (i : Fin pos.length) (y : ℕ), y < pos.get i ∧
        List.foldl Nat.xor 0 (pos.set i.val y) = 0) := by
  constructor
  · intro hs0 i y hylt hcon
    have hset := foldl_set_fin pos i y
    rw [hs0, Nat.zero_xor] at hset
    have h0 : pos.get i ^^^ y = 0 := hset.symm.trans hcon
    have heq : pos.get i = y := (xor_eq_zero_iff _ _).mp h0
    exact (ne_of_lt hylt) heq.symm
  · intro hne
    obtain ⟨k, hk_true, hk_above⟩ := Nat.exists_most_significant_bit hne
    have hex : ∃ x ∈ pos, x.testBit k = true := by
      by_contra habs
      push Not at habs
      have hfalse :=
        foldl_testBit_false pos k (fun x hx => by simpa using habs x hx)
      rw [hk_true] at hfalse
      exact Bool.noConfusion hfalse
    obtain ⟨x, hx_mem, hx_bit⟩ := hex
    obtain ⟨i, hi_eq⟩ := List.mem_iff_get.mp hx_mem
    refine ⟨i, List.foldl Nat.xor 0 pos ^^^ pos.get i, ?_, ?_⟩
    · have hx_bit' : (pos.get i).testBit k = true := by
        rw [hi_eq]
        exact hx_bit
      have hy_bit : (List.foldl Nat.xor 0 pos ^^^ pos.get i).testBit k = false := by
        rw [Nat.testBit_xor, hk_true, hx_bit']
        rfl
      have hagree : ∀ j, k < j →
          (List.foldl Nat.xor 0 pos ^^^ pos.get i).testBit j
            = (pos.get i).testBit j := by
        intro j hj
        rw [Nat.testBit_xor, hk_above j hj, Bool.false_xor]
      exact Nat.lt_of_testBit k hy_bit hx_bit' hagree
    · have hset :=
        foldl_set_fin pos i (List.foldl Nat.xor 0 pos ^^^ pos.get i)
      rw [hset]
      exact Nat.xor_self _

end MetaMathlibExt.BoutonNim
