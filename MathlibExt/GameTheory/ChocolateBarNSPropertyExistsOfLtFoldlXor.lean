/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
public import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Bitwise

/-! # The mex step for chocolate bars with many functions

At the highest bit where the current nim-sum and a smaller target differ, a coordinate or the
width can be lowered to reach the target. The width-image identity converts an unclamped width
move into a legal move that clamps the coordinates.
-/

namespace MetaMathlibExt

private theorem foldl_xor_cons (a : ℕ) (l : List ℕ) :
    (a :: l).foldl (· ^^^ ·) 0 = a ^^^ l.foldl (· ^^^ ·) 0 := by
  let : Std.Associative (α := ℕ) (· ^^^ ·) := ⟨Nat.xor_assoc⟩
  rw [List.foldl_cons, Nat.zero_xor]
  have h : l.foldl (· ^^^ ·) (a ^^^ 0) = a ^^^ l.foldl (· ^^^ ·) 0 := List.foldl_assoc
  rwa [Nat.xor_zero] at h

/-- **Change one coordinate of a nim-sum by an XOR mask.** Replacing `x i` by `x i ^^^ d`
XORs the nim-sum of all coordinates with the same mask `d`. -/
public theorem foldl_xor_update {m : ℕ} (x : Fin m → ℕ) (i : Fin m) (d : ℕ) :
    (List.ofFn (Function.update x i (x i ^^^ d))).foldl (· ^^^ ·) 0 =
      (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ d := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · have htail : (fun j : Fin m ↦ Function.update x 0 (x 0 ^^^ d) j.succ) =
          (fun j ↦ x j.succ) :=
        funext fun j ↦ Function.update_of_ne j.succ_ne_zero _ _
      simp only [List.ofFn_succ, foldl_xor_cons, Function.update_self, htail]
      rw [Nat.xor_assoc, Nat.xor_comm d, ← Nat.xor_assoc]
    · have htail : (fun j : Fin m ↦ Function.update x i.succ (x i.succ ^^^ d) j.succ) =
          Function.update (fun j ↦ x j.succ) i (x i.succ ^^^ d) := by
        funext j
        by_cases h : j = i
        · subst j
          simp
        · rw [Function.update_of_ne (Fin.succ_inj.not.mpr h), Function.update_of_ne h]
      simp only [List.ofFn_succ, foldl_xor_cons,
        Function.update_of_ne i.succ_ne_zero.symm, htail, ih, Nat.xor_assoc]

private theorem foldl_xor_testBit_false {l : List ℕ} {k : ℕ}
    (h : ∀ a ∈ l, a.testBit k = false) : (l.foldl (· ^^^ ·) 0).testBit k = false := by
  induction l with
  | nil => exact Nat.zero_testBit k
  | cons a l ih =>
    rw [foldl_xor_cons, Nat.testBit_xor, h a (List.mem_cons_self),
      ih (fun b hb ↦ h b (List.mem_cons_of_mem a hb)), Bool.false_xor]

/-- **Mex step for chocolate bars with many functions.** Let $m$ be a natural number, let
$f_1, \dots, f_m : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_1, \dots, x_m, z, c$ be natural numbers with $x_t \le f_t(z)$ for all $t$ and
$c < x_1 \oplus \cdots \oplus x_m \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or).
Then either there are an index $i$ and some $u < x_i$ such that $c$ is the nim-sum
$x_1 \oplus \cdots \oplus x_m \oplus z$ with $x_i$ replaced by $u$, or there is some $w < z$
with $c = \min(x_1, f_1(w)) \oplus \cdots \oplus \min(x_m, f_m(w)) \oplus w$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 4 (`integers-2025-G3-lem-4`). -/
public theorem exists_of_lt_foldl_xor {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z c : ℕ} (hx : ∀ t, x t ≤ f t z)
    (hc : c < (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ z) :
    (∃ i, ∃ u < x i, c = (List.ofFn (Function.update x i u)).foldl (· ^^^ ·) 0 ^^^ z) ∨
      ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w := by
  let s := (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ z
  let d := s ^^^ c
  change c < s at hc
  have hc_eq : c = s ^^^ d := by
    rw [show d = s ^^^ c from rfl, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hd : d ≠ 0 := fun h ↦ hc.ne (by simpa only [h, Nat.xor_zero] using hc_eq)
  obtain ⟨k, hk, habove⟩ := Nat.exists_most_significant_bit hd
  -- The highest changed bit is set in the original nim-sum, since the target is smaller.
  have hs : s.testBit k = true := by
    by_contra h
    have hs0 := Bool.eq_false_of_not_eq_true h
    have hc1 : c.testBit k = true := by
      simp only [hc_eq, Nat.testBit_xor, hs0, hk, Bool.false_xor]
    exact Nat.lt_asymm hc (Nat.lt_of_testBit k hs0 hc1 fun j hj ↦ by
      rw [hc_eq, Nat.testBit_xor s d, habove j hj, Bool.xor_false])
  have hdecrease {a : ℕ} (ha : a.testBit k = true) : a ^^^ d < a := by
    refine Nat.lt_of_testBit k ?_ ha ?_
    · simp only [Nat.testBit_xor, ha, hk, Bool.xor_self]
    · intro j hj
      rw [Nat.testBit_xor a d, habove j hj, Bool.xor_false]
  by_cases hz : z.testBit k = true
  · right
    have hw : c ∈ {v | ∃ w < z, v = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ w} :=
      ⟨z ^^^ d, hdecrease hz, by simpa only [s, Nat.xor_assoc] using hc_eq⟩
    rwa [image_foldl_xor_eq_image_min hf hx] at hw
  · have hi : ∃ i, (x i).testBit k = true := by
      by_contra h
      have hfold : ((List.ofFn x).foldl (· ^^^ ·) 0).testBit k = false := by
        apply foldl_xor_testBit_false
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact Bool.eq_false_of_not_eq_true fun hb ↦ h ⟨i, hb⟩
      have hs0 : s.testBit k = false := by
        simp only [s, Nat.testBit_xor, hfold, Bool.eq_false_of_not_eq_true hz, Bool.false_xor]
      exact Bool.false_ne_true (hs0.symm.trans hs)
    obtain ⟨i, hi⟩ := hi
    refine Or.inl ⟨i, x i ^^^ d, hdecrease hi, ?_⟩
    change c = (List.ofFn (Function.update x i (x i ^^^ d))).foldl (· ^^^ ·) 0 ^^^ z
    rw [foldl_xor_update, Nat.xor_assoc, Nat.xor_comm d z, ← Nat.xor_assoc]
    exact hc_eq

end MetaMathlibExt
