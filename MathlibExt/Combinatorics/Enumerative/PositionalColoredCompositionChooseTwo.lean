/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositions

/-!
# Odd colored compositions and binomial-color compositions

For every `k ≥ 1`, the number `o(k) = c_{2,1}(k)` of odd colored compositions of `k` equals the
number of compositions of `k + 1` in which a part `p` has `p.choose 2` colors
(`odd_eq_choose_two_colorCompositions`).

Andrew Li and Hua Wang prove this with a bijection on tilings (Theorem 3.2 of the preprint
arXiv:2511.08529v1). The proof here uses recurrences instead. For `n ≥ 1`, increasing the first
part of a composition of `n`, or putting a part `1` in front of it, is a bijection from two copies
of the compositions of `n` onto the compositions of `n + 1`. Sum over the compositions of `n` the
odd colored weight, giving `o(n)`; the even colored weight, giving `e(n) = c_{2,0}(n)`; and the
product of the parts at the odd positions `3, 5, …`, giving `t(n)`. Sum likewise the binomial
weight `∏ᵢ (pᵢ.choose 2)`, giving `b(n)`; the first part times the binomial weight of the other
parts, giving `u(n)`; and the binomial weight of the parts after the first, giving `v(n)`. The
bijection gives, for `n ≥ 1`,
`o(n + 1) = o(n) + t(n) + e(n)`, `e(n + 1) = e(n) + o(n)`, `t(n + 1) = t(n) + e(n)`,
`b(n + 1) = b(n) + u(n)`, `u(n + 1) = u(n) + v(n) + b(n)` and `v(n + 1) = v(n) + b(n)`;
from `o(1) = t(1) = e(1) = u(1) = v(1) = 1` and `b(1) = 0`, induction on `n ≥ 1` gives
`o(n) = b(n + 1)`, `t(n) = u(n)` and `e(n) = v(n + 1)`.
-/

namespace MetaMathlibExt
namespace PositionalColoredCompositionChooseTwo

/-- Increase the first part of a list by one. -/
private def bump : List ℕ → List ℕ
  | [] => []
  | p :: ps => (p + 1) :: ps

/-- Increase the first part in the left copy, or prepend a unit part in the right copy. -/
private def extend {n : ℕ} (hn : 1 ≤ n) :
    Composition n ⊕ Composition n → Composition (n + 1)
  | .inl ⟨[], _, hs⟩ => by simp at hs; omega
  | .inl ⟨p :: ps, hp, hs⟩ =>
    ⟨(p + 1) :: ps, by
      simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩
  | .inr c =>
    ⟨1 :: c.blocks, by simpa using fun i (hi : i ∈ c.blocks) => c.blocks_pos hi, by
      simp [Nat.add_comm]⟩

/-- Undo the extension according to the size of the first part. -/
private def shorten {n : ℕ} : Composition (n + 1) → Composition n ⊕ Composition n
  | ⟨[], _, hs⟩ => by simp at hs
  | ⟨0 :: _, hp, _⟩ => by have := hp List.mem_cons_self; omega
  | ⟨1 :: ps, hp, hs⟩ =>
    .inr ⟨ps, fun hi => hp (List.mem_cons_of_mem _ hi), by simp only [List.sum_cons] at hs; omega⟩
  | ⟨(p + 2) :: ps, hp, hs⟩ =>
    .inl ⟨(p + 1) :: ps, by
      simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩

/-- For `n ≥ 1`, two copies of the compositions of `n` correspond to the compositions of
`n + 1`. -/
private def extendEquiv {n : ℕ} (hn : 1 ≤ n) :
    Composition n ⊕ Composition n ≃ Composition (n + 1) where
  toFun := extend hn
  invFun := shorten
  left_inv := by
    rintro (⟨_ | ⟨_ | p, ps⟩, hp, hs⟩ | c)
    · simp at hs; omega
    · have := hp List.mem_cons_self; omega
    · rfl
    · rfl
  right_inv := by
    rintro ⟨_ | ⟨_ | _ | p, ps⟩, hp, hs⟩
    · simp at hs
    · have := hp List.mem_cons_self; omega
    · rfl
    · rfl

/-- The sum of a weight of the list of parts over the compositions of `n`. -/
private def total (F : List ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ c : Composition n, F c.blocks

private theorem total_succ (F : List ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    total F (n + 1) = total (fun l => F (bump l)) n + total (fun l => F (1 :: l)) n := by
  unfold total
  rw [← Equiv.sum_comp (extendEquiv hn), Fintype.sum_sum_type]
  congr 1
  apply Finset.sum_congr rfl
  rintro ⟨_ | ⟨p, ps⟩, hp, hs⟩ _
  · simp at hs; omega
  · rfl

private theorem total_add (F G : List ℕ → ℕ) (n : ℕ) :
    total (fun l => F l + G l) n = total F n + total G n :=
  Finset.sum_add_distrib

private theorem total_one (F : List ℕ → ℕ) : total F 1 = F [1] := by
  rw [total, Fintype.sum_eq_single (Composition.ones 1)]
  · rfl
  · intro c hc
    exact absurd (Composition.eq_ones_iff.2 fun i hi =>
      le_antisymm (c.blocks_le hi) (c.one_le_blocks hi)) hc

/-- The product of alternate parts, starting with the first part exactly when `b` is true. -/
private def alt : Bool → List ℕ → ℕ
  | _, [] => 1
  | b, p :: ps => (if b then p else 1) * alt (!b) ps

/-- The weight `alt false` of the parts after the first one, and `0` for no parts. -/
private def tailAlt : List ℕ → ℕ
  | [] => 0
  | _ :: ps => alt false ps

/-- The product of the binomial coefficients `p.choose 2` over the parts `p`. -/
private def binW (l : List ℕ) : ℕ :=
  (l.map fun p => p.choose 2).prod

/-- The first part times the binomial weight of the other parts, and `0` for no parts. -/
private def headBin : List ℕ → ℕ
  | [] => 0
  | p :: ps => p * binW ps

/-- The binomial weight of the parts after the first one, and `0` for no parts. -/
private def tailBin : List ℕ → ℕ
  | [] => 0
  | _ :: ps => binW ps

private theorem total_altTrue_succ {n : ℕ} (hn : 1 ≤ n) :
    total (alt true) (n + 1) = total (alt true) n + total tailAlt n + total (alt false) n := by
  have h₁ : (fun l => alt true (bump l)) = fun l => alt true l + tailAlt l := by
    funext l; cases l <;> simp [alt, bump, tailAlt, add_mul]
  have h₂ : (fun l => alt true (1 :: l)) = alt false := by
    funext l; simp [alt]
  rw [total_succ _ hn, h₁, h₂, total_add]

private theorem total_altFalse_succ {n : ℕ} (hn : 1 ≤ n) :
    total (alt false) (n + 1) = total (alt false) n + total (alt true) n := by
  have h₁ : (fun l => alt false (bump l)) = alt false := by
    funext l; cases l <;> simp [alt, bump]
  have h₂ : (fun l => alt false (1 :: l)) = alt true := by
    funext l; simp [alt]
  rw [total_succ _ hn, h₁, h₂]

private theorem total_tailAlt_succ {n : ℕ} (hn : 1 ≤ n) :
    total tailAlt (n + 1) = total tailAlt n + total (alt false) n := by
  have h₁ : (fun l => tailAlt (bump l)) = tailAlt := by
    funext l; cases l <;> simp [tailAlt, bump]
  have h₂ : (fun l => tailAlt (1 :: l)) = alt false := by
    funext l; simp [tailAlt]
  rw [total_succ _ hn, h₁, h₂]

private theorem total_binW_succ {n : ℕ} (hn : 1 ≤ n) :
    total binW (n + 1) = total binW n + total headBin n := by
  have h₁ : (fun l => binW (bump l)) = fun l => binW l + headBin l := by
    funext l; cases l <;> simp [binW, bump, headBin, Nat.choose_succ_succ, add_mul, add_comm]
  have h₂ : (fun l => binW (1 :: l)) = fun _ => 0 := by
    funext l; simp [binW]
  rw [total_succ _ hn, h₁, h₂, total_add]
  simp [total]

private theorem total_headBin_succ {n : ℕ} (hn : 1 ≤ n) :
    total headBin (n + 1) = total headBin n + total tailBin n + total binW n := by
  have h₁ : (fun l => headBin (bump l)) = fun l => headBin l + tailBin l := by
    funext l; cases l <;> simp [headBin, bump, tailBin, add_mul]
  have h₂ : (fun l => headBin (1 :: l)) = binW := by
    funext l; simp [headBin]
  rw [total_succ _ hn, h₁, h₂, total_add]

private theorem total_tailBin_succ {n : ℕ} (hn : 1 ≤ n) :
    total tailBin (n + 1) = total tailBin n + total binW n := by
  have h₁ : (fun l => tailBin (bump l)) = tailBin := by
    funext l; cases l <;> simp [tailBin, bump]
  have h₂ : (fun l => tailBin (1 :: l)) = binW := by
    funext l; simp [tailBin]
  rw [total_succ _ hn, h₁, h₂]

/-- The three sequences built from the odd colored weight agree with the three built from the
binomial weight. -/
private theorem total_alt_eq (n : ℕ) (hn : 1 ≤ n) :
    total (alt true) n = total binW (n + 1) ∧ total tailAlt n = total headBin n ∧
      total (alt false) n = total tailBin (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [total_binW_succ le_rfl, total_tailBin_succ le_rfl]
    simp [total_one, alt, tailAlt, binW, headBin, tailBin]
  | succ n hn ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    have r₁ := total_altTrue_succ hn
    have r₂ := total_altFalse_succ hn
    have r₃ := total_tailAlt_succ hn
    have r₄ := total_binW_succ (n := n + 1) (by omega)
    have r₅ := total_headBin_succ hn
    have r₆ := total_tailBin_succ hn
    have r₇ := total_tailBin_succ (n := n + 1) (by omega)
    refine ⟨?_, ?_, ?_⟩ <;> omega

private theorem alt_eq_mapIdx (ps : List ℕ) (j : ℕ) :
    alt (decide (j % 2 = 0)) ps =
      (ps.mapIdx fun i p => if (i + j) % 2 = 0 then p else 1).prod := by
  induction ps generalizing j with
  | nil => simp [alt]
  | cons p ps ih =>
    have flip : (!decide (j % 2 = 0)) = decide ((j + 1) % 2 = 0) := by
      by_cases h : j % 2 = 0 <;> simp [h] <;> omega
    simp [alt, List.mapIdx_cons, flip, ih, Nat.add_left_comm, Nat.add_comm]

/-- The odd colored weight of a list of parts, as written in `positionalColoredCompositionCount`.
-/
private theorem alt_true_eq (ps : List ℕ) :
    alt true ps = (ps.mapIdx fun i p => if (i + 1) % 2 = 1 % 2 then p else 1).prod := by
  have h := alt_eq_mapIdx ps 0
  simp only [Nat.zero_mod, decide_true, Nat.add_zero] at h
  rw [h]
  congr 2
  funext i p
  by_cases hi : i % 2 = 0 <;> simp [hi] <;> omega

end PositionalColoredCompositionChooseTwo

open PositionalColoredCompositionChooseTwo

/-- **Odd colored compositions and binomial-color compositions.** For every $k \ge 1$, the number
$o(k) = c_{2,1}(k)$ of odd colored compositions of $k$, in which only the parts at odd positions
are colored, equals the sum, over all compositions $(p_1, \dots, p_r)$ of $k + 1$, of
$\prod_i \binom{p_i}{2}$; that is, the number of compositions of $k + 1$ in which a part $p$ has
$\binom{p}{2}$ colors.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 2 (`integers-2026-A49-thm-2`). -/
public theorem odd_eq_choose_two_colorCompositions (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      ∑ c : Composition (k + 1), (c.blocks.map fun p => p.choose 2).prod := by
  have h := (total_alt_eq k hk).1
  unfold total binW at h
  rw [← h]
  unfold positionalColoredCompositionCount
  exact Finset.sum_congr rfl fun c _ => (alt_true_eq c.blocks).symm

end MetaMathlibExt
