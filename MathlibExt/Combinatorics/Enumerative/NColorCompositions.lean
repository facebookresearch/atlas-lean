/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Finite.Sigma
import Mathlib.Tactic.LinearCombination

/-!
# Restricted n-color compositions and the Hopkins–Wang tribonacci numbers

For compositions using only colors 3 and 4, counting by the color of the first part and the
size of the tail gives a recurrence. It implies that the counts at `n` and `n - 2` sum to
`Nat.fib (n - 1)` for `3 ≤ n`.

Let `t(0) = 1`, `t(1) = 0`, `t(2) = 1` and `t(n) = t(n-1) + t(n-2) + t(n-3)` for `n ≥ 3`, and
set `t(n) = 0` for `n < 0`; on the naturals this is `tribNat`, on the integers `trib`. This file
proves that for every natural number `k ≥ 1`, with `n = 3k + 2`,
`t(n) + t(n-2) = 2 + 2 ∑_{i=0}^{k-1} t(n-3i-1)` (`trib_add_two_sub_three_mul_add_two`).

## Proof outline

All indices are nonnegative, so the identity is one about `tribNat`, where the sum reads
`s(k) = t(3k+1) + t(3k-2) + ⋯ + t(4)`. Induct on `k`. For `k = 1` both sides equal
`t(5) + t(3) = 6 + 2 = 2 + 2 t(4)`. Passing from `k` to `k + 1` adds `2 t(3k+4)` to the right
side, and adds `t(3k+5) + t(3k+3) - t(3k+2) - t(3k)` to the left side. Expanding `t(3k+5)` and
then `t(3k+3)` by the recurrence turns the latter into
`t(3k+4) + t(3k+3) + t(3k+2) + t(3k+1) = 2 t(3k+4)`. The identity also holds for `k = 0`, where
it reads `t(2) + t(0) = 2`, but the statement keeps the hypothesis `k ≥ 1`.

## Implementation notes

`tribNat`, `trib` and `trib_add_two_sub_three_mul_add_two` keep the full names, bodies,
statements and docstrings they had in
`WantedExt.Combinatorics.Enumerative.NColorCompositionsWanted`, so their namespace reads
`NColorCompositionsWanted`. That module imports this one and keeps its other wanted statements
about these numbers and about restricted `n`-color compositions; the docstring of
`trib_add_two_sub_three_mul_add_two` cites the source of the statement.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- **Tribonacci numbers with initial values $1, 0, 1$.** The sequence
$t : \mathbb{N} \to \mathbb{Z}$ with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$. -/
def tribNat : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => tribNat (n + 2) + tribNat (n + 1) + tribNat n

/-- **Hopkins–Wang tribonacci numbers on the integers.** Let $t(0) = 1$, $t(1) = 0$,
$t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for natural numbers $n \ge 3$. This
extends $t$ to an integer-valued function on all integers by setting $t(n) = 0$ for
$n < 0$. -/
def trib (n : ℤ) : ℤ :=
  if 0 ≤ n then tribNat n.toNat else 0

/-- At an integer equal to a natural number `m`, `trib` takes the value `tribNat m`. -/
private theorem trib_eq_tribNat {n : ℤ} {m : ℕ} (h : n = m) : trib n = tribNat m := by
  simp [trib, h]

/-- The recurrence of `tribNat`. -/
private theorem tribNat_add_three (n : ℕ) :
    tribNat (n + 3) = tribNat (n + 2) + tribNat (n + 1) + tribNat n :=
  rfl

/-- The identity for `tribNat`, with the sum indexed as `t(3(k - i) + 1)` for `i < k`. -/
private theorem tribNat_add_two_sub_three_mul_add_two (k : ℕ) (hk : 1 ≤ k) :
    tribNat (3 * k + 2) + tribNat (3 * k) =
      2 + 2 * ∑ i ∈ Finset.range k, tribNat (3 * (k - i) + 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    have h3 : tribNat (3 * k + 3) =
        tribNat (3 * k + 2) + tribNat (3 * k + 1) + tribNat (3 * k) := tribNat_add_three _
    have h4 : tribNat (3 * k + 4) =
        tribNat (3 * k + 3) + tribNat (3 * k + 2) + tribNat (3 * k + 1) := tribNat_add_three _
    have h5 : tribNat (3 * k + 5) =
        tribNat (3 * k + 4) + tribNat (3 * k + 3) + tribNat (3 * k + 2) := tribNat_add_three _
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [show 3 * (k + 1) + 2 = 3 * k + 5 by omega, show 3 * (k + 1) + 1 = 3 * k + 4 by omega,
      show 3 * (k + 1) = 3 * k + 3 by omega]
    linear_combination h5 - h4 + h3 + ih

/-- **Identity for $t(n) + t(n-2)$ when $n \ge 3$ and $n \equiv 2 \pmod 3$.** Let $t$ be the
tribonacci numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every
natural number $k \ge 1$, with $n = 3k + 2$,
$$t(n) + t(n-2) = 2 + 2 \sum_{i=0}^{k-1} t(n-3i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem trib_add_two_sub_three_mul_add_two (k : ℕ)
    (hk : 1 ≤ k) :
    trib (3 * (k : ℤ) + 2) + trib (3 * (k : ℤ) + 2 - 2) =
      2 + 2 * ∑ i ∈ Finset.range k,
        trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) := by
  have hsum : ∑ i ∈ Finset.range k, trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) =
      ∑ i ∈ Finset.range k, tribNat (3 * (k - i) + 1) :=
    Finset.sum_congr rfl fun i hi =>
      trib_eq_tribNat (by have := Finset.mem_range.mp hi; omega)
  rw [trib_eq_tribNat (m := 3 * k + 2) (by omega), trib_eq_tribNat (m := 3 * k) (by omega), hsum]
  exact tribNat_add_two_sub_three_mul_add_two k hk

/-- **n-color compositions with two allowed consecutive colors.** For natural numbers $b$ and $n$,
$\mathrm{CCo}_{b,b+1}(n)$ is the set of $n$-color compositions of $n$ that use only the colors $b$
and $b+1$: finite sequences of pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural numbers (part
$k_i$ with color $c_i$) such that $1 \le c_i \le k_i$ and $c_i \in \{b, b+1\}$ for every $i$, and
$k_1 + \dots + k_m = n$. -/
def ColorCompAllowed (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ (pc.2 = b ∨ pc.2 = b + 1)) ∧
      (l.map Prod.fst).sum = n }

/-- **Count of n-color compositions with two consecutive colors.** An $n$-color composition of a
natural number $n$ is a finite sequence of parts, each a positive integer $k$ carrying a color
$c$ with $1 \le c \le k$, whose sizes sum to $n$. For natural numbers $b$ and $n$,
$\operatorname{cco}_{b,b+1}(n)$ is the number of $n$-color compositions of $n$ in which every
part has color $b$ or $b+1$. -/
noncomputable def ccoAllowed (b n : ℕ) : ℕ :=
  Nat.card (ColorCompAllowed b n)

private theorem ccoAllowed_three_zero : ccoAllowed 3 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨[], by simp⟩, ?_⟩
  rintro ⟨_ | ⟨⟨k, c⟩, l⟩, hvalid, hsum⟩
  · rfl
  · have h := hvalid (k, c) (by simp)
    simp only [List.map_cons, List.sum_cons] at hsum
    omega

-- The first color is 3 + i. A tail of total m leaves a first part of size n + 1 - m,
-- which can carry that color exactly when m < n - 1 - i.
private abbrev ColoredTails (n : ℕ) :=
  (i : Fin 2) × (m : Fin (n - 1 - i.val)) × ColorCompAllowed 3 m.val

private def prependFirst (n : ℕ) (t : ColoredTails n) : ColorCompAllowed 3 (n + 1) := by
  obtain ⟨i, m, l, hvalid, hsum⟩ := t
  refine ⟨(n + 1 - m.val, 3 + i.val) :: l, ?_, ?_⟩
  · rw [List.forall_mem_cons]
    exact ⟨by dsimp; omega, hvalid⟩
  · simp only [List.map_cons, List.sum_cons, hsum]
    omega

private noncomputable def coloredTailsEquiv (n : ℕ) :
    ColoredTails n ≃ ColorCompAllowed 3 (n + 1) := by
  apply Equiv.ofBijective (prependFirst n)
  constructor
  · rintro ⟨i, m, l, hl, hs⟩ ⟨j, p, t, ht, hu⟩ h
    have he : (n + 1 - m.val, 3 + i.val) :: l = (n + 1 - p.val, 3 + j.val) :: t :=
      congrArg Subtype.val h
    obtain ⟨hc, rfl⟩ := List.cons.inj he
    have hij : i = j := Fin.ext (by simpa using congrArg Prod.snd hc)
    subst j
    have hmp : m = p := Fin.ext (hs.symm.trans hu)
    subst p
    rfl
  · rintro ⟨_ | ⟨⟨k, c⟩, l⟩, hvalid, hsum⟩
    · simp at hsum
    · obtain ⟨⟨_, hck, hc⟩, hl⟩ := List.forall_mem_cons.mp hvalid
      simp only [List.map_cons, List.sum_cons] at hsum
      dsimp at hck hc
      let i : Fin 2 := ⟨c - 3, by omega⟩
      let m : Fin (n - 1 - i.val) :=
        ⟨(l.map Prod.fst).sum, by dsimp [i]; omega⟩
      refine ⟨⟨i, m, l, hl, rfl⟩, Subtype.ext ?_⟩
      change (n + 1 - (l.map Prod.fst).sum, 3 + (c - 3)) :: l = (k, c) :: l
      congr 2 <;> omega

private instance finiteColorCompThree (n : ℕ) : Finite (ColorCompAllowed 3 n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact Nat.finite_of_card_ne_zero (ccoAllowed_three_zero.trans_ne Nat.one_ne_zero)
    | succ n =>
      have (i : Fin 2) (m : Fin (n - 1 - i.val)) : Finite (ColorCompAllowed 3 m.val) :=
        ih m.val (by omega)
      exact Finite.of_equiv _ (coloredTailsEquiv n)

private theorem ccoAllowed_three_succ (n : ℕ) :
    ccoAllowed 3 (n + 1) = (∑ m ∈ Finset.range (n - 1), ccoAllowed 3 m) +
      ∑ m ∈ Finset.range (n - 2), ccoAllowed 3 m := by
  unfold ccoAllowed
  rw [← Nat.card_congr (coloredTailsEquiv n)]
  simp only [ColoredTails, Nat.card_sigma, Fin.sum_univ_two, Fin.val_zero, Nat.sub_zero,
    Fin.val_one]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  rfl

private theorem ccoAllowed_three_step (n : ℕ) :
    ccoAllowed 3 (n + 4) = ccoAllowed 3 (n + 3) + ccoAllowed 3 (n + 1) + ccoAllowed 3 n := by
  rw [ccoAllowed_three_succ (n + 3), ccoAllowed_three_succ (n + 2)]
  simp only [Nat.add_sub_cancel, Nat.reduceSubDiff]
  rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ (n := n)]
  omega

/-- **Fibonacci identity for n-color compositions with colors 3 and 4.** For a natural number
$m$, let $\operatorname{cco}_{3,4}(m)$ be the number of $n$-color compositions of $m$ in which
every part has color $3$ or $4$, and let $F_k$ be the Fibonacci numbers with $F_0 = 0$ and
$F_1 = 1$. Then for every natural number $n \ge 3$,
$\operatorname{cco}_{3,4}(n) + \operatorname{cco}_{3,4}(n-2) = F_{n-1}$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 10. -/
theorem ccoAllowed_three_add (n : ℕ) (hn : 3 ≤ n) :
    ccoAllowed 3 n + ccoAllowed 3 (n - 2) = Nat.fib (n - 1) := by
  have hfib (m : ℕ) : ccoAllowed 3 (m + 2) + ccoAllowed 3 m = Nat.fib (m + 1) := by
    induction m using Nat.twoStepInduction with
    | zero =>
      rw [ccoAllowed_three_succ 1, ccoAllowed_three_zero]
      decide
    | one =>
      rw [ccoAllowed_three_succ 2, ccoAllowed_three_succ 0]
      simp [ccoAllowed_three_zero]
    | more m ih₀ ih₁ =>
      rw [ccoAllowed_three_step m, Nat.fib_add_two (n := m + 1), ← ih₀, ← ih₁]
      ac_rfl
  simpa [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] using hfib (n - 2)

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
