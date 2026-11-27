/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.BigOperators
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Floor and ceiling function sums

The ceiling form of Hermite's identity follows by reflecting the index in the floor form
at `-x`. We also define the inclusion-exclusion-like sums and Tverberg sums used with
these rounding functions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ceiling analogue of Hermite's identity.** For every real number $x$ and every natural
number $n$, $\sum_{k=1}^{n} \lceil x + k/n \rceil = \lceil n x \rceil + n$.

The paper assumes $n \ge 1$; for $n = 0$ both sides are $0$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 6. -/
public theorem sum_ceil_add_div_eq_ceil_mul_add (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ⌈x + (k : ℝ) / n⌉ = ⌈(n : ℝ) * x⌉ + n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  calc
    _ = ∑ i ∈ Finset.range n, ⌈x + ((n - i : ℕ) : ℝ) / n⌉ := by
      simpa [Nat.Ico_zero_eq_range, Finset.Ico_add_one_right_eq_Icc] using
        (Finset.sum_Ico_reflect (fun k : ℕ ↦ ⌈x + (k : ℝ) / n⌉) 0
          (Nat.le_succ n)).symm
    _ = ∑ i ∈ Finset.range n, (-⌊-x + (i : ℝ) / n⌋ + 1) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := (Finset.mem_range.mp hi).le
      rw [Nat.cast_sub hi', sub_div, div_self (Nat.cast_ne_zero.mpr hn),
        show x + (1 - (i : ℝ) / n) = -(-x + i / n) + 1 by ring,
        Int.ceil_add_one, Int.ceil_neg]
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, Int.sum_floor_add_div,
        mul_neg, Int.floor_neg]

/-- **Inclusion-exclusion-like sum.** For a function $F : \mathbb{R} \to \mathbb{Z}$ and real
numbers $x_1, \dots, x_n$, the inclusion-exclusion-like sum is the integer
$g^{(F)}(x_1, \dots, x_n) = \sum_T (-1)^{|T| - 1} F\left(\sum_{i \in T} x_i\right)$, where $T$
ranges over the nonempty subsets of $\{1, \dots, n\}$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public def inclExclLikeSum {n : ℕ} (F : ℝ → ℤ) (x : Fin n → ℝ) : ℤ :=
  ∑ T : Finset (Fin n) with T.Nonempty, (-1) ^ (T.card - 1) * F (∑ i ∈ T, x i)

/-- **The inclusion-exclusion-like sum in one variable.** For every function
$F : \mathbb{R} \to \mathbb{Z}$ and every real $x$, the inclusion-exclusion-like sum of $F$ in the
single variable $x$ is $g^{(F)}(x) = F(x)$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_one (F : ℝ → ℤ) (x : ℝ) : inclExclLikeSum F ![x] = F x := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

/-- **The inclusion-exclusion-like sum in two variables.** For every function
$F : \mathbb{R} \to \mathbb{Z}$ and all real numbers $x$ and $y$,
$g^{(F)}(x, y) = F(x) + F(y) - F(x + y)$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_two (F : ℝ → ℤ) (x y : ℝ) :
    inclExclLikeSum F ![x, y] = F x + F y - F (x + y) := by
  have h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

/-- **Tverberg's sum.** Let $F : \mathbb{R} \to \mathbb{Z}$, let $a = (a_1, \dots, a_\ell)$ be a
tuple of integers, let $m$ be a natural number and let $k$ be an integer. Tverberg's sum is
$f^{(F)}(a, m, k) = \sum_{T \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |T|}
F((k + \sum_{i \in T} a_i) / m)$, where the division is in $\mathbb{R}$ (with $x / 0 = 0$).

The paper takes $F = \lfloor \cdot \rfloor$ in Definition 1, and $F = \lceil \cdot \rceil$,
$x \mapsto \lfloor x + 1/2 \rfloor$ or $x \mapsto \lceil x - 1/2 \rceil$ in Section 1 and
Definition 3.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public noncomputable def tverbergSum {ℓ : ℕ} (F : ℝ → ℤ) (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) : ℤ :=
  ∑ T : Finset (Fin ℓ), (-1) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, a i : ℤ) : ℝ) / m)

/-- **Tverberg's sum of the empty tuple.** For every function $F : \mathbb{R} \to \mathbb{Z}$,
every natural number $m$ and every integer $k$, Tverberg's sum of the empty tuple of integers is
$f^{(F)}(\emptyset, m, k) = F(k / m)$, where $k / m$ is division in $\mathbb{R}$ (with $x / 0 = 0$).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_zero (F : ℝ → ℤ) (a : Fin 0 → ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F a m k = F (k / m) := by
  simp [tverbergSum, Finset.univ_unique, Finset.eq_empty_of_isEmpty]

/-- **Tverberg's sum of a single integer.** For every function $F : \mathbb{R} \to \mathbb{Z}$,
all integers $a$ and $k$ and every natural number $m$, Tverberg's sum of $F$ for the one-element
family $(a)$, modulus $m$ and shift $k$ equals $F((k + a)/m) - F(k/m)$, with $x/0 = 0$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_one (F : ℝ → ℤ) (a : ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F ![a] m k = F ((k + a : ℤ) / m) - F (k / m) := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [tverbergSum, h]
  ring

end

end MetaMathlibExt
