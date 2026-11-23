/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Tilings of grids, cylinders, and tori

Kagey and Keehn count the tilings of the `n × m` grid, cylinder and torus by a finite set `T` of
tile designs, up to symmetry. A tiling is a map `F` from the cells to `T`. A symmetry acts on the
cells by a map `φ` and on the designs by a permutation `σ`, and it fixes `F` when
`F (φ c) = σ (F c)` for every cell `c`; Burnside's lemma turns the numbers of fixed tilings into
the number of tilings up to symmetry. This file defines the number of fixed tilings and counts
the tilings of the rectangular grid fixed by the identity.

On the `n × m` cylinder, applying the shift `x ↦ x + a` and then the reflection
`x ↦ n - 1 - x` sends the column `x` to `-1 - x - a` modulo `n`, so the columns this map fixes
are the solutions of `x = -1 - x - a` in `ZMod n`. Kagey and Keehn solve this equation according
to the parities of `n` and `a`; this file proves the case of an odd modulus, and the case of an
even modulus with a shift whose representative `a.val` is odd.

## Main definitions

* `MetaMathlibExt.fixedTilingCount`: the number of maps `F : α → T` with `F (φ c) = σ (F c)`
  for every `c : α`.

## Main results

* `MetaMathlibExt.rectangularGrid_identity`: when `σ ^ 1 = 1`, all `|T| ^ (n * m)` tilings of
  the `n × m` grid are fixed by the identity map of the cells.
* `MetaMathlibExt.reflection_shift_solutions_odd`: for odd `n`, the solutions of
  `x = -1 - x - a` in `ZMod n` form the singleton `{((n + 1) / 2) * (-1 - a)}`.
* `MetaMathlibExt.reflection_shift_solutions_even_odd`: for even `n` and odd `a.val`, the
  solutions of `x = -1 - x - a` in `ZMod n` are the residues of the integers
  `(-1 - a.val) / 2` and `(n - 1 - a.val) / 2`.

## Implementation notes

The hypothesis `σ ^ 1 = 1` says that `σ = 1`, so the condition `F c = σ (F c)` holds for every
map `F`, and the fixed tilings are all `|T| ^ (n * m)` maps from the `n * m` cells to `T`.

The equation says `2 * x = -1 - a`. For odd `n` the division `(n + 1) / 2` is exact, and the
residue of its quotient is the inverse of `2` in `ZMod n`, since `2 * ((n + 1) / 2) = n + 1`.
Multiplying by it solves the equation, and multiplying back by `2` shows the solution is unique.

For even `n = 2 * k` and odd `a.val = 2 * j + 1`, both integer divisions are exact, with
quotients `-(j + 1)` and `k - (j + 1)`, and both residues solve the equation because
`2 * k = 0` in `ZMod n`. Conversely, a solution `x` gives `2 * y = 0` for `y = x + (j + 1)`, so
`n` divides `2 * y.val`; then `y.val < 2 * k` is a multiple of `k`, hence `y` is `0` or `k`.

## References

* Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
  Journal of Integer Sequences 27 (2024), Article 24.6.1; arXiv:2311.13072v2, Theorem 2.1.2
  (the tilings of the grid fixed by the identity) and Lemma 3.0.1.
-/

namespace MetaMathlibExt

/-- **Number of fixed tilings.** Let $\alpha$ (the cells) and $T$ (the tile designs) be finite sets,
let $\varphi : \alpha \to \alpha$ be a map and let $\sigma$ be a permutation of $T$. The number of
tilings fixed by $(\varphi, \sigma)$ is the number of maps $F : \alpha \to T$ such that
$F(\varphi(c)) = \sigma(F(c))$ for every $c \in \alpha$.

This is the paper's fixed-point condition $F(c \cdot s) = F(c) \cdot g$, with $\varphi$ encoding
the action on cells and $\sigma$ the action on designs. No ambient group action is assumed, since
each fixed-point formula involves a single symmetry.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting. -/
@[expose] public def fixedTilingCount {α T : Type*} [Fintype α] [DecidableEq α]
    [Fintype T] [DecidableEq T] (φ : α → α) (σ : Equiv.Perm T) : ℕ :=
  Fintype.card {F : α → T // ∀ c, F (φ c) = σ (F c)}

/-- **Rectangular-grid tilings fixed by the identity.** Let $n$ and $m$ be positive integers, let
$T$ be a finite set of tiles and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$, that is,
the identity. Then the number of tilings $F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with
$F(c) = \sigma(F(c))$ for every cell $c$ equals $|T|^{nm}$.

The Burnside conclusion of Theorem 22 is not part of this single-element fixed-point statement.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 22. -/
public theorem rectangularGrid_identity {T : Type*} [Fintype T] [DecidableEq T]
    (n m : ℕ) [NeZero n] [NeZero m] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    fixedTilingCount (id : ZMod n × ZMod m → ZMod n × ZMod m) σ =
      Fintype.card T ^ (n * m) := by
  -- `σ ^ 1 = 1` says that `σ` is the identity, so every tiling satisfies the condition.
  rw [pow_one] at hσ
  subst hσ
  have hfixed : ∀ F : ZMod n × ZMod m → T, ∀ c, F (id c) = (1 : Equiv.Perm T) (F c) :=
    fun _ _ => rfl
  -- The fixed tilings are then all the maps from the `n * m` cells to `T`.
  rw [fixedTilingCount, Fintype.card_congr (Equiv.subtypeUnivEquiv hfixed), Fintype.card_fun,
    Fintype.card_prod, ZMod.card, ZMod.card]

/-- **Solution of $x = -1-x-a$ modulo odd $n$.** Let $n$ be a positive odd integer and
$a \in \mathbb{Z}/n$. Then the set of $x \in \mathbb{Z}/n$ with $x = -1-x-a$ is the singleton
$\{k(-1-a)\}$, where $k$ is the residue mod $n$ of the integer $(n+1)/2$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_odd (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Odd n) :
    {x : ZMod n | x = -1 - x - a} =
      {(((n + 1) / 2 : ℕ) : ZMod n) * (-1 - a)} := by
  -- The residue of `(n + 1) / 2` is the inverse of `2`: twice it is `n + 1 = 1` in `ZMod n`.
  have hinv : (((n + 1) / 2 : ℕ) : ZMod n) * 2 = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod n)
      (Nat.div_mul_cancel (even_iff_two_dvd.mp hn.add_one))
    push_cast at h
    simpa using h
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    linear_combination (((n + 1) / 2 : ℕ) : ZMod n) * hx - x * hinv
  · rintro rfl
    linear_combination (-1 - a) * hinv

/-- **Solutions of $x = -1-x-a$ modulo even $n$ for odd $a$.** Let $n$ be a positive even
integer and $a \in \mathbb{Z}/n$ whose representative $\bar a \in \{0, \dots, n-1\}$ is odd.
Then the set of $x \in \mathbb{Z}/n$ with $x = -1-x-a$ consists of the residues mod $n$ of the
integers $(-1-\bar a)/2$ and $(n-1-\bar a)/2$.

The divisions by $2$ are exact divisions of integers, carried out before reducing mod $n$.

Source: Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*,
        Journal of Integer Sequences 27 (2024), Article 24.6.1, Lemma 25. -/
public theorem reflection_shift_solutions_even_odd (n : ℕ) [NeZero n]
    (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    {x : ZMod n | x = -1 - x - a} =
      {((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n),
        ((((n : ℤ) - 1 - a.val) / 2 : ℤ) : ZMod n)} := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨j, hj⟩ := ha
  -- Both divisions are exact, with quotients `-(j + 1)` and `k - (j + 1)`.
  have h₁ : ((-1 : ℤ) - a.val) / 2 = -(j + 1) := by
    rw [hj]
    push_cast
    omega
  have h₂ : ((n : ℤ) - 1 - a.val) / 2 = k - (j + 1) := by
    rw [hj, hk]
    push_cast
    omega
  -- In `ZMod n`, `a = 2 * j + 1` and `2 * k = n = 0`.
  have ha' : a = 2 * j + 1 := by
    rw [← ZMod.natCast_zmod_val a, hj]
    push_cast
    ring
  have hk' : (2 * k : ZMod n) = 0 := by
    rw [← ZMod.natCast_self n, hk]
    push_cast
    ring
  rw [h₁, h₂]
  push_cast
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    -- `y = x + (j + 1)` satisfies `2 * y = 0`, so `n = 2 * k` divides `2 * y.val`. Hence
    -- `y.val < 2 * k` is a multiple of `k`, that is `0` or `k`.
    set y : ZMod n := x + (j + 1) with hy
    have h2y : 2 * y = 0 := by linear_combination hx - ha'
    have hdvd : n ∣ 2 * y.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h2y
    have hlt := ZMod.val_lt y
    have hyv : y = (y.val : ZMod n) := (ZMod.natCast_zmod_val y).symm
    generalize y.val = v at hdvd hlt hyv
    subst hk
    obtain ⟨c, rfl⟩ : k ∣ v := by
      rw [← two_mul] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hc : c < 2 := Nat.lt_of_mul_lt_mul_left (a := k) (by omega)
    interval_cases c <;> push_cast at hyv
    · exact Or.inl (by linear_combination hy.symm.trans hyv)
    · exact Or.inr (by linear_combination hy.symm.trans hyv)
  · rintro (rfl | rfl)
    · linear_combination ha'
    · linear_combination ha' + hk'

end MetaMathlibExt
