/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic

namespace MetaMathlibExt

@[expose] public section

/-- `GridLRamseyProperty k n`: every `k`-coloring of the integer grid `[n] × [n]`,
`[n] = {1, …, n}`, contains a monochromatic L, i.e. positive integers `x`, `y`, `d`
such that the points `(x, y)`, `(x + d, y)`, `(x + d, y + d)` all lie in `[n] × [n]`
and have the same color. A coloring is a map `ℕ × ℕ → Fin k`; its values off the
grid are irrelevant. The grid Ramsey number `R_k(L)` is the least `n` with this
property, so `R_k(L) ≤ N` is `GridLRamseyProperty k N` (the property is monotone in
`n`, see `GridLRamseyProperty.mono`).

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 1 and the
definition of `R_k(L)` following it. -/
public def GridLRamseyProperty (k n : ℕ) : Prop :=
  ∀ c : ℕ × ℕ → Fin k, ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ n ∧ y + d ≤ n ∧
    c (x, y) = c (x + d, y) ∧ c (x + d, y) = c (x + d, y + d)

/-- A larger grid contains every L of a smaller one, so `GridLRamseyProperty k` is
monotone in the grid size.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of `R_k(L)`). -/
public theorem GridLRamseyProperty.mono {k m n : ℕ} (h : GridLRamseyProperty k m)
    (hmn : m ≤ n) : GridLRamseyProperty k n := by
  intro c
  obtain ⟨x, y, d, hx, hy, hd, hxd, hyd, h1, h2⟩ := h c
  exact ⟨x, y, d, hx, hy, hd, by omega, by omega, h1, h2⟩

/-- The `1 × 1` grid has no L at all.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of an L). -/
public theorem not_gridLRamseyProperty_one_one : ¬ GridLRamseyProperty 1 1 := by
  intro h
  obtain ⟨x, y, d, hx, _, hd, hxd, _⟩ := h fun _ => 0
  omega

/-- With one color, the `2 × 2` grid already contains the monochromatic L
`(1, 1), (2, 1), (2, 2)`, so `R_1(L) = 2`.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21 (definition of `R_k(L)`). -/
public theorem gridLRamseyProperty_one_two : GridLRamseyProperty 1 2 := by
  intro c
  exact ⟨1, 1, 1, by omega, by omega, by omega, by omega, by omega,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Grid Ramsey theorem for Ls: for every positive integer `k` there is a positive
integer `n` such that every `k`-coloring of `[n] × [n]` contains a monochromatic L
`(x, y), (x + d, y), (x + d, y + d)` with `x, y, d` positive.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 1 (quoted there
from earlier work). -/
public theorem_wanted exists_gridLRamseyProperty (k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ GridLRamseyProperty k n

/-- `R_3(L) ≤ 2593`: every 3-coloring of `[2593] × [2593]` contains a monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 2 (quoted there from
earlier work). -/
public theorem_wanted gridLRamseyProperty_three_2593 : GridLRamseyProperty 3 2593

/-- `R_3(L) ≤ 1804`: every 3-coloring of `[1804] × [1804]` contains a monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 3. -/
public theorem_wanted gridLRamseyProperty_three_1804 : GridLRamseyProperty 3 1804

/-- `R_3(L) ≤ 1573`: every 3-coloring of `[1573] × [1573]` contains a monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 4. -/
public theorem_wanted gridLRamseyProperty_three_1573 : GridLRamseyProperty 3 1573

/-- `R_3(L) ≤ 772`: every 3-coloring of `[772] × [772]` contains a monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 5. -/
public theorem_wanted gridLRamseyProperty_three_772 : GridLRamseyProperty 3 772

/-- `R_3(L) ≤ 493`, the paper's main bound: every 3-coloring of `[493] × [493]`
contains a monochromatic L. By `GridLRamseyProperty.mono` it implies the bounds of
Theorems 2–5.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 6. -/
public theorem_wanted gridLRamseyProperty_three_493 : GridLRamseyProperty 3 493


/-- Lemma 1 (corrected threshold): let `n ≥ 3` and let `c` be a 3-coloring of
`[n] × [n]` with distinct colors `red` and `blue`. Fix a diagonal `x - y = s` (`s ≥ 1`)
and a set `X` of positions such that, for `x ∈ X`, the point `(x + s, x)` is blue and is
forced by red to be blue: the main-diagonal points `(x, x)` and `(x + s, x + s)` are red,
so `(x, x), (x + s, x), (x + s, x + s)` would be a red L (Definition 1). If
`binom(|X|, 2) > n - 2`, then `c` has a monochromatic L. The paper's threshold
`|X| ≥ ⌈√(2n - 15/4) + 1/2⌉` is meant as the least `b` with `binom(b, 2)/(n - 2) > 1` (its
proof); the closed form is one too small when `√(2n - 15/4) + 1/2` is an integer, and the
lemma then fails: for `n = 3` the coloring with red diagonal, `(2,1), (3,2), (2,3)` blue,
`(3,1)` green and `(1,2), (1,3)` red has two forced blue points and no monochromatic L.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Lemma 1. -/
public theorem_wanted exists_mono_L_of_forced_blue_diagonal (n : ℕ) (hn : 3 ≤ n)
    (c : ℕ × ℕ → Fin 3) (red blue : Fin 3) (hrb : red ≠ blue) (s : ℕ) (hs : 0 < s)
    (X : Finset ℕ)
    (hX : ∀ x ∈ X, 0 < x ∧ x + s ≤ n ∧ c (x + s, x) = blue ∧ c (x, x) = red ∧
      c (x + s, x + s) = red)
    (hcard : n - 2 < X.card.choose 2) :
    ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ n ∧ y + d ≤ n ∧
      c (x, y) = c (x + d, y) ∧ c (x + d, y) = c (x + d, y + d)

end

end MetaMathlibExt
