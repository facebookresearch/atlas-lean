/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ZeckendorfOdometer
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# New-information zones of the Zeckendorf odometer

This file defines the prefix values `v_k` of digit sequences (`zeckAdicPrefixValue`), the sets
`CST_k` (`zeckCST`) and the new-information zones `NIZ_k = CST_k \ CST_{k-1}` (`zeckNIZ`) of the
algorithm of Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf
Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of
Integer Sequences 27 (2024), Article 24.3.2 (definitions read from arXiv:2309.14285v2). It also
defines the truncated variations `Δ_k^{(r)}` (`zeckAdicTruncVariation`) and the variation
`Δ^{(r)}` (`zeckAdicVariation`) of the Zeckendorf sum of digits on digit sequences.

For `r ≥ 1` and `k ≥ 2`, every Zeckendorf-adic integer in `NIZ_k` has leading digits
`x_{k+1} = x_k = 0` (`zeckNIZ_leading_zeros`, Lemma 5.3 in arXiv:2309.14285v2).

If the cylinder `C_{00 n_{k-1} ⋯ n_2}` lies in `NIZ_k`, then the cylinder `C_{0010 n_{k-1} ⋯ n_2}`
lies in `NIZ_{k+2}` (`zeckNIZ_cylinder_shift`, Lemma 5.4 in arXiv:2309.14285v2).

For `ℓ ≥ 3` and the shift `r = F_ℓ`, among the `v < F_{ℓ+3}` whose digit sequence `i(v)` lies in
`NIZ_{ℓ+1}`, exactly `F_{ℓ-1}` have `Δ^{(F_ℓ)}(i(v)) = 0` and exactly `F_{ℓ-2}` have
`Δ^{(F_ℓ)}(i(v)) = 1` (`zeckNIZ_fib_variation_order_succ`, Proposition 6.3 in arXiv:2309.14285v2).

For `zeckNIZ_leading_zeros`, write `v_k = v_{k-1} + x_{k+1} F_{k+1}` and
`v_{k-1} = v_{k-2} + x_k F_k`, where `v_{k-2} < F_k` and `v_{k-1} < F_{k+1}` because no two
consecutive digits are `1`. If `x_{k+1} = 1`, then `x_k = 0` and `v_{k-1} < F_k`, and membership
in `CST_k` forces `v_{k-1} + r < F_k`. If `x_{k+1} = 0` and `x_k = 1`, then
`F_k ≤ v_k = v_{k-1} < F_{k+1}`, and membership in `CST_k` forces `v_{k-1} + r < F_{k+1}`. Either
way `x` lies in `CST_{k-1}`, so it is not in `NIZ_k`.

The proof of `zeckNIZ_cylinder_shift` works directly with the prefix values. Let `w` be the value
of the common digits `n_{k-1} ⋯ n_2`; it is less than `F_k` because no two consecutive digits are
`1`. Every point of the first cylinder has prefix value `w` at the orders `k - 1` and `k`, so the
hypothesis gives `F_k ≤ w + r < F_{k+1}`. Every point of the second cylinder has prefix value
`w + F_{k+1}` at the orders `k + 1` and `k + 2`, and these bounds place it in `CST_{k+2}` but not
in `CST_{k+1}`.

For `zeckNIZ_fib_variation_order_succ`, let `s(n)` be the number of terms of the Zeckendorf
representation of `n`. The odometer adds `r` to the digit sequences of natural numbers, so
`Δ^{(r)}(i(v)) = s(v + r) - s(v)`, and the prefix values of `i(v)` show that for `v < F_{ℓ+3}` the
point `i(v)` lies in `NIZ_{ℓ+1}` exactly when `F_{ℓ-1} ≤ v < F_{ℓ+1}`. For `w < F_k` the
Zeckendorf representation of `F_{k+1} + w` is that of `w` with the index `k + 1` put in front, so
`s(F_{k+1} + w) = s(w) + 1`. Write `D_m(u) = s(u + F_m) - s(u)`. For `m ≥ 2`, `D_m(u) = 1` for
`u < F_{m-1}`, `D_m(u) = 0` for `F_{m-1} ≤ u < F_m`, and `D_m(F_m + u) = D_{m-2}(u)` for
`u < F_{m-1}`, because `2 F_m = F_{m+1} + F_{m-2}`. By induction on `m`, exactly `F_m` of the
`u < F_{m+1}` have `D_m(u) = 1` and the others have `D_m(u) = 0`. On `[F_{ℓ-1}, F_{ℓ+1})` the
variation is therefore `0` below `F_ℓ`, which gives `F_{ℓ-2}` zeros. From `F_ℓ` onward it takes
the values of `D_{ℓ-2}` on `[0, F_{ℓ-1})`, which gives `F_{ℓ-3}` more zeros and `F_{ℓ-2}` ones.

## References

* Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
  An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
  (2024), Article 24.3.2, pp. 1–48, Sections 3.1, 4 and 5.1, Lemmas 32–33, and Proposition 41.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Prefix value of a digit sequence.** For $k \in \mathbb{N}$ and a binary sequence
$x = (x_i)_{i \in \mathbb{N}}$, the prefix value of order $k$ is the natural number
$v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$ is the $i$-th Fibonacci number
($F_1 = F_2 = 1$). It is the value of the block $x_{k+1} \cdots x_2$ of the $k$ rightmost digits
of $x$, the name of the cylinder of order $k$ that contains $x$.

In the paper the levels of the two Rokhlin towers of order $k$ are level sets of $v_k$: the
large tower has levels $\{v_k = j - 1\}$ for $1 \le j \le F_{k+1}$, and the small tower has
levels $\{v_k = F_{k+1} + j - 1\}$ for $1 \le j \le F_k$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 3.1 (cylinders of order `k` and the two towers). -/
public def zeckAdicPrefixValue (k : ℕ) (x : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.Icc 2 (k + 1), if x i = true then Nat.fib i else 0

/-- **The sets $\mathrm{CST}_k$.** Fix $r, k \in \mathbb{N}$. For a digit sequence
$x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ let $v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, where $F_i$
is the $i$-th Fibonacci number ($F_1 = F_2 = 1$). The set $\mathrm{CST}_k$ (for the shift $r$)
consists of the digit sequences $x$ such that either $v_k(x) + r < F_{k+1}$, or both
$F_{k+1} \le v_k(x)$ and $v_k(x) + r < F_{k+2}$.

In terms of the Rokhlin towers of order $k$, this is the union of the levels of the large and the
small tower except the $r$ highest levels of each tower.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `CST_k`). -/
public def zeckCST (r k : ℕ) : Set (ℕ → Bool) :=
  {x | zeckAdicPrefixValue k x + r < Nat.fib (k + 1) ∨
    (Nat.fib (k + 1) ≤ zeckAdicPrefixValue k x ∧ zeckAdicPrefixValue k x + r < Nat.fib (k + 2))}

/-- **New-information zone.** Let $F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and
for a digit sequence $x = (x_i)_{i \ge 0}$ with $x_i \in \{0, 1\}$ and $j \in \mathbb{N}$ let
$v_j(x) = \sum_{i=2}^{j+1} x_i F_i$. For $r \in \mathbb{N}$ let $\mathrm{CST}_j$ be the
set of digit sequences $x$ with $v_j(x) + r < F_{j+1}$, or with $F_{j+1} \le v_j(x)$ and
$v_j(x) + r < F_{j+2}$. For $k \in \mathbb{N}$, the new-information zone of order $k$
for $r$ is $\mathrm{NIZ}_k = \mathrm{CST}_k \setminus \mathrm{CST}_{k-1}$, where $k - 1$ is read
as $0$ when $k = 0$ (so $\mathrm{NIZ}_0 = \emptyset$).

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 5.1 (definition of `NIZ_k`). -/
public def zeckNIZ (r k : ℕ) : Set (ℕ → Bool) := zeckCST r k \ zeckCST r (k - 1)

end

namespace zeckNIZ_cylinder_shift

/-- Adding the digit $x_{m+2}$ on top of the prefix of order $m$. -/
private theorem prefixValue_succ (m : ℕ) (x : ℕ → Bool) :
    zeckAdicPrefixValue (m + 1) x =
      zeckAdicPrefixValue m x + if x (m + 2) = true then Nat.fib (m + 2) else 0 :=
  Finset.sum_Icc_succ_top (by omega) _

/-- The prefix value of order $m$ only depends on the digits $x_2, \dots, x_{m+1}$. -/
private theorem prefixValue_congr {m : ℕ} {x x' : ℕ → Bool}
    (h : ∀ i, 2 ≤ i → i ≤ m + 1 → x i = x' i) :
    zeckAdicPrefixValue m x = zeckAdicPrefixValue m x' :=
  Finset.sum_congr rfl fun i hi => by
    rw [Finset.mem_Icc] at hi
    rw [h i hi.1 hi.2]

/-- A Zeckendorf word $x_{m+1} \cdots x_2$ has value less than $F_{m+2}$. -/
private theorem prefixValue_lt {x : ℕ → Bool} (hx : x ∈ zeckAdic) :
    ∀ m, zeckAdicPrefixValue m x < Nat.fib (m + 2)
  | 0 => by simp [zeckAdicPrefixValue]
  | 1 => by
    have e : zeckAdicPrefixValue 1 x = zeckAdicPrefixValue 0 x +
        if x 2 = true then Nat.fib 2 else 0 := prefixValue_succ 0 x
    have e0 : zeckAdicPrefixValue 0 x = 0 := by simp [zeckAdicPrefixValue]
    have hf2 : Nat.fib 2 = 1 := rfl
    have hf3 : Nat.fib (1 + 2) = 2 := rfl
    rw [e, e0, hf2, hf3]
    split <;> omega
  | m + 2 => by
    -- Peel off the top two digits `x (m + 3)` and `x (m + 2)`.
    have e1 : zeckAdicPrefixValue (m + 2) x = zeckAdicPrefixValue (m + 1) x +
        if x (m + 3) = true then Nat.fib (m + 3) else 0 := prefixValue_succ (m + 1) x
    have e0 : zeckAdicPrefixValue (m + 1) x = zeckAdicPrefixValue m x +
        if x (m + 2) = true then Nat.fib (m + 2) else 0 := prefixValue_succ m x
    have h1 : zeckAdicPrefixValue (m + 1) x < Nat.fib (m + 3) := prefixValue_lt hx (m + 1)
    have h0 : zeckAdicPrefixValue m x < Nat.fib (m + 2) := prefixValue_lt hx m
    have hf : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
    cases h3 : x (m + 3)
    · -- The top digit is `0`: the value is the one of order `m + 1`.
      simp only [h3, Bool.false_eq_true, ite_false, add_zero] at e1
      rw [e1, hf]
      omega
    · -- The top digit is `1`, so the digit below it is `0`.
      have h2 : x (m + 2) = false := (hx.2.2 (m + 2)).resolve_right (by simp [h3])
      simp only [h3, ite_true] at e1
      simp only [h2, Bool.false_eq_true, ite_false, add_zero] at e0
      rw [e1, e0, hf]
      omega

end zeckNIZ_cylinder_shift

open zeckNIZ_cylinder_shift in
/-- **Points of $\mathrm{NIZ}_k$ have leading digits $00$.** Let $r \ge 1$ and $k \ge 2$, and
let $\mathrm{NIZ}_k$ be the new-information zone of order $k$ for $r$. Every Zeckendorf-adic
integer $x = (x_i)_{i \ge 2}$ in $\mathrm{NIZ}_k$ has $x_{k+1} = x_k = 0$, that is, the name
$x_{k+1} \cdots x_2$ of its cylinder of order $k$ starts with $00$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 32 (`jis-2024-24.3.2-lem-32`). -/
public theorem zeckNIZ_leading_zeros {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h : x ∈ zeckNIZ r k) :
    x (k + 1) = false ∧ x k = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  change x (j + 3) = false ∧ x (j + 2) = false
  -- Unfold `x ∈ NIZ_{j+2} = CST_{j+2} \ CST_{j+1}`.
  have hN : (zeckAdicPrefixValue (j + 2) x + r < Nat.fib (j + 3) ∨
        (Nat.fib (j + 3) ≤ zeckAdicPrefixValue (j + 2) x ∧
          zeckAdicPrefixValue (j + 2) x + r < Nat.fib (j + 4))) ∧
      ¬(zeckAdicPrefixValue (j + 1) x + r < Nat.fib (j + 2) ∨
        (Nat.fib (j + 2) ≤ zeckAdicPrefixValue (j + 1) x ∧
          zeckAdicPrefixValue (j + 1) x + r < Nat.fib (j + 3))) :=
    h
  -- Peel off the digits `x (j + 3)` and `x (j + 2)` from the prefix values.
  have e2 : zeckAdicPrefixValue (j + 2) x = zeckAdicPrefixValue (j + 1) x +
      if x (j + 3) = true then Nat.fib (j + 3) else 0 := prefixValue_succ (j + 1) x
  have e1 : zeckAdicPrefixValue (j + 1) x = zeckAdicPrefixValue j x +
      if x (j + 2) = true then Nat.fib (j + 2) else 0 := prefixValue_succ j x
  -- Zeckendorf words are bounded by the next Fibonacci number.
  have h0 : zeckAdicPrefixValue j x < Nat.fib (j + 2) := prefixValue_lt hx j
  have h1 : zeckAdicPrefixValue (j + 1) x < Nat.fib (j + 3) := prefixValue_lt hx (j + 1)
  have g4 : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  cases h3 : x (j + 3)
  · cases h2 : x (j + 2)
    · exact ⟨rfl, rfl⟩
    · -- `x_{k+1} = 0` and `x_k = 1`: then `F_k ≤ v_k = v_{k-1} < F_{k+1}`, so `x ∈ CST_{k-1}`.
      simp only [h3, h2, Bool.false_eq_true, ite_true, ite_false, add_zero] at e1 e2
      omega
  · -- `x_{k+1} = 1` forces `x_k = 0`, and then `v_{k-1} + r < F_k`, so `x ∈ CST_{k-1}`.
    have h2 : x (j + 2) = false := (hx.2.2 (j + 2)).resolve_right (by simp [h3])
    simp only [h3, h2, Bool.false_eq_true, ite_true, ite_false, add_zero] at e1 e2
    omega

open zeckNIZ_cylinder_shift in
set_option linter.unusedVariables false in
/-- **Shifting a new-information cylinder by two orders.** Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers: the digit sequences $x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ with
$x_0 = x_1 = 0$ and no two consecutive digits equal to $1$. Let $r \ge 1$, $k \ge 2$ and
$y \in \mathbb{X}$. Suppose that every $x \in \mathbb{X}$ with $x_{k+1} = x_k = 0$ and $x_i = y_i$
for $2 \le i \le k - 1$ lies in the new-information zone $\mathrm{NIZ}_k$ (for the shift $r$).
Then every $x \in \mathbb{X}$ with $x_{k+3} = x_{k+2} = 0$, $x_{k+1} = 1$, $x_k = 0$ and
$x_i = y_i$ for $2 \le i \le k - 1$ lies in $\mathrm{NIZ}_{k+2}$.

In the paper's cylinder notation, where $C_w$ is the set of points of $\mathbb{X}$ whose digits
ending at $x_2$ read $w$, and with $n_i = y_i$: $C_{00 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_k$
implies $C_{0010 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_{k+2}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Lemma 33 (`jis-2024-24.3.2-lem-33`). -/
public theorem zeckNIZ_cylinder_shift {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k)
    {y : ℕ → Bool} (hy : y ∈ zeckAdic)
    (h : zeckAdic ∩ {x | x (k + 1) = false ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r k) :
    zeckAdic ∩ {x | x (k + 3) = false ∧ x (k + 2) = false ∧ x (k + 1) = true ∧ x k = false ∧
      ∀ i, 2 ≤ i → i ≤ k - 1 → x i = y i} ⊆ zeckNIZ r (k + 2) := by
  rintro x ⟨hx, hx3, hx2, hx1, hx0, hxy⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  -- The truncation `x'` of `y` below index `j + 2` is a point of the first cylinder.
  let x' : ℕ → Bool := fun i => if i < j + 2 then y i else false
  have hx' : x' ∈ zeckAdic := by
    obtain ⟨h0, h1, hc⟩ := hy
    refine ⟨by simp [x', h0], by simp [x', h1], fun i => ?_⟩
    by_cases hi : i + 1 < j + 2
    · simpa [x', hi, show i < j + 2 by omega] using hc i
    · exact Or.inr (by simp [x', hi])
  have hmem : x' ∈ zeckAdic ∩ {x | x (j + 2 + 1) = false ∧ x (j + 2) = false ∧
      ∀ i, 2 ≤ i → i ≤ j + 2 - 1 → x i = y i} :=
    ⟨hx', by simp [x'], by simp [x'], fun i _ hi => by simp [x', show i < j + 2 by omega]⟩
  -- Unfold `x' ∈ NIZ_{j+2} = CST_{j+2} \ CST_{j+1}`.
  have hN : (zeckAdicPrefixValue (j + 2) x' + r < Nat.fib (j + 3) ∨
        (Nat.fib (j + 3) ≤ zeckAdicPrefixValue (j + 2) x' ∧
          zeckAdicPrefixValue (j + 2) x' + r < Nat.fib (j + 4))) ∧
      ¬(zeckAdicPrefixValue (j + 1) x' + r < Nat.fib (j + 2) ∨
        (Nat.fib (j + 2) ≤ zeckAdicPrefixValue (j + 1) x' ∧
          zeckAdicPrefixValue (j + 1) x' + r < Nat.fib (j + 3))) :=
    h hmem
  -- Unfold the goal `x ∈ NIZ_{j+4} = CST_{j+4} \ CST_{j+3}`.
  change (zeckAdicPrefixValue (j + 4) x + r < Nat.fib (j + 5) ∨
        (Nat.fib (j + 5) ≤ zeckAdicPrefixValue (j + 4) x ∧
          zeckAdicPrefixValue (j + 4) x + r < Nat.fib (j + 6))) ∧
      ¬(zeckAdicPrefixValue (j + 3) x + r < Nat.fib (j + 4) ∨
        (Nat.fib (j + 4) ≤ zeckAdicPrefixValue (j + 3) x ∧
          zeckAdicPrefixValue (j + 3) x + r < Nat.fib (j + 5)))
  -- Both points have the prefix value `w` at order `j`.
  set w := zeckAdicPrefixValue j x with hw
  have hwlt : w < Nat.fib (j + 2) := prefixValue_lt hx j
  have hx'w : zeckAdicPrefixValue j x' = w :=
    prefixValue_congr fun i hi hi' => by
      simp only [x', show i < j + 2 by omega, ite_true]
      exact (hxy i hi (by omega)).symm
  -- Prefix values of `x'` at the orders `j + 1` and `j + 2`.
  have e1 : zeckAdicPrefixValue (j + 1) x' = w := by
    rw [prefixValue_succ, hx'w]
    simp [x']
  have e2 : zeckAdicPrefixValue (j + 2) x' = w := by
    rw [prefixValue_succ, e1]
    simp [x']
  -- Prefix values of `x` at the orders `j + 1`, ..., `j + 4`.
  have f1 : zeckAdicPrefixValue (j + 1) x = w := by
    rw [prefixValue_succ, ← hw]
    simp [hx0]
  have f2 : zeckAdicPrefixValue (j + 2) x = w + Nat.fib (j + 3) := by
    rw [prefixValue_succ, f1]
    simp [hx1]
  have f3 : zeckAdicPrefixValue (j + 3) x = w + Nat.fib (j + 3) := by
    rw [prefixValue_succ, f2]
    simp [hx2]
  have f4 : zeckAdicPrefixValue (j + 4) x = w + Nat.fib (j + 3) := by
    rw [prefixValue_succ, f3]
    simp [hx3]
  -- The Fibonacci relations used in the final comparison.
  have g4 : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  have g5 : Nat.fib (j + 5) = Nat.fib (j + 3) + Nat.fib (j + 4) := Nat.fib_add_two
  have g23 : Nat.fib (j + 2) ≤ Nat.fib (j + 3) := Nat.fib_mono (by omega)
  rw [e1, e2] at hN
  rw [f3, f4]
  omega

/-! ### The variation of the Zeckendorf sum of digits -/

@[expose] public section

/-- **Truncated variation of the Zeckendorf digit sum.** Let $T$ be the Zeckendorf odometer
$x \mapsto x + 1$ on binary sequences, and write $x + r = T^r(x)$ for its $r$-th iterate. For
$r, k \in \mathbb{N}$ and a binary sequence $x = (x_i)_{i \in \mathbb{N}}$, let
$s_k(x) = x_2 + \dots + x_k$. The truncated variation is the integer
$\Delta_k^{(r)}(x) = s_k(x + r) - s_k(x)$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `s_k` and `Δ_k^{(r)}`). -/
public noncomputable def zeckAdicTruncVariation (r k : ℕ) (x : ℕ → Bool) : ℤ :=
  ∑ i ∈ Finset.Icc 2 k, ((zeckOdometer^[r] x i).toNat : ℤ) -
    ∑ i ∈ Finset.Icc 2 k, ((x i).toNat : ℤ)

/-- **Change of the truncated variation at the next digit.** Let $r \in \mathbb{N}$, $k \ge 1$,
let $x$ be a binary sequence, and let $T$ be the Zeckendorf odometer. Then
$\Delta_{k+1}^{(r)}(x) = \Delta_k^{(r)}(x) + (T^r x)_{k+1} - x_{k+1}$, where each digit is
read as an integer. -/
public theorem zeckAdicTruncVariation_succ (r : ℕ) (x : ℕ → Bool) {k : ℕ} (hk : 1 ≤ k) :
    zeckAdicTruncVariation r (k + 1) x = zeckAdicTruncVariation r k x +
      ((zeckOdometer^[r] x (k + 1)).toNat : ℤ) - ((x (k + 1)).toNat : ℤ) := by
  simp only [zeckAdicTruncVariation, Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1)]
  omega

/-- **The truncated variation vanishes for zero steps.** Let $T$ be the Zeckendorf odometer and,
for a binary sequence $x$, let $s_k(x) = x_2 + \dots + x_k$ and
$\Delta_k^{(r)}(x) = s_k(T^r(x)) - s_k(x)$. Then $\Delta_k^{(0)}(x) = 0$ for every
$k \in \mathbb{N}$ and every binary sequence $x$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ_k^{(r)}`). -/
public theorem zeckAdicTruncVariation_zero (k : ℕ) (x : ℕ → Bool) :
    zeckAdicTruncVariation 0 k x = 0 := by
  simp [zeckAdicTruncVariation]

/-- **The variation of the Zeckendorf digit sum.** For $r \in \mathbb{N}$ and a digit sequence
$x : \mathbb{N} \to \{0, 1\}$, let $\Delta_k^{(r)}(x)$ be the truncated variation of order $k$. If
the integer sequence $(\Delta_k^{(r)}(x))_k$ is eventually constant, the variation
$\Delta^{(r)}(x) = \lim_{k \to \infty} \Delta_k^{(r)}(x)$ is its eventual value; otherwise
$\Delta^{(r)}(x) = 0$.

The value $0$ is a junk value. The paper shows that the Zeckendorf-adic integers at which the
limit does not exist form a finite set.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (definition of `Δ^{(r)}` on `𝕏`). -/
public noncomputable def zeckAdicVariation (r : ℕ) (x : ℕ → Bool) : ℤ :=
  open Classical in
  if h : ∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d then h.choose else 0

/-- **The variation is the eventual value of the truncated variations.** Let $r \in \mathbb{N}$,
let $x$ be a binary sequence and let $d \in \mathbb{Z}$. If the truncated variation
$\Delta_k^{(r)}(x)$ equals $d$ for all sufficiently large $k$, then the variation
$\Delta^{(r)}(x)$ equals $d$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ^{(r)}`). -/
public theorem zeckAdicVariation_eq_of_eventually {r : ℕ} {x : ℕ → Bool} {d : ℤ}
    (h : ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d) :
    zeckAdicVariation r x = d := by
  have hex : ∃ d, ∀ᶠ k in Filter.atTop, zeckAdicTruncVariation r k x = d := ⟨d, h⟩
  unfold zeckAdicVariation
  split
  · rename_i hex'
    obtain ⟨k, hk1, hk2⟩ := (hex'.choose_spec.and h).exists
    rw [← hk1, hk2]
  · exact absurd hex ‹_›

/-- **The variation for $r = 0$ vanishes.** For every digit sequence $x : \mathbb{N} \to \{0, 1\}$,
not only for Zeckendorf-adic integers, the variation satisfies $\Delta^{(0)}(x) = 0$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 4 (characteristic lemma for `Δ^{(r)}`). -/
public theorem zeckAdicVariation_zero (x : ℕ → Bool) : zeckAdicVariation 0 x = 0 :=
  zeckAdicVariation_eq_of_eventually (Filter.Eventually.of_forall fun k =>
    zeckAdicTruncVariation_zero k x)

end

namespace zeckNIZ_fib_variation_order_succ

open Nat (fib zeckendorf)

/-- Adding $F_{k+1}$ to a number $w < F_k$ puts the index $k + 1$ in front of its Zeckendorf
representation. -/
private theorem zeckendorf_fib_add {k w : ℕ} (hw : w < fib k) :
    zeckendorf (fib (k + 1) + w) = (k + 1) :: zeckendorf w := by
  have hpos : 0 < fib (k + 1) + w := by
    have : 0 < fib (k + 1) := Nat.fib_pos.2 (by omega)
    omega
  have h2 : fib (k + 2) = fib k + fib (k + 1) := Nat.fib_add_two
  have hg : Nat.greatestFib (fib (k + 1) + w) = k + 1 := by
    refine le_antisymm (Nat.lt_add_one_iff.1 (Nat.greatestFib_lt.2 ?_))
      (Nat.le_greatestFib.2 (by omega))
    change fib (k + 1) + w < fib (k + 2)
    omega
  rw [Nat.zeckendorf_of_pos hpos, hg, Nat.add_sub_cancel_left]

/-- The Zeckendorf sum of digits of $F_{k+1} + w$ for $w < F_k$. -/
private theorem length_fib_add {k w : ℕ} (hw : w < fib k) :
    (zeckendorf (fib (k + 1) + w)).length = (zeckendorf w).length + 1 := by
  rw [zeckendorf_fib_add hw, List.length_cons]

/-- Every term $F_i$ of the Zeckendorf representation of $n$ is at most $n$. -/
private theorem fib_le_of_mem {n i : ℕ} (hi : i ∈ zeckendorf n) : fib i ≤ n := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fib) hi)
  rwa [Nat.sum_zeckendorf_fib] at this

/-- The indices of a Zeckendorf representation are at least $2$, and each is at least $2$ more
than the next one. -/
private theorem pairwise_zeckendorf (n : ℕ) :
    (zeckendorf n).Pairwise (fun a b => b + 2 ≤ a) ∧ ∀ i ∈ zeckendorf n, 2 ≤ i := by
  have : Trans (fun a b : ℕ => b + 2 ≤ a) (fun a b : ℕ => b + 2 ≤ a)
      (fun a b : ℕ => b + 2 ≤ a) := ⟨fun h₁ h₂ => by omega⟩
  have h := (List.isChain_iff_pairwise (R := fun a b : ℕ => b + 2 ≤ a)).1
    (Nat.isZeckendorfRep_zeckendorf n)
  rw [List.pairwise_append] at h
  exact ⟨h.1, fun i hi => by simpa using h.2.2 i hi 0 (List.mem_singleton_self 0)⟩

/-- The prefix value of order $k$ of the digit sequence of $n < F_{k+2}$ is $n$. -/
private theorem prefixValue_ofNat {n k : ℕ} (hn : n < fib (k + 2)) :
    zeckAdicPrefixValue k (zeckAdicOfNat n) = n := by
  classical
  obtain ⟨hp, h2⟩ := pairwise_zeckendorf n
  have hnd : (zeckendorf n).Nodup := hp.imp fun h => by omega
  have hsub : (zeckendorf n).toFinset ⊆ Finset.Icc 2 (k + 1) := fun i hi => by
    rw [List.mem_toFinset] at hi
    have hlt : i < k + 2 := lt_of_not_ge fun h =>
      (hn.trans_le ((Nat.fib_mono h).trans (fib_le_of_mem hi))).false
    exact Finset.mem_Icc.2 ⟨h2 i hi, by omega⟩
  have hc : ∀ i ∈ Finset.Icc 2 (k + 1), (if zeckAdicOfNat n i = true then fib i else 0) =
      if i ∈ (zeckendorf n).toFinset then fib i else 0 := fun i _ => by
    simp [zeckAdicOfNat]
  rw [zeckAdicPrefixValue, Finset.sum_congr rfl hc, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 hsub, List.sum_toFinset _ hnd, Nat.sum_zeckendorf_fib]

/-- Among the indices $2, \dots, k$, the digit sequence of $n$ has as many digits $1$ as the
Zeckendorf representation of $n$ has terms, once $k > n$. -/
private theorem sum_toNat_ofNat {n k : ℕ} (hk : n + 1 ≤ k) :
    ∑ i ∈ Finset.Icc 2 k, ((zeckAdicOfNat n i).toNat : ℤ) = (zeckendorf n).length := by
  classical
  obtain ⟨hp, h2⟩ := pairwise_zeckendorf n
  have hnd : (zeckendorf n).Nodup := hp.imp fun h => by omega
  have hsub : (zeckendorf n).toFinset ⊆ Finset.Icc 2 k := fun i hi => by
    rw [List.mem_toFinset] at hi
    have := Nat.le_fib_add_one i
    have := fib_le_of_mem hi
    exact Finset.mem_Icc.2 ⟨h2 i hi, by omega⟩
  have hc : ∀ i ∈ Finset.Icc 2 k, ((zeckAdicOfNat n i).toNat : ℤ) =
      if i ∈ (zeckendorf n).toFinset then 1 else 0 := fun i _ => by
    by_cases h : i ∈ zeckendorf n <;> simp [zeckAdicOfNat, h]
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    Finset.sum_const, List.toFinset_card_of_nodup hnd, nsmul_eq_mul, mul_one]

/-- On the digit sequence of $v$, the variation $\Delta^{(r)}$ is the variation
$s(v + r) - s(v)$ of the Zeckendorf sum of digits. -/
private theorem variation_ofNat (r v : ℕ) :
    zeckAdicVariation r (zeckAdicOfNat v) =
      ((zeckendorf (v + r)).length : ℤ) - (zeckendorf v).length := by
  apply zeckAdicVariation_eq_of_eventually
  rw [Filter.eventually_atTop]
  refine ⟨v + r + 1, fun k hk => ?_⟩
  rw [zeckAdicTruncVariation, zeckOdometer_iterate_zeckAdicOfNat, sum_toNat_ofNat hk,
    sum_toNat_ofNat (by omega)]

/-- For $v < F_{n+5}$, the digit sequence of $v$ lies in $\mathrm{NIZ}_{n+3}$ for the shift
$F_{n+2}$ exactly when $F_{n+1} \le v < F_{n+3}$. -/
private theorem mem_zeckNIZ_iff {n v : ℕ} (hv : v < fib (n + 5)) :
    zeckAdicOfNat v ∈ zeckNIZ (fib (n + 2)) (n + 3) ↔ fib (n + 1) ≤ v ∧ v < fib (n + 3) := by
  set x := zeckAdicOfNat v with hx
  have f3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := Nat.fib_add_two
  have f4 : fib (n + 4) = fib (n + 2) + fib (n + 3) := Nat.fib_add_two
  have f5 : fib (n + 5) = fib (n + 3) + fib (n + 4) := Nat.fib_add_two
  have e3 : zeckAdicPrefixValue (n + 3) x = v := prefixValue_ofNat hv
  have e2 : zeckAdicPrefixValue (n + 3) x = zeckAdicPrefixValue (n + 2) x +
      if x (n + 4) = true then fib (n + 4) else 0 :=
    zeckNIZ_cylinder_shift.prefixValue_succ (n + 2) x
  -- A number in `[F_{n+4}, F_{n+5})` has the digit `1` at index `n + 4`.
  have hdig : fib (n + 4) ≤ v → x (n + 4) = true := fun h => by
    have hz : zeckendorf (fib (n + 4) + (v - fib (n + 4))) =
        (n + 4) :: zeckendorf (v - fib (n + 4)) :=
      zeckendorf_fib_add (k := n + 3) (by omega)
    rw [Nat.add_sub_cancel' h] at hz
    simp [hx, zeckAdicOfNat, hz]
  change (zeckAdicPrefixValue (n + 3) x + fib (n + 2) < fib (n + 4) ∨
        (fib (n + 4) ≤ zeckAdicPrefixValue (n + 3) x ∧
          zeckAdicPrefixValue (n + 3) x + fib (n + 2) < fib (n + 5))) ∧
      ¬(zeckAdicPrefixValue (n + 2) x + fib (n + 2) < fib (n + 3) ∨
        (fib (n + 3) ≤ zeckAdicPrefixValue (n + 2) x ∧
          zeckAdicPrefixValue (n + 2) x + fib (n + 2) < fib (n + 4))) ↔ _
  rw [e3] at e2 ⊢
  cases h4 : x (n + 4)
  · -- The digit at index `n + 4` is `0`, so `v < F_{n+4}` and `v_{n+2} = v`.
    simp only [h4, Bool.false_eq_true, ite_false, add_zero] at e2
    have hv4 : v < fib (n + 4) := lt_of_not_ge fun h => by simp [hdig h] at h4
    rw [← e2]
    omega
  · -- The digit at index `n + 4` is `1`, so `v_{n+2} = v - F_{n+4}`.
    simp only [h4, ite_true] at e2
    omega

/-- The number of $u < N$ with $s(a + u + F_m) - s(a + u) = c$, where $s(n)$ is the number of
terms of the Zeckendorf representation of $n$. -/
private def cnt (m a N : ℕ) (c : ℤ) : ℕ :=
  ((Finset.range N).filter fun u =>
    ((zeckendorf (a + u + fib m)).length : ℤ) - (zeckendorf (a + u)).length = c).card

/-- Splitting the range of `cnt` in two. -/
private theorem cnt_add (m a N₁ N₂ : ℕ) (c : ℤ) :
    cnt m a (N₁ + N₂) c = cnt m a N₁ c + cnt m (a + N₁) N₂ c := by
  simp only [cnt, Finset.card_filter, Finset.sum_range_add, Nat.add_assoc]

/-- `cnt` only depends on the values of the variations it counts. -/
private theorem cnt_congr {m a m' a' N : ℕ} {c : ℤ}
    (h : ∀ u < N, ((zeckendorf (a + u + fib m)).length : ℤ) - (zeckendorf (a + u)).length =
      ((zeckendorf (a' + u + fib m')).length : ℤ) - (zeckendorf (a' + u)).length) :
    cnt m a N c = cnt m' a' N c := by
  unfold cnt
  congr 1
  exact Finset.filter_congr fun u hu => by rw [h u (Finset.mem_range.1 hu)]

/-- `cnt` of a constant variation. -/
private theorem cnt_const {m a N : ℕ} {d c : ℤ}
    (h : ∀ u < N, ((zeckendorf (a + u + fib m)).length : ℤ) - (zeckendorf (a + u)).length = d) :
    cnt m a N c = if d = c then N else 0 := by
  unfold cnt
  split_ifs with hdc
  · rw [Finset.filter_true_of_mem fun u hu => (h u (Finset.mem_range.1 hu)).trans hdc,
      Finset.card_range]
  · rw [Finset.filter_false_of_mem fun u hu => by rw [h u (Finset.mem_range.1 hu)]; exact hdc,
      Finset.card_empty]

/-- $s(u + F_{n+2}) - s(u) = 1$ for $u < F_{n+1}$. -/
private theorem diff_low {n u : ℕ} (hu : u < fib (n + 1)) :
    ((zeckendorf (0 + u + fib (n + 2))).length : ℤ) - (zeckendorf (0 + u)).length = 1 := by
  have h : (zeckendorf (fib (n + 2) + u)).length = (zeckendorf u).length + 1 :=
    length_fib_add (k := n + 1) hu
  rw [show 0 + u + fib (n + 2) = fib (n + 2) + u by omega, Nat.zero_add, h]
  omega

/-- $s(F_{n+1} + u + F_{n+2}) - s(F_{n+1} + u) = 0$ for $u < F_n$. -/
private theorem diff_mid {n u : ℕ} (hu : u < fib n) :
    ((zeckendorf (fib (n + 1) + u + fib (n + 2))).length : ℤ) -
      (zeckendorf (fib (n + 1) + u)).length = 0 := by
  have f3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := Nat.fib_add_two
  have hmono : fib n ≤ fib (n + 2) := Nat.fib_mono (by omega)
  have h1 : (zeckendorf (fib (n + 3) + u)).length = (zeckendorf u).length + 1 :=
    length_fib_add (k := n + 2) (by omega)
  have h2 : (zeckendorf (fib (n + 1) + u)).length = (zeckendorf u).length + 1 :=
    length_fib_add hu
  rw [show fib (n + 1) + u + fib (n + 2) = fib (n + 3) + u by omega, h1, h2, sub_self]

/-- $s(F_{n+2} + u + F_{n+2}) - s(F_{n+2} + u) = s(u + F_n) - s(u)$ for $u < F_{n+1}$. -/
private theorem diff_high {n u : ℕ} (hu : u < fib (n + 1)) :
    ((zeckendorf (fib (n + 2) + u + fib (n + 2))).length : ℤ) -
        (zeckendorf (fib (n + 2) + u)).length =
      ((zeckendorf (0 + u + fib n)).length : ℤ) - (zeckendorf (0 + u)).length := by
  have f2 : fib (n + 2) = fib n + fib (n + 1) := Nat.fib_add_two
  have f3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := Nat.fib_add_two
  have h1 : (zeckendorf (fib (n + 3) + (fib n + u))).length =
      (zeckendorf (fib n + u)).length + 1 := length_fib_add (k := n + 2) (by omega)
  have h2 : (zeckendorf (fib (n + 2) + u)).length = (zeckendorf u).length + 1 :=
    length_fib_add (k := n + 1) hu
  rw [show fib (n + 2) + u + fib (n + 2) = fib (n + 3) + (fib n + u) by omega, h1, h2,
    show 0 + u + fib n = fib n + u by omega, Nat.zero_add]
  omega

/-- Among the $u < F_{n+1}$, exactly $F_n$ satisfy $s(u + F_n) - s(u) = 1$, and the other
$F_{n+1} - F_n$ satisfy $s(u + F_n) - s(u) = 0$. -/
private theorem cnt_full : ∀ n : ℕ,
    cnt n 0 (fib (n + 1)) 1 = fib n ∧ cnt n 0 (fib (n + 1)) 0 + fib n = fib (n + 1)
  | 0 => by
    -- `F_0 = 0`, so every variation counted is `0`.
    have h : ∀ c : ℤ, cnt 0 0 (fib (0 + 1)) c = if (0 : ℤ) = c then fib (0 + 1) else 0 :=
      fun c => cnt_const fun u _ => by simp
    rw [h, h]
    simp
  | 1 => by
    -- The only `u < F_2 = 1` is `u = 0`, and `s(1) - s(0) = 1`.
    have h1 : (zeckendorf (fib (1 + 1) + 0)).length = (zeckendorf 0).length + 1 :=
      length_fib_add (by simp)
    have h : ∀ c : ℤ, cnt 1 0 (fib (1 + 1)) c = if (1 : ℤ) = c then fib (1 + 1) else 0 :=
      fun c => cnt_const fun u hu => by
        have hu0 : u = 0 := by simpa using hu
        subst hu0
        rw [show 0 + 0 + fib 1 = fib (1 + 1) + 0 from rfl, h1]
        simp
    rw [h, h]
    simp
  | n + 2 => by
    obtain ⟨ih1, ih0⟩ := cnt_full n
    have f2 : fib (n + 2) = fib n + fib (n + 1) := Nat.fib_add_two
    have f3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := Nat.fib_add_two
    -- Split `[0, F_{n+3})` into `[0, F_{n+1})`, `[F_{n+1}, F_{n+2})` and `[F_{n+2}, F_{n+3})`.
    have hsplit : ∀ c : ℤ, cnt (n + 2) 0 (fib (n + 3)) c =
        (if (1 : ℤ) = c then fib (n + 1) else 0) + (if (0 : ℤ) = c then fib n else 0) +
          cnt n 0 (fib (n + 1)) c := fun c => by
      rw [show fib (n + 3) = fib (n + 1) + (fib n + fib (n + 1)) by omega, cnt_add, cnt_add,
        cnt_const fun u hu => diff_low hu, Nat.zero_add,
        cnt_const (d := 0) fun u hu => diff_mid hu, ← Nat.add_assoc]
      congr 1
      exact cnt_congr fun u hu => by
        rw [show fib (n + 1) + fib n = fib (n + 2) by omega]
        exact diff_high hu
    change cnt (n + 2) 0 (fib (n + 3)) 1 = fib (n + 2) ∧
      cnt (n + 2) 0 (fib (n + 3)) 0 + fib (n + 2) = fib (n + 3)
    rw [hsplit, hsplit, ih1]
    simp only [ite_true, ite_false, show ((1 : ℤ) = 0) = False by decide,
      show ((0 : ℤ) = 1) = False by decide]
    omega

end zeckNIZ_fib_variation_order_succ

open zeckNIZ_fib_variation_order_succ in
/-- **Values of the variation by $F_\ell$ on $\mathrm{NIZ}_{\ell+1}$.** Let $\ell \ge 3$, let
$F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and let $\Delta^{(F_\ell)}$ be the
variation of the Zeckendorf sum of digits under adding $F_\ell$ on the Zeckendorf-adic integers.
For $v \in \mathbb{N}$ write $i(v)$ for the Zeckendorf-adic integer whose digits are the
Zeckendorf digits of $v$. Among the $v < F_{\ell+3}$ with $i(v)$ in the new-information zone
$\mathrm{NIZ}_{\ell+1}$ of order $\ell + 1$ for $r = F_\ell$, exactly $F_{\ell-1}$ satisfy
$\Delta^{(F_\ell)}(i(v)) = 0$ and exactly $F_{\ell-2}$ satisfy $\Delta^{(F_\ell)}(i(v)) = 1$.

Each such $v$ stands for the level (cylinder of order $\ell + 1$) whose name is its digits.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Proposition 41 (`jis-2024-24.3.2-prop-41`). -/
public theorem zeckNIZ_fib_variation_order_succ {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 0}.ncard = Nat.fib (ℓ - 1) ∧
      {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 1}.ncard = Nat.fib (ℓ - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 2 := ⟨ℓ - 2, by omega⟩
  have f2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have f3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  -- The levels of `NIZ_{ℓ+1}` below `F_{ℓ+3}` are the `v = F_{ℓ-1} + u` with `u < F_ℓ`, and
  -- there `Δ^{(F_ℓ)}(i(v)) = s(v + F_ℓ) - s(v)`.
  have key : ∀ c : ℤ, {v | v < Nat.fib (n + 2 + 3) ∧
      zeckAdicOfNat v ∈ zeckNIZ (Nat.fib (n + 2)) (n + 2 + 1) ∧
      zeckAdicVariation (Nat.fib (n + 2)) (zeckAdicOfNat v) = c}.ncard =
      cnt (n + 2) (Nat.fib (n + 1)) (Nat.fib (n + 2)) c := by
    intro c
    have h35 : Nat.fib (n + 3) ≤ Nat.fib (n + 5) := Nat.fib_mono (by omega)
    have hset : {v | v < Nat.fib (n + 2 + 3) ∧
        zeckAdicOfNat v ∈ zeckNIZ (Nat.fib (n + 2)) (n + 2 + 1) ∧
        zeckAdicVariation (Nat.fib (n + 2)) (zeckAdicOfNat v) = c} =
        ↑(((Finset.range (Nat.fib (n + 2))).filter fun u =>
          ((Nat.zeckendorf (Nat.fib (n + 1) + u + Nat.fib (n + 2))).length : ℤ) -
            (Nat.zeckendorf (Nat.fib (n + 1) + u)).length = c).image (Nat.fib (n + 1) + ·)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hv, hniz, hc⟩
        obtain ⟨h1, h2⟩ := (mem_zeckNIZ_iff (n := n) hv).1 hniz
        refine ⟨v - Nat.fib (n + 1), ⟨by omega, ?_⟩, by omega⟩
        rw [Nat.add_sub_cancel' h1, ← hc, variation_ofNat]
      · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
        have hlt : Nat.fib (n + 1) + u < Nat.fib (n + 3) := by omega
        refine ⟨show Nat.fib (n + 1) + u < Nat.fib (n + 5) by omega,
          (mem_zeckNIZ_iff (by omega)).2 ⟨by omega, hlt⟩, ?_⟩
        rw [variation_ofNat, hc]
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ (add_right_injective _)]
    rfl
  -- Split `[F_{ℓ-1}, F_{ℓ+1})` at `F_ℓ`: the variation is `0` below `F_ℓ`, and above it is the
  -- variation by `F_{ℓ-2}` of `v - F_ℓ`.
  have htop : ∀ c : ℤ, cnt (n + 2) (Nat.fib (n + 1)) (Nat.fib (n + 2)) c =
      (if (0 : ℤ) = c then Nat.fib n else 0) + cnt n 0 (Nat.fib (n + 1)) c := by
    intro c
    rw [f2, cnt_add, cnt_const (d := 0) fun u hu => diff_mid hu]
    congr 1
    exact cnt_congr fun u hu => by
      rw [show Nat.fib (n + 1) + Nat.fib n = Nat.fib (n + 2) by omega]
      exact diff_high hu
  obtain ⟨h1, h0⟩ := cnt_full n
  rw [key, key, htop, htop, h1, show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  simp only [ite_true, ite_false, show ((0 : ℤ) = 1) = False by decide]
  omega

end MetaMathlibExt
