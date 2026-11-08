/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP

/-!
# Combinations without specified separations

Statements from Michael A. Allen, *Connections Between Combinations Without Specified
Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of
Integer Sequences 28 (2025), Article 25.3.7 (arXiv:2409.00624v4).

`restrictedCombinationCount Q n k` is the paper's `S^Q_{n,k}`: the number of `k`-subsets of
`{1, …, n}` in which no two elements differ by an element of `Q`; `restrictedCombinationTotal Q n`
is `S^Q_n`. Permutations of `ℕ_n = {1, …, n}` are modelled as permutations of `Fin n`
(0-based positions; only differences `π(i) - i` and excedances matter, so the shift is
harmless). Most bijection statements are recorded as equalities of cardinalities, which is
equivalent for finite sets. Lemma 12 (`fenceTiling_strongPerm_bijection`) states the explicit
correspondence instead: a compatibility relation between tilings and permutations that is
functional in both directions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The restricted combinations of the paper: the `k`-subsets of `{1, …, n}` such that no two
elements differ by an element of `Q`. Differences are taken between distinct elements, so an
element `0 ∈ Q` has no effect, as in the paper.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinations (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powersetCard k).filter fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q

/-- The paper's `S^Q_{n,k}`: the number of `k`-subsets of `{1, …, n}` with no two elements
differing by an element of `Q`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedCombinations Q n k).card

/-- The paper's `S^Q_n`: the number of subsets of `{1, …, n}` with no two elements differing by
an element of `Q` (a `k`-subset has `k ≤ n`).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationTotal (Q : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), restrictedCombinationCount Q n k

/-- With no disallowed differences, `S^{}_{n,k} = (n choose k)`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedCombinationCount_empty (n k : ℕ) :
    restrictedCombinationCount ∅ n k = n.choose k := by
  unfold restrictedCombinationCount restrictedCombinations
  rw [Finset.filter_true_of_mem (fun s _ => by simp), Finset.card_powersetCard, Nat.card_Icc,
    Nat.add_sub_cancel]

/-- Characteristic value `S^{1}_4 = F_6 = 8`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1 (`S^{1}_n = F_{n+2}`). -/
public theorem restrictedCombinationTotal_singleton_one_four :
    restrictedCombinationTotal {1} 4 = 8 := by
  decide

/-- Theorem 8: for `Q = {1, q}`, the `k`-subsets of `{1, …, n}` with disallowed
differences `Q` are equinumerous with the permutations `π` of `ℕ_{n+1}` with
`π(i) - i ∈ {-1, 0, 1}` (products of exchanges of consecutive items) having `k` exchanged
pairs (excedances), such that every window of `q` consecutive values `π(i), …, π(i+q-1)`,
`i = 1, …, n+2-q`, has `max - min ≤ q`. The class `π(i) - i ∈ {-1, 0, 1}` is the one named
in the paper's Section 3.1; without it the count is wrong (`q = 2`, `n = 2`: all `6`
permutations of `ℕ_3` meet the window condition, while `S^{1,2}_2 = 3`). The paper takes
`q ≥ 2`; the statement is kept for every `q : ℕ` (for `q ≤ 1` it reduces to the `Q = {1}`
case and still holds).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 8. -/
public theorem_wanted restrictedCombinationCount_one_q_eq_card_windowedAdjacentSwapPerms
    (q n k : ℕ) :
    restrictedCombinationCount {1, q} n k =
      Nat.card {π : Equiv.Perm (Fin (n + 1)) //
        (∀ i : Fin (n + 1), (π i : ℕ) ≤ i + 1 ∧ (i : ℕ) ≤ π i + 1) ∧
        (∀ i₀ < n + 2 - q, ∀ i j : Fin (n + 1), i₀ ≤ (i : ℕ) → (i : ℕ) < i₀ + q →
          i₀ ≤ (j : ℕ) → (j : ℕ) < i₀ + q → (π i : ℕ) ≤ π j + q) ∧
        excedanceCount (n + 1) π = k}

/-- Proposition 9: `∑ S^{1,4}_n x^n = (1+x+x^2+x^3+2x^4+x^6)/(1-x-x^3+x^4-2x^5+x^6-x^7)`,
stated with the denominator cleared in `ℤ⟦X⟧`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 9. -/
public theorem_wanted restrictedCombinationTotal_one_four_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 4} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 +
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        PowerSeries.X ^ 6

/-- Proposition 10: `∑ S^{1,5}_n x^n = (1+2x+2x^2+2x^3+2x^4+4x^5+3x^6+2x^7+x^8+x^9) /
(1-x^2-x^3-x^4+x^5-x^6-x^7-x^8-x^10)`, stated with the denominator cleared in `ℤ⟦X⟧`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 10. -/
public theorem_wanted restrictedCombinationTotal_one_five_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 5} n : ℤ)) *
        (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 -
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7 - PowerSeries.X ^ 8 - PowerSeries.X ^ 10) =
      1 + 2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6 +
        2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 + PowerSeries.X ^ 9

/-- Proposition 11: the generating function of `S^{1,6}_n` is the printed degree-17 over
degree-18 rational function, stated with the denominator cleared in `ℤ⟦X⟧`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 11. -/
public theorem_wanted restrictedCombinationTotal_one_six_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 6} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 -
          4 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 10 +
          2 * PowerSeries.X ^ 11 - 4 * PowerSeries.X ^ 12 + 3 * PowerSeries.X ^ 13 -
          PowerSeries.X ^ 14 + 2 * PowerSeries.X ^ 16 - PowerSeries.X ^ 17 +
          PowerSeries.X ^ 18) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        2 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 + 3 * PowerSeries.X ^ 8 +
        2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10 + PowerSeries.X ^ 11 -
        4 * PowerSeries.X ^ 12 - PowerSeries.X ^ 13 - 2 * PowerSeries.X ^ 14 -
        2 * PowerSeries.X ^ 15 - PowerSeries.X ^ 17

/-- Theorem 13: for `j, m ≥ 1` the `k`-subsets of `{1, …, n}` with disallowed differences
`{m, 2m, …, jm}` are equinumerous with the permutations `π` of `ℕ_{n+jm}` with
`π(i) - i ∈ {-m, 0, jm}` for all `i` that have `k` excedances.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 13. -/
public theorem_wanted restrictedCombinationCount_multiples_eq_card_strongPerms
    (m j n k : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) :
    restrictedCombinationCount ((Finset.Icc 1 j).image fun u => u * m) n k =
      Nat.card {π : Equiv.Perm (Fin (n + j * m)) //
        (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
        excedanceCount (n + j * m) π = k}

/-- The paper's `(1,t)`-bonacci polynomial `f^{(t)}_n(x)` with `t = s + 1`:
`f^{(t)}_n(x) = f^{(t)}_{n-1}(x) + x f^{(t)}_{n-t}(x) + δ_{n,0}` and `f^{(t)}_{n<0}(x) = 0`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public noncomputable def oneTBonacciPolynomial (s : ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 =>
    oneTBonacciPolynomial s n +
      Polynomial.X * (if s ≤ n then oneTBonacciPolynomial s (n - s) else 0)
termination_by n => n
decreasing_by all_goals omega

/-- Initial value `f^{(t)}_0(x) = 1`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_zero (s : ℕ) : oneTBonacciPolynomial s 0 = 1 := by
  rw [oneTBonacciPolynomial]

/-- The recurrence `f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x) + x f^{(s+1)}_{n-s}(x)` for `s ≤ n`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_le (s n : ℕ) (h : s ≤ n) :
    oneTBonacciPolynomial s (n + 1) =
      oneTBonacciPolynomial s n + Polynomial.X * oneTBonacciPolynomial s (n - s) := by
  rw [oneTBonacciPolynomial]
  simp [h]

/-- Below the recurrence range, `f^{(s+1)}_{n+1}(x) = f^{(s+1)}_n(x)` for `n < s`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 3.2. -/
public theorem oneTBonacciPolynomial_succ_of_lt (s n : ℕ) (h : n < s) :
    oneTBonacciPolynomial s (n + 1) = oneTBonacciPolynomial s n := by
  rw [oneTBonacciPolynomial]
  simp [show ¬ s ≤ n by omega]

/-- Corollary 14, counting part: for `j ≥ 1`, `i ≥ 0` and `0 ≤ r < m` (which gives the
paper's `m ≥ 1`), `P^{\{-m,0,jm\}}_{im+r} = (f^{(j+1)}_i)^{m-r} (f^{(j+1)}_{i+1})^r`.
The `(1,t)`-bonacci numbers `f^{(t)}_n` (`f^{(t)}_n = f^{(t)}_{n-1} + f^{(t)}_{n-t} + δ_{n,0}`) are the existing
Fibonacci `p`-numbers shifted: `f^{(j+1)}_n = fibonacciP j (n + 1)`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem_wanted card_strongPerms_multiples_eq_fibonacciP
    (m j i r : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)} =
      fibonacciP j (i + 1) ^ (m - r) * fibonacciP j (i + 2) ^ r

/-- Corollary 14, excedance part: for `j ≥ 1`, `i, k ≥ 0` and `0 ≤ r < m`, the number of
permutations counted by `P^{\{-m,0,jm\}}_{im+r}` with `k` excedances is
`[x^k] (f^{(j+1)}_i(x))^{m-r} (f^{(j+1)}_{i+1}(x))^r`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 14. -/
public theorem_wanted card_strongPerms_multiples_excedance_eq_coeff
    (m j i r k : ℕ) (hj : 1 ≤ j) (hr : r < m) :
    Nat.card {π : Equiv.Perm (Fin (i * m + r)) //
        (∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
        excedanceCount (i * m + r) π = k} =
      ((oneTBonacciPolynomial j i) ^ (m - r) * (oneTBonacciPolynomial j (i + 1)) ^ r).coeff k

/-- Theorem 19: if `Q = {1, …, q} \ {p}` with `p < q < 2p`, then `S^Q_n` is the number of
compositions of `n + q` into parts `1` and `q + 1 + jp`, `j = 0, 1, 2, …`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 19. -/
public theorem_wanted restrictedCombinationTotal_Icc_erase_eq_card_compositions
    (p q n : ℕ) (hpq : p < q) (hqp : q < 2 * p) :
    restrictedCombinationTotal ((Finset.Icc 1 q).erase p) n =
      Nat.card {c : Composition (n + q) //
        ∀ b ∈ c.blocks, b = 1 ∨ (q + 1 ≤ b ∧ p ∣ b - (q + 1))}

/-- A finite set `Q` of positive integers is well based (Kitaev; Valyuzhenich) if every
element `x ∈ Q` has, for each splitting `x = a + (x - a)` with `0 < a < x`, a part in `Q`.
For nonempty `Q` this forces `1 ∈ Q`; the empty set also counts as well based, as in the
paper's equivalent formulation.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public def IsWellBased (Q : Finset ℕ) : Prop :=
  ∀ x ∈ Q, ∀ a, 0 < a → a < x → a ∈ Q ∨ x - a ∈ Q

/-- `{1, …, q}` is well based.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem isWellBased_Icc (q : ℕ) : IsWellBased (Finset.Icc 1 q) := by
  intro x hx a ha hax
  left
  simp only [Finset.mem_Icc] at hx ⊢
  omega

/-- `{1, 3, 4}` is not well based (`4 = 2 + 2`).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem not_isWellBased_one_three_four : ¬ IsWellBased {1, 3, 4} := by
  intro h
  have := h 4 (by simp) 2 (by norm_num) (by norm_num)
  simp at this

/-- The set `Q` the paper builds from a length-`l` binary subword `ω` (read as the natural
number `ω < 2^l`): `j ∈ Q` iff `⌊ω / 2^j⌋ ≠ ω mod 2^{l-j}` for `j = 1, …, l - 1`, i.e. the
leftmost and rightmost `l - j` bits of `ω` differ.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 21. -/
public def subwordShiftSet (ω l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (l - 1)).filter fun j => ω / 2 ^ j ≠ ω % 2 ^ (l - j)

/-- The subword `1010` gives `Q = {1, 3}`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1 (OEIS list after Theorem 21). -/
public theorem subwordShiftSet_1010 : subwordShiftSet 0b1010 4 = {1, 3} := by
  decide

/-- Theorem 22, well-based part: for every length-`l` binary subword `ω`, the set `Q` built
from `ω` as in Theorem 21 is well based. The theorem's additional claim that no
integer linear combination of the elements `p_i` of `{1, …, q} \ Q` lies in `Q` is omitted:
it is false (`ω = 010100101`, `l = 9`: `Q = {1, 2, 3, 4, 6, 8}`, `q = 8 = l - 1`,
`p_1 = 5`, `p_2 = 7`, and `p_2 - p_1 = 2 ∈ Q`). The side condition `q = l - 1` of Theorem 21
is not needed here.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 22. -/
public theorem_wanted isWellBased_subwordShiftSet (ω l : ℕ) (hω : ω < 2 ^ l) :
    IsWellBased (subwordShiftSet ω l)

/-- Corollary 24: if the elements of `Q` (positive integers) form a well-based sequence, then
`g(x, y) = ∑ S^Q_{n,k} x^n y^k = c / ((1 - x) c - x y)` with `c = 1 + ∑_{q_i ∈ Q} x^{q_i} y`,
stated with the denominator cleared in `(ℤ[y])⟦x⟧` (`y` is `C Polynomial.X`). The empty
set, well based under the paper's equivalent definition, is included (`g = 1/(1-x-xy)`).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 24. -/
public theorem_wanted restrictedCombination_bivariate_genFun_of_isWellBased
    (Q : Finset ℕ) (hQ0 : 0 ∉ Q) (hQ : IsWellBased Q) :
    PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) *
        ((1 - PowerSeries.X) *
            (1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X) -
          PowerSeries.X * PowerSeries.C Polynomial.X) =
      1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X

/-- The restricted-overlap tilings of an `n`-board (cells `0, …, n - 1`) with squares and `k`
`Q`-combs. The `Q`-comb has length `q + 1` with `q = Q.sup id`; its cell `0` and each cell
`j ∈ Q` are teeth and the other cells are gaps. A comb's non-leftmost cells may overlap
non-leftmost cells of other combs and no other overlap is allowed, so squares fill exactly the
cells covered by no comb and a tiling is determined by its set `P` of comb start cells: each
comb fits on the board and no comb's cell `0` is covered by a tooth `s' + j` (`0 ≠ j ∈ Q`) of
another comb.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilings (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  (((Finset.range n).filter fun s => s + Q.sup id < n).powersetCard k).filter
    fun P => ∀ s ∈ P, ∀ s' ∈ P, ∀ j ∈ Q, j ≠ 0 → s ≠ s' + j

/-- The paper's `B^Q_{n,k}`: the number of restricted-overlap tilings of an `n`-board with
squares and `k` `Q`-combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilingCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedOverlapTilings Q n k).card

/-- With `Q = {1}` the comb is a domino, and a `4`-board has one tiling with two dominoes.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedOverlapTilingCount_singleton_one_four_two :
    restrictedOverlapTilingCount {1} 4 2 = 1 := by
  decide

/-- With `Q = {2}` the comb is a `(1,1,1)`-comb; two of them interlock on a `4`-board
(starts `0` and `1`), the only tiling with two combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem restrictedOverlapTilingCount_singleton_two_four_two :
    restrictedOverlapTilingCount {2} 4 2 = 1 := by
  decide

/-- Theorem 1 (Theorem 2 of All24): `S^Q_{n,k} = B^Q_{n+q,k}` and `S^Q_n = B^Q_{n+q}`, where `q`
is the largest element of `Q` (`0` for `Q = ∅`).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 1. -/
public theorem_wanted restrictedCombinationCount_eq_restrictedOverlapTilingCount
    (Q : Finset ℕ) (n k : ℕ) :
    restrictedCombinationCount Q n k = restrictedOverlapTilingCount Q (n + Q.sup id) k ∧
      restrictedCombinationTotal Q n = ∑ j ∈ Finset.range (n + Q.sup id + 1),
        restrictedOverlapTilingCount Q (n + Q.sup id) j

/-- Corollary 7: with `G(x, y) = ∑ B^Q_{n,k} x^n y^k` and `g^Q(x, y) = ∑ S^Q_{n,k} x^n y^k`,
`g^Q = (G - (1 - x^q)/(1 - x)) / x^q`, stated as `x^q g^Q = G - ∑_{n<q} x^n` in `(ℤ[y])⟦x⟧`
(`y` is `Polynomial.X`); the record's `g^Q(x) = g^Q(x, 1)` is notation.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 7. -/
public theorem_wanted restrictedCombination_genFun_eq_tiling_genFun (Q : Finset ℕ) :
    PowerSeries.X ^ Q.sup id * PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) =
      PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedOverlapTilingCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) -
        ∑ n ∈ Finset.range (Q.sup id), PowerSeries.X ^ n

/-- Lemma 12 (from Edwards and Allen 2015): fence tilings and strongly restricted
permutations. Each cell `i` of an `n`-board has a left slot `2i` and a right slot `2i + 1`; a
fence `(s, g)` (a `(1/2, g)`-fence) has teeth in slots `s` and `s + 1 + 2g`. Allowed fences:
left tooth in a left slot with `g ∈ D`, or left tooth in a right slot (gap aligned with cell
boundaries) with `-g - 1 ∈ D`; a tiling covers every slot exactly once. The tilings correspond
bijectively to the permutations `π` of `ℕ_n` (0-based) with `π(i) - i ∈ D`, via: if the left
slot of cell `i` holds the left (right) tooth of a fence with gap `g`, then `π(i) = i + g`
(`π(i) = i - g - 1`).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Lemma 12. -/
public theorem_wanted fenceTiling_strongPerm_bijection (D : Finset ℤ) (n : ℕ) :
    let IsTiling := fun t : Finset (ℕ × ℕ) =>
      (∀ f ∈ t, f.1 + 1 + 2 * f.2 < 2 * n ∧
        ((f.1 % 2 = 0 ∧ (f.2 : ℤ) ∈ D) ∨ (f.1 % 2 = 1 ∧ -(f.2 : ℤ) - 1 ∈ D))) ∧
      ∀ x < 2 * n, ∃! f, f ∈ t ∧ (x = f.1 ∨ x = f.1 + 1 + 2 * f.2)
    let Compatible := fun (t : Finset (ℕ × ℕ)) (π : Equiv.Perm (Fin n)) =>
      ∀ i : Fin n, ∀ f ∈ t,
        (f.1 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) + f.2) ∧
        (f.1 + 1 + 2 * f.2 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) - f.2 - 1)
    (∀ t, IsTiling t → ∃! π : Equiv.Perm (Fin n),
        (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) ∧ Compatible t π) ∧
      ∀ π : Equiv.Perm (Fin n), (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) →
        ∃! t, IsTiling t ∧ Compatible t π

/-- Every metatile of every restricted-overlap tiling with squares and `Q`-combs contains at most
two combs. A metatile is a gapless grouping of tiles that cannot be split into smaller gapless
groupings; for a tiling given by its set `P` of comb start cells (see
`restrictedOverlapTilings`), the boundary before cell `j` separates two metatiles iff no tile
straddles it, i.e. no comb `s ∈ P` has `s < j ≤ s + q` (`q = Q.sup id`; squares never straddle).
So the condition says that any three combs `a < b < c` of a tiling are separated by such a
boundary `j` with `a < j ≤ c`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1 (metatiles) and Lemma 15. -/
public def MetatilesHaveAtMostTwoCombs (Q : Finset ℕ) : Prop :=
  ∀ N k, ∀ P ∈ restrictedOverlapTilings Q N k, ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a < b → b < c →
    ∃ j, a < j ∧ j ≤ c ∧ ∀ s ∈ P, ¬ (s < j ∧ j ≤ s + Q.sup id)

/-- With `Q = ∅` the comb is a single cell, so no tile straddles a boundary and every metatile
is a single tile.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem metatilesHaveAtMostTwoCombs_empty : MetatilesHaveAtMostTwoCombs ∅ := by
  intro N k P _ a _ b _ c _ hab hbc
  exact ⟨c, by omega, le_rfl, fun s _ h => by simp at h; omega⟩

/-- With `Q = {3}` the comb is a `(1,2,1)`-comb, and combs starting at cells `0, 1, 2` of a
`6`-board form a single metatile with three combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public theorem not_metatilesHaveAtMostTwoCombs_three : ¬ MetatilesHaveAtMostTwoCombs {3} := by
  intro h
  obtain ⟨j, hj0, hj2, hj⟩ := h 6 3 {0, 1, 2} (by decide) 0 (by simp) 1 (by simp) 2 (by simp)
    (by omega) (by omega)
  exact hj 0 (by simp) ⟨hj0, by simp; omega⟩

/-- Lemma 15: let `q > 0` be the largest element of `Q`. Then `S^Q_n` is, for all `n`, the
number of compositions of `n + q` into parts drawn from a finite set of distinct parts iff every
metatile of a restricted-overlap tiling with squares and `Q`-combs contains at most two combs;
in that case the parts are `1`, `q + 1` and `q + 1 + p` for each empty cell `p ∈ {1, …, q} \ Q`
of the `Q`-comb. Parts are positive (Mathlib `Composition`), so the finite part set is a
`Finset ℕ`.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Lemma 15. -/
public theorem_wanted restrictedCombinationTotal_eq_card_compositions_iff_metatiles
    (Q : Finset ℕ) (hq : 0 < Q.sup id) :
    ((∃ A : Finset ℕ, ∀ n, restrictedCombinationTotal Q n =
        Nat.card {c : Composition (n + Q.sup id) // ∀ b ∈ c.blocks, b ∈ A}) ↔
      MetatilesHaveAtMostTwoCombs Q) ∧
    (MetatilesHaveAtMostTwoCombs Q → ∀ n, restrictedCombinationTotal Q n =
      Nat.card {c : Composition (n + Q.sup id) // ∀ b ∈ c.blocks,
        b = 1 ∨ b = Q.sup id + 1 ∨ ∃ p ∈ Finset.Icc 1 (Q.sup id) \ Q, b = Q.sup id + 1 + p})

end

end MetaMathlibExt
