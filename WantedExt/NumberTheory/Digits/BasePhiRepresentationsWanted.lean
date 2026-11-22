/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.LinearCombination
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Counting base phi representations

Statements from Michel Dekking and Ad van Loon, *Counting Base Phi
Representations*, Fibonacci Quarterly 62 (2024), no. 2, 112-124.

A finite base phi expansion with digits `0` and `1` is encoded by the finite set
`S : Finset ℤ` of positions of its digits `1`; it represents
`∑ i ∈ S, φ ^ i`. The word `B(N)` of the paper is the digit word of `S` read from
the highest to the lowest position, so a statement about `B(N)` alone is a
statement about `S` up to translation.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- The real number represented by the finite base phi expansion whose digits `1`
sit at the positions in `S`, namely `∑ i ∈ S, φ ^ i`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (definition of a base phi
representation). -/
noncomputable def basePhiValue (S : Finset ℤ) : ℝ :=
  ∑ i ∈ S, φ ^ i

/-- A finite base phi expansion is a Bergman expansion when no two digits `1` are
adjacent (`d_{i+1} d_i = 11` is not allowed).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (Bergman representation). -/
def IsBergmanExpansion (S : Finset ℤ) : Prop :=
  ∀ i ∈ S, i + 1 ∉ S

/-- The golden mean flip `100 → 011`: the digit `1` at position `i` is replaced by
digits `1` at positions `i - 1` and `i - 2`, which were `0`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Sections 1 and 2 (the map `T_i`). -/
def IsGoldenMeanFlip (S T : Finset ℤ) : Prop :=
  ∃ i ∈ S, i - 1 ∉ S ∧ i - 2 ∉ S ∧ T = insert (i - 1) (insert (i - 2) (S.erase i))

/-- Knott's truncation rule `a_{R+2} a_{R+1} a_R ≠ 011`: the expansion does not end
in the digits `0, 1, 1`, where `R` is the lowest position of a digit `1`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
def SatisfiesKnottCondition (S : Finset ℤ) : Prop :=
  ∀ m ∈ S, (∀ j ∈ S, m ≤ j) → ¬ (m + 1 ∈ S ∧ m + 2 ∉ S)

/-- The Knott expansions of `N`: the finite base phi expansions of `N` with digits
`0` and `1` that satisfy Knott's truncation rule.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
def knottExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | basePhiValue S = N ∧ SatisfiesKnottCondition S}

/-- `Tot_κ(N)`, the number of Knott expansions of `N` (OEIS A289749).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
noncomputable def knottExpansionCount (N : ℕ) : ℕ :=
  (knottExpansions N).ncard

/-- The natural base phi expansions of `N`: the Knott expansions of `N` whose
lowest digit `1` is at the same position as the lowest digit `1` of the Bergman
expansion of `N` (equal length of the negative part).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
def naturalExpansions (N : ℕ) : Set (Finset ℤ) :=
  {S | S ∈ knottExpansions N ∧
    ∃ T : Finset ℤ, IsBergmanExpansion T ∧ basePhiValue T = N ∧ T.min = S.min}

/-- `Tot_ν(N)`, the number of natural base phi expansions of `N`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
noncomputable def naturalExpansionCount (N : ℕ) : ℕ :=
  (naturalExpansions N).ncard

/-- `Tot_FIB(m)`, the number of representations of `m` as a sum of Fibonacci
numbers `F_i` with distinct indices `i ≥ 2` (OEIS A000119). Indices above `m + 1`
never occur because `F_{m+2} > m`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (base Fibonacci representations). -/
def fibonacciRepresentationCount (m : ℕ) : ℕ :=
  ((Finset.Icc 2 (m + 1)).powerset.filter fun T => ∑ i ∈ T, Nat.fib i = m).card

/-- The empty expansion represents `0`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_empty : basePhiValue ∅ = 0 := by
  simp [basePhiValue]

/-- `β(1) = 1`: the expansion with a single digit `1` at position `0` represents `1`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem basePhiValue_singleton_zero : basePhiValue {0} = 1 := by
  simp [basePhiValue]

/-- `β(2) = 10.01`, that is `φ + φ⁻² = 2`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), proof of Proposition 3.1. -/
theorem basePhiValue_one_neg_two : basePhiValue {1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_pair (by decide), zpow_one, zpow_neg, zpow_ofNat, ← inv_pow,
    hinv]
  linear_combination Real.goldenRatio_sq

/-- The expansion `1.11` also represents `2`: `1 + φ⁻¹ + φ⁻² = 2`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem basePhiValue_zero_neg_one_neg_two : basePhiValue {0, -1, -2} = 2 := by
  have hinv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]; ring
  rw [basePhiValue, Finset.sum_insert (by decide), Finset.sum_pair (by decide), zpow_zero,
    zpow_neg, zpow_neg, zpow_one, zpow_ofNat, ← inv_pow, hinv]
  linear_combination Real.goldenRatio_sq

/-- `10.01` is a Bergman expansion.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem isBergmanExpansion_one_neg_two : IsBergmanExpansion {1, -2} := by
  unfold IsBergmanExpansion
  decide

/-- One golden mean flip turns `10.01` into `1.11`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 2. -/
theorem isGoldenMeanFlip_one_neg_two : IsGoldenMeanFlip {1, -2} {0, -1, -2} :=
  ⟨1, by decide, by decide, by decide, by decide⟩

/-- `1.11` is a Knott expansion of `2`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1. -/
theorem zero_neg_one_neg_two_mem_knottExpansions : ({0, -1, -2} : Finset ℤ) ∈ knottExpansions 2 :=
  ⟨by rw [basePhiValue_zero_neg_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩

/-- `0.11` (which represents `1`) ends in `011` and is not a Knott expansion.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1). -/
theorem not_satisfiesKnottCondition_neg_one_neg_two :
    ¬ SatisfiesKnottCondition {-1, -2} := by
  unfold SatisfiesKnottCondition
  decide

/-- `10.01` is a natural expansion of `2` (it is the Bergman expansion).

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 4. -/
theorem one_neg_two_mem_naturalExpansions : ({1, -2} : Finset ℤ) ∈ naturalExpansions 2 :=
  ⟨⟨by rw [basePhiValue_one_neg_two]; norm_num, by unfold SatisfiesKnottCondition; decide⟩,
    {1, -2}, isBergmanExpansion_one_neg_two, by rw [basePhiValue_one_neg_two]; norm_num, rfl⟩

/-- Small values `Tot_FIB(0), …, Tot_FIB(8) = 1, 1, 1, 2, 1, 2, 2, 1, 3`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Section 1 (the listed values of `Tot_FIB`). -/
theorem fibonacciRepresentationCount_small :
    (List.range 9).map fibonacciRepresentationCount = [1, 1, 1, 2, 1, 2, 2, 1, 3] := by
  decide

/-- Every finite base phi expansion with digits `0` and `1` of a natural number `N`
is obtained from the Bergman expansion of `N` by finitely many golden mean flips.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.1
(`fq-2024-dekking11102023-thm-2.1`). -/
public theorem_wanted reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion (N : ℕ)
    {S T : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    (hTN : basePhiValue T = N) :
    Relation.ReflTransGen IsGoldenMeanFlip S T

/-- Recursion for `Tot_κ(N)`. The Bergman expansion of `N ≥ 2` has digits `1` at
positions `p 0 < p 1 < ⋯ < p n`, so `β(N) = 10^{s_n} ⋯ 10^{s_1} 1` with
`s_k = p k - p (k - 1) - 1`. With `r 0 = 1`, `r 1 = s_1 / 2 + 1` (`s_1` even) or
`(s_1 + 1) / 2 + 1` (`s_1` odd), and for `2 ≤ k ≤ n`,
`r k = (s_k / 2 + 1) r (k - 1)` (`s_k` even) or
`r k = ((s_k + 1) / 2 + 1) r (k - 1) - r (k - 2)` (`s_k` odd), one has
`Tot_κ(N) = r n`. The halves are cleared by doubling.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.3
(`fq-2024-dekking11102023-thm-2.3`). -/
public theorem_wanted knottExpansionCount_eq_of_recursion (N : ℕ) (hN : 2 ≤ N) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 3))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (knottExpansionCount N : ℤ) = r n

/-- The Bergman words of the Fibonacci numbers: for `n ≥ 1`,
`B(F_{2n}) = (1000)^{n-1} 1` and `B(F_{2n+1}) = (1000)^{n-1} 1001`. Since `B`
drops the radix point, the position sets are determined up to a translation `t`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 3.1
(`fq-2024-dekking11102023-prop-3.1`). -/
public theorem_wanted bergmanWord_fib (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n) →
      ∃ t : ℤ, S = (Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + t) ∧
    (∀ S : Finset ℤ, IsBergmanExpansion S → basePhiValue S = Nat.fib (2 * n + 1) →
      ∃ t : ℤ, S = insert t ((Finset.range n).image fun j : ℕ => 4 * (j : ℤ) + 3 + t))

/-- `Tot_κ(F_n) = F_n` for all `n ≥ 1`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.2
(`fq-2024-dekking11102023-thm-3.2`). -/
public theorem_wanted knottExpansionCount_fib (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (Nat.fib n) = Nat.fib n

/-- `Tot_κ(L_{2n}) = Tot_κ(L_{2n+1}) = 2n + 1` for all `n ≥ 1`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 3.3
(`fq-2024-dekking11102023-thm-3.3`). -/
public theorem_wanted knottExpansionCount_lucasNumber (n : ℕ) (hn : 1 ≤ n) :
    knottExpansionCount (lucasNumber (2 * n)) = 2 * n + 1 ∧
      knottExpansionCount (lucasNumber (2 * n + 1)) = 2 * n + 1

/-- Recursion for `Tot_ν(N)`: the same as for `Tot_κ(N)` except
`r 1 = (s_1 + 1) / 2` when `s_1` is odd. Notation as in
`knottExpansionCount_eq_of_recursion`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.1
(`fq-2024-dekking11102023-thm-4.1`). -/
public theorem_wanted naturalExpansionCount_eq_of_recursion (N : ℕ) (n : ℕ)
    (p : ℕ → ℤ) (hgap : ∀ k < n, p k + 2 ≤ p (k + 1))
    (hval : basePhiValue ((Finset.range (n + 1)).image p) = N)
    (s : ℕ → ℤ) (hs : ∀ k, 1 ≤ k → k ≤ n → s k = p k - p (k - 1) - 1)
    (r : ℕ → ℤ) (hr0 : r 0 = 1)
    (hr1 : 1 ≤ n → (Even (s 1) → 2 * r 1 = s 1 + 2) ∧ (Odd (s 1) → 2 * r 1 = s 1 + 1))
    (hr : ∀ k, 2 ≤ k → k ≤ n →
      (Even (s k) → 2 * r k = (s k + 2) * r (k - 1)) ∧
      (Odd (s k) → 2 * r k = (s k + 3) * r (k - 1) - 2 * r (k - 2))) :
    (naturalExpansionCount N : ℤ) = r n

/-- `F_{2n+2}` lies in the even Lucas interval `Λ_{2n} = [L_{2n}, L_{2n+1}]` and
`F_{2n+3}` in the odd Lucas interval `Λ_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]`,
for all `n ≥ 1`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Lemma 4.2
(`fq-2024-dekking11102023-lem-4.2`). -/
public theorem_wanted fib_mem_lucasIntervals (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n + 2) ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) ∧
      Nat.fib (2 * n + 3) ∈
        Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1)

/-- `Tot_ν(F_{2n+2}) = F_{2n+1}` and `Tot_ν(F_{2n+3}) = F_{2n+3}` for all `n ≥ 0`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.3
(`fq-2024-dekking11102023-thm-4.3`). -/
public theorem_wanted naturalExpansionCount_fib (n : ℕ) :
    naturalExpansionCount (Nat.fib (2 * n + 2)) = Nat.fib (2 * n + 1) ∧
      naturalExpansionCount (Nat.fib (2 * n + 3)) = Nat.fib (2 * n + 3)

/-- For `N > 3` with Bergman expansion `β(N)` whose lowest digit `1` is at position
`R`, `Tot_ν(N) = Tot_FIB(F_{2 - R} N)`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.4
(`fq-2024-dekking11102023-thm-4.4`). -/
public theorem_wanted naturalExpansionCount_eq_fibonacciRepresentationCount (N : ℕ)
    (hN : 3 < N) {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N)
    {R : ℤ} (hR : IsLeast (S : Set ℤ) R) :
    naturalExpansionCount N = fibonacciRepresentationCount (Nat.fib (2 - R).toNat * N)

/-- Part (a): let `N ≥ 2` and let `β(N)` end in `10^s1`, i.e. its two lowest digits
`1` are at positions `a` and `a + s + 1`. Then `N` lies in an even Lucas interval
`Λ_{2n}` iff `s` is odd, and in an odd Lucas interval `Λ_{2n+1}` iff `s` is even.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(a)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem_wanted bergman_tail_parity_iff_lucasInterval (N : ℕ) (hN : 2 ≤ N)
    {S : Finset ℤ} (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) (a : ℤ) (s : ℕ)
    (htail : S.filter (· ≤ a + s + 1) = {a, a + s + 1}) :
    ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1))) ↔ Odd s) ∧
      ((∃ n : ℕ, N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1)) ↔
        Even s)

/-- Part (b): if the lowest digit `1` of `β(N)` is at position `R`, then `-R = 2n`
for `N ∈ Λ_{2n}` and `-R = 2n + 2` for `N ∈ Λ_{2n+1}`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Proposition 5.1(b)
(`fq-2024-dekking11102023-prop-5.1`). -/
public theorem_wanted bergman_lowest_position_lucasInterval (N n : ℕ) {S : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSN : basePhiValue S = N) {R : ℤ}
    (hR : IsLeast (S : Set ℤ) R) :
    (N ∈ Set.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) → -R = 2 * n) ∧
      (N ∈ Set.Icc (lucasNumber (2 * n + 1) + 1) (lucasNumber (2 * n + 2) - 1) →
        -R = 2 * n + 2)

/-- Recursive structure theorem, part I: for `n ≥ 1` and `0 ≤ k ≤ L_{2n-1}`,
`β(L_{2n} + k) = β(L_{2n}) + β(k) = 10⋯0 β(k) 0⋯01`, where
`β(L_{2n}) = 10^{2n}.0^{2n-1}1` has digits `1` at positions `2n` and `-2n`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 I,
quoting F. M. Dekking, *How to add two numbers in base phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem_wanted bergman_lucas_even_add (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ lucasNumber (2 * n - 1)) {S T : Finset ℤ}
    (hS : IsBergmanExpansion S) (hSk : basePhiValue S = k)
    (hT : IsBergmanExpansion T) (hTN : basePhiValue T = (lucasNumber (2 * n) + k : ℕ)) :
    (2 * n : ℤ) ∉ S ∧ -(2 * n : ℤ) ∉ S ∧ T = insert (2 * n : ℤ) (insert (-(2 * n : ℤ)) S)

/-- Recursive structure theorem, part II, as identities of digit words (free-group
notation of the paper). If `β(M)` has lowest digit `1` at `a` and highest at `t`,
removing its leading `10` and trailing `01` leaves the digits at positions in
`(S.erase a).erase t`. Then, for `n ≥ 2`:
* `I_n`, `1 ≤ k ≤ L_{2n-2} - 1`:
  `β(L_{2n+1} + k) = 1000 (10)⁻¹ β(L_{2n-1} + k) (01)⁻¹ 1001`;
* `K_n`, same `k`:
  `β(L_{2n+1} + L_{2n-1} + k) = 1010 (10)⁻¹ β(L_{2n-1} + k) (01)⁻¹ 0001`;
* `J_n`, `0 ≤ k ≤ L_{2n-3}`:
  `β(L_{2n+1} + L_{2n-2} + k) = 10010 (10)⁻¹ β(L_{2n-2} + k) (01)⁻¹ 001001`.
The words carry no radix point, so the new expansion is pinned up to its lowest
position `b`.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 II,
quoting F. M. Dekking, *How to add two numbers in base phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem_wanted bergman_lucas_odd_add (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + (t - a) + 2, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, k ≤ lucasNumber (2 * n - 3) →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 2) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 2) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4, b + (t - a) + 7} ∪
          ((S.erase a).erase t).image (· + (b - a + 4)))

end

end MetaMathlibExt
