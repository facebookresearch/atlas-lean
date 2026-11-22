/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Nat.Fib.Zeckendorf
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import WantedExt.NumberTheory.Digits.BasePhiRepresentationsWanted

/-!
# The structure of base phi expansions

Statements from F. Michel Dekking, *The Structure of Base Phi Expansions*,
INTEGERS 24 (2024), Article A24 (arXiv:2305.08349).

The base phi expansion `β(N)` of a natural number `N` is its unique finite
expansion `N = ∑ dᵢ φ ^ i` with digits `0, 1` and no two adjacent digits `1`.
It is encoded, as in `BasePhiRepresentationsWanted`, by the finite set
`S : Finset ℤ` of positions of its digits `1`. Statements about `β(N)` are stated
for every `S` with `IsBasePhiExpansion N S`; existence and uniqueness of `S` are
Bergman's theorem and are not assumed. The positive part `β⁺(N)` is
`S.filter (0 ≤ ·)` and the negative part `β⁻(N)` is `S.filter (· < 0)`.
A free-group word identity of the paper such as
`β(N) = 1000 (10)⁻¹ β(M) (01)⁻¹ 1001` is stated as the corresponding operation on
the position sets, together with the digit facts that make the cancellations
`(10)⁻¹` and `(01)⁻¹` valid.
-/

open scoped goldenRatio

namespace MetaMathlibExt

@[expose] public section

/-- `S` is the base phi expansion of `N`: a Bergman expansion (no two adjacent
digits `1`) whose value `∑ i ∈ S, φ ^ i` is `N`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 1 (definition of `β(N)`). -/
def IsBasePhiExpansion (N : ℕ) (S : Finset ℤ) : Prop :=
  IsBergmanExpansion S ∧ basePhiValue S = N

/-- The empty expansion is the base phi expansion of `0`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 1. -/
theorem isBasePhiExpansion_zero : IsBasePhiExpansion 0 ∅ := by
  refine ⟨fun i hi => by simp at hi, ?_⟩
  simp [basePhiValue]

/-- `β(1) = 1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Table 1. -/
theorem isBasePhiExpansion_one : IsBasePhiExpansion 1 {0} := by
  refine ⟨fun i hi => by simp at hi ⊢; omega, ?_⟩
  simp [basePhiValue]

/-- `HasDigitBlock S k w`: the digits `d_k d_{k-1} … d_{k-|w|+1}` of the
expansion with digit-`1` positions `S` are the letters of `w`, read from the
highest position down (a letter `1` means a digit `1`, any other letter a
digit `0`).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Sections 6 and 7 (digit blocks `d_{m-1} ⋯ d_0` and
`d_{-1} ⋯ d_{-m}`). -/
def HasDigitBlock (S : Finset ℤ) : ℤ → List ℕ → Prop
  | _, [] => True
  | k, b :: w => (k ∈ S ↔ b = 1) ∧ HasDigitBlock S (k - 1) w

/-- The empty block always occurs.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem hasDigitBlock_nil (S : Finset ℤ) (k : ℤ) : HasDigitBlock S k [] := trivial

/-- Peeling off the leading letter of a digit block.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem hasDigitBlock_cons (S : Finset ℤ) (k : ℤ) (b : ℕ) (w : List ℕ) :
    HasDigitBlock S k (b :: w) ↔ (k ∈ S ↔ b = 1) ∧ HasDigitBlock S (k - 1) w :=
  Iff.rfl

/-- The occurrence set of the digit block `w` placed with its first letter at
position `k`: the natural numbers `N` whose base phi expansion has
`HasDigitBlock S k w`. The paper's `R_w` (an end block of `β⁺(N)`) is the case
`k = |w| - 1`, and `R_{·w}` (a prefix of `β⁻(N)`) is the case `k = -1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Sections 6 and 7 (occurrence sequences `R_w`). -/
def basePhiOccurrences (k : ℤ) (w : List ℕ) : Set ℕ :=
  {N | ∃ S, IsBasePhiExpansion N S ∧ HasDigitBlock S k w}

/-- `1 ∈ R_1`: the expansion `β(1) = 1` ends in the digit `1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 6. -/
theorem one_mem_basePhiOccurrences_one : 1 ∈ basePhiOccurrences 0 [1] :=
  ⟨{0}, isBasePhiExpansion_one, by simp [HasDigitBlock]⟩

/-- The generalized Beatty sequence `V(p, q, r)`, `n ↦ p ⌊n φ⌋ + q n + r`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
noncomputable def generalizedBeatty (p q r : ℤ) (n : ℕ) : ℤ :=
  p * ⌊(n : ℝ) * φ⌋ + q * n + r

/-- `V(p, q, r)` at `n = 0` is `r`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6 (`V₀`). -/
theorem generalizedBeatty_zero (p q r : ℤ) : generalizedBeatty p q r 0 = r := by
  simp [generalizedBeatty]

/-- `V(p, q, r)` at `n = 1` is `p + q + r`, since `⌊φ⌋ = 1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
theorem generalizedBeatty_one (p q r : ℤ) : generalizedBeatty p q r 1 = p + q + r := by
  have h : ⌊φ⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using Real.one_lt_goldenRatio.le, by
      simpa [one_add_one_eq_two] using Real.goldenRatio_lt_two⟩
  simp [generalizedBeatty, h]

/-- The terms `V(p, q, r)(n)`, `n ≥ 1`, as a set.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
def beattySet (p q r : ℤ) : Set ℤ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = generalizedBeatty p q r n}

/-- The terms `V₀(p, q, r)(n)`, `n ≥ 0`, as a set.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6 (definition of `V₀`). -/
def beattySet₀ (p q r : ℤ) : Set ℤ :=
  Set.range (generalizedBeatty p q r)

/-- `V(p, q, r)(1) = p + q + r` is a term of `V(p, q, r)`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 5. -/
theorem add_add_mem_beattySet (p q r : ℤ) : p + q + r ∈ beattySet p q r :=
  ⟨1, le_rfl, (generalizedBeatty_one p q r).symm⟩

/-- `r = V₀(p, q, r)(0)` is a term of `V₀(p, q, r)`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 6. -/
theorem mem_beattySet₀_self (p q r : ℤ) : r ∈ beattySet₀ p q r :=
  ⟨0, generalizedBeatty_zero p q r⟩

/-- No base phi expansion contains `d_{2m} ⋯ d_0 · d_{-1} = 10^{2m} · 1`, and
none contains `d_{2m+1} ⋯ d_0 · d_{-1} = 10^{2m+1} · 0`, for `m ≥ 1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 1 (`integers-2024-A24-lem-1`). -/
public theorem_wanted basePhi_no_block_one_zeros_dot (m : ℕ) (hm : 1 ≤ m) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S (2 * m) (1 :: List.replicate (2 * m) 0 ++ [1]) ∧
      ¬ HasDigitBlock S (2 * m + 1) (1 :: List.replicate (2 * m + 1) 0 ++ [0])

/-- Propagation Principle, part (a): a central digit block
`d_3 ⋯ d_0 · d_{-1} ⋯ d_{-4}` that occurs in none of the expansions of
`N = 0, 1, …, 17` occurs in no base phi expansion. The base case includes
`N = 0`, as in the paper's proof; part (b) is not formalized.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 2 (a) (`integers-2024-A24-lem-2`). -/
public theorem_wanted basePhi_propagation_principle (w : List ℕ) (hw : w.length = 8)
    (h : ∀ N ≤ 17, ∀ S, IsBasePhiExpansion N S → ¬ HasDigitBlock S 3 w) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) : ¬ HasDigitBlock S 3 w

/-- Composition with the lower and upper Wythoff sequences
`A(n) = ⌊n φ⌋` and `B(n) = ⌊n φ⌋ + n`: for `n ≥ 1`,
`V(p,q,r)(A(n)) = V(p+q, p, r-p)(n)` and `V(p,q,r)(B(n)) = V(2p+q, p+q, r)(n)`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 3 (`integers-2024-A24-lem-3`). -/
public theorem_wanted generalizedBeatty_comp_wythoff (p q r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    generalizedBeatty p q r ⌊(n : ℝ) * φ⌋₊ = generalizedBeatty (p + q) p (r - p) n ∧
      generalizedBeatty p q r (⌊(n : ℝ) * φ⌋₊ + n) =
        generalizedBeatty (2 * p + q) (p + q) r n

/-- Converse of the composition lemma: if the terms of an increasing generalized
Beatty sequence `V(p, q, r)` split into disjoint sets `U` and `W` and `U` is the
term set of `V(p+q, p, r-p)`, then `W` is the term set of `V(2p+q, p+q, r)`.
Sequences are identified with their term sets; the hypotheses `0 < p + q` and
`0 < 2p + q` say that `V` is increasing, as the paper's sequences are.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 4 (`integers-2024-A24-lem-4`). -/
public theorem_wanted beattySet_complement_of_lowerWythoff (p q r : ℤ) (hpq : 0 < p + q)
    (h2pq : 0 < 2 * p + q) (U W : Set ℤ) (hdisj : Disjoint U W)
    (hunion : U ∪ W = beattySet p q r) (hU : U = beattySet (p + q) p (r - p)) :
    W = beattySet (2 * p + q) (p + q) r

/-- The first differences `V(n+1) - V(n)`, `n ≥ 1`, of `V(p, q, r)` form the
Fibonacci word on the alphabet `{2p+q, p+q}` (letter `0 ↦ 2p+q`,
`1 ↦ p+q`); conversely every integer sequence whose first differences form the
Fibonacci word on `{a, b}` is `V(a-b, 2b-a, r)` for some integer `r`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 5 (`integers-2024-A24-lem-5`). -/
public theorem_wanted generalizedBeatty_diff_eq_fibInf (p q r : ℤ) :
    (∀ n : ℕ, 1 ≤ n → generalizedBeatty p q r (n + 1) - generalizedBeatty p q r n =
      if fibInf (n - 1) then p + q else 2 * p + q) ∧
    ∀ (a b : ℤ) (v : ℕ → ℤ),
      (∀ n : ℕ, 1 ≤ n → v (n + 1) - v n = if fibInf (n - 1) then b else a) →
        ∃ r' : ℤ, ∀ n : ℕ, 1 ≤ n → v n = generalizedBeatty (a - b) (2 * b - a) r' n

/-- For `m ≥ 2` no positive part `β⁺(N)` has end block `10^{2m}1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 6 (`integers-2024-A24-lem-6`). -/
public theorem_wanted basePhi_no_end_block_one_zeros_one (m : ℕ) (hm : 2 ≤ m) (N : ℕ)
    (S : Finset ℤ) (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S (2 * m + 1) (1 :: List.replicate (2 * m) 0 ++ [1])

/-- For a nonempty word `u = d_{m-1} ⋯ d_1` such that `u 1` contains no `11`,
the block `u 1 · 0` occurs in `β(N)` if and only if `u 0 · 0` occurs in
`β(N - 1)`, for `N ≥ 1`. The hypothesis that `u 1` has no `11` is the paper's
implicit standing assumption on digit blocks (for `u = 1` the block `11 · 0`
never occurs, while `10 · 0` occurs in `β(2) = 10 · 01`).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 7 (`integers-2024-A24-lem-7`). -/
public theorem_wanted basePhi_end_block_one_iff_pred (u : List ℕ) (hu : u ≠ [])
    (hz : List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) (u ++ [1])) (N : ℕ) (hN : 1 ≤ N) :
    N ∈ basePhiOccurrences u.length (u ++ [1, 0]) ↔
      N - 1 ∈ basePhiOccurrences u.length (u ++ [0, 0])

/-- `F_n + 3 F_{n+1} = L_{n+2}` for all `n ≥ 0`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 9 (`integers-2024-A24-lem-9`). -/
public theorem_wanted fib_add_three_mul_fib_succ_eq_lucasNumber (n : ℕ) :
    Nat.fib n + 3 * Nat.fib (n + 1) = lucasNumber (n + 2)

/-- Border words and codes, for `n ≥ 1`. With `γ⁻(N)` the negative part
`β⁻(N)` with its final `01` removed, the paper's
`γ⁻(L_{2n}) = 0^{2n-2}`, `γ⁻(L_{2n+1}) = (01)^{n-1}`,
`γ⁻(L_{2n+1}+1) = (10)^n`, `γ⁻(L_{2n+2}-1) = 0^{2n}` are stated as the
corresponding negative parts `β⁻ = γ⁻ 01`. The code `C(N) = Z⁻¹(γ⁻(N))` of an
`N` whose `β⁻(N)` has length `2j` is `∑_{i ∈ β⁻(N)} F_{i + 2j}`, and
`C(L_{2n}) = 0`, `C(L_{2n+1}) = F_{2n-1} - 1`, `C(L_{2n+1}+1) = F_{2n+2} - 1`,
`C(L_{2n+2}-1) = 0`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 10 (`integers-2024-A24-lem-10`). -/
public theorem_wanted basePhi_lucas_border_codes (n : ℕ) (hn : 1 ≤ n) (S₁ S₂ S₃ S₄ : Finset ℤ)
    (h₁ : IsBasePhiExpansion (lucasNumber (2 * n)) S₁)
    (h₂ : IsBasePhiExpansion (lucasNumber (2 * n + 1)) S₂)
    (h₃ : IsBasePhiExpansion (lucasNumber (2 * n + 1) + 1) S₃)
    (h₄ : IsBasePhiExpansion (lucasNumber (2 * n + 2) - 1) S₄) :
    S₁.filter (· < 0) = {-(2 * n : ℤ)} ∧
    S₂.filter (· < 0) = (Finset.Icc 1 n).image (fun j : ℕ => -(2 * j : ℤ)) ∧
    S₃.filter (· < 0) =
      insert (-(2 * n + 2 : ℤ)) ((Finset.Icc 1 n).image (fun j : ℕ => 1 - (2 * j : ℤ))) ∧
    S₄.filter (· < 0) = {-(2 * n + 2 : ℤ)} ∧
    ∑ i ∈ S₁.filter (· < 0), Nat.fib (i + 2 * n).toNat = 0 ∧
    ∑ i ∈ S₂.filter (· < 0), Nat.fib (i + 2 * n).toNat = Nat.fib (2 * n - 1) - 1 ∧
    ∑ i ∈ S₃.filter (· < 0), Nat.fib (i + 2 * n + 2).toNat = Nat.fib (2 * n + 2) - 1 ∧
    ∑ i ∈ S₄.filter (· < 0), Nat.fib (i + 2 * n + 2).toNat = 0

/-- The block `d_1 d_0 · d_{-1} = 10 · 1` never occurs, and
`d_1 d_0 · d_{-1} = 00 · 1` occurs in `β(N)`, `N ≥ 1`, if and only if
`N = 3 ⌊n φ⌋ + n + 1` for some `n ≥ 1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 1 (`integers-2024-A24-prop-1`). -/
public theorem_wanted basePhi_digits_dot_one (N : ℕ) (hN : 1 ≤ N) (S : Finset ℤ)
    (hS : IsBasePhiExpansion N S) :
    ¬ HasDigitBlock S 1 [1, 0, 1] ∧
      (HasDigitBlock S 1 [0, 0, 1] ↔ (N : ℤ) ∈ beattySet 3 1 1)

/-- End blocks of length at most 3 ending in `0`, for `N ≥ 1`:
`R_0 = V(-1,3,0)`, `R_{00} = V₀(1,2,0) ⊔ V(3,1,1)`,
`R_{10} = R_{010} = V(1,2,-1)`, `R_{000} = V₀(4,3,0) ⊔ V(3,1,1)`,
`R_{100} = V(3,1,-1)`. Sequences are compared through their terms `≥ 1`; the two
disjoint unions `⊔` are stated as unions together with `Disjoint` conjuncts.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 2 (`integers-2024-A24-prop-2`). -/
public theorem_wanted basePhi_short_end_blocks_zero (N : ℕ) (hN : 1 ≤ N) :
    (N ∈ basePhiOccurrences 0 [0] ↔ (N : ℤ) ∈ beattySet (-1) 3 0) ∧
    (N ∈ basePhiOccurrences 1 [0, 0] ↔ (N : ℤ) ∈ beattySet₀ 1 2 0 ∪ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences 1 [1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 2 [0, 1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 2 [0, 0, 0] ↔ (N : ℤ) ∈ beattySet₀ 4 3 0 ∪ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences 2 [1, 0, 0] ↔ (N : ℤ) ∈ beattySet 3 1 (-1)) ∧
    Disjoint (beattySet₀ 1 2 0) (beattySet 3 1 1) ∧ Disjoint (beattySet₀ 4 3 0) (beattySet 3 1 1)

/-- Prefixes of length at most 3 of `β⁻(N)`, for `N ≥ 2` (so that `β⁻(N)` is
nonempty; `β(1) = 1` has empty negative part). Part (a) is stated in the reading
`R_{·0} = V(1,2,[-1,0,1])` of the paper's Figure 3: as printed,
`V(2,1,-1) ⊔ V(2,1,0) ⊔ V(2,1,1)` misses `6` (`β(6) = 1010 · 0001`) and contains
`12` (`β(12) = 100000 · 101001`).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Proposition 3 (`integers-2024-A24-prop-3`). -/
public theorem_wanted basePhi_short_negative_prefixes (N : ℕ) (hN : 2 ≤ N) :
    (N ∈ basePhiOccurrences (-1) [0] ↔
      (N : ℤ) ∈ beattySet 1 2 (-1) ∪ beattySet 1 2 0 ∪ beattySet 1 2 1) ∧
    (N ∈ basePhiOccurrences (-1) [1] ↔ (N : ℤ) ∈ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0] ↔ (N : ℤ) ∈ beattySet 3 1 1) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0] ↔
      (N : ℤ) ∈ beattySet 3 1 2 ∪ beattySet 3 1 3 ∪ beattySet 3 1 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 1] ↔
      (N : ℤ) ∈ beattySet₀ 4 3 2 ∪ beattySet₀ 4 3 3 ∪ beattySet₀ 4 3 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 1, 0] ↔
      (N : ℤ) ∈ beattySet₀ 4 3 2 ∪ beattySet₀ 4 3 3 ∪ beattySet₀ 4 3 4) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0, 0] ↔
      (N : ℤ) ∈ beattySet 4 3 (-1) ∪ beattySet 4 3 0 ∪ beattySet 4 3 1) ∧
    (N ∈ basePhiOccurrences (-1) [0, 0, 1] ↔
      (N : ℤ) ∈ beattySet 7 4 2 ∪ beattySet 7 4 3 ∪ beattySet 7 4 4) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0, 0] ↔ (N : ℤ) ∈ beattySet 4 3 (-2)) ∧
    (N ∈ basePhiOccurrences (-1) [1, 0, 1] ↔ (N : ℤ) ∈ beattySet 7 4 1)

/-- Embedding into Zeckendorf: `β⁺(N) = Z(N + S(N))` for all `N ≥ 0`, where
`Z(M)` is the Zeckendorf expansion (digit `e_i` weighted by `F_{i+2}`) and
`S(N)` is the number of `n ≥ 1` with `3 ⌊n φ⌋ + n + 1 < N`, i.e. the number of
`M < N` with `d_{-1}(M) = 1`, as in the paper's proof. Both printed formulas for
`S` are off by one: `S(N) = max {k : 3⌊kφ⌋ + k ≤ N}` gives `S(4) = 1` and
`Z(5) = 1000 ≠ 101 = β⁺(4)`, and `S(N) = max {k : V(k) ≤ N} - 1` gives
`S(6) = 0` and `Z(6) = 1001 ≠ 1010 = β⁺(6)`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 1 (`integers-2024-A24-thm-1`). -/
public theorem_wanted basePhi_positive_part_eq_zeckendorf (N : ℕ) (S : Finset ℤ)
    (hS : IsBasePhiExpansion N S) :
    S.filter (0 ≤ ·) =
      ((Nat.zeckendorf
          (N + ((Finset.Icc 1 N).filter (fun n => generalizedBeatty 3 1 1 n < N)).card)).map
        (fun k : ℕ => (k : ℤ) - 2)).toFinset

/-- Recursive Structure Theorem, in the index ranges of the arXiv text. With
`β(M)` for `M ∈ Λ_{2n-1}` (top digits `10` at `2n-1, 2n-2`, bottom digits `01`
at `1-2n, -2n`) and `M ∈ Λ_{2n-2}` (top `10` at `2n-2`, bottom `01` at `2-2n`),
for `n ≥ 2`:
`I_n`: `β(L_{2n+1}+k) = 1000 (10)⁻¹ β(L_{2n-1}+k) (01)⁻¹ 1001`, `1 ≤ k ≤ L_{2n-2}-1`;
`K_n`: `β(L_{2n+1}+L_{2n-1}+k) = 1010 (10)⁻¹ β(L_{2n-1}+k) (01)⁻¹ 0001`, same `k`;
`J_n`: `β(L_{2n+1}+L_{2n-2}+k) = 10010 (10)⁻¹ β(L_{2n-2}+k) (01)⁻¹ 001001`,
`0 ≤ k ≤ L_{2n-3}`. Part (B), `β(L_{2n+2}+k) = β(L_{2n+2}) + β(k)` for `n ≥ 1` and
`0 ≤ k ≤ L_{2n+1}`, is not restated: it is the existing `bergman_lucas_even_add`
(`WantedExt/NumberTheory/Digits/BasePhiRepresentationsWanted.lean`) at index `n + 1`.
The record's ranges `k ≤ L_{2n}-1` for `I_n, K_n` and `k ≤ L_{2n-1}` for `J_n`
are too wide: at `n = 2`, `k = 3`, `β(L_3 + 3) = β(7) = 10000 · 0001` has no
digit `1` at position `3`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 2 (`integers-2024-A24-thm-2`). -/
public theorem_wanted basePhi_recursive_structure (n : ℕ) (T S : Finset ℤ) :
    (2 ≤ n → ∀ k, 1 ≤ k → k + 1 ≤ lucasNumber (2 * n - 2) →
      IsBasePhiExpansion (lucasNumber (2 * n - 1) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + k) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            ((T.erase (2 * n - 1 : ℤ)).erase (-(2 * n : ℤ)))))) ∧
    (2 ≤ n → ∀ k, 1 ≤ k → k + 1 ≤ lucasNumber (2 * n - 2) →
      IsBasePhiExpansion (lucasNumber (2 * n - 1) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 1) + k) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
        S = insert (2 * n + 1 : ℤ) (insert (-2 * n - 2 : ℤ) (T.erase (-(2 * n : ℤ))))) ∧
    (2 ≤ n → ∀ k, k ≤ lucasNumber (2 * n - 3) →
      IsBasePhiExpansion (lucasNumber (2 * n - 2) + k) T →
      IsBasePhiExpansion (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 2) + k) S →
        (2 * n - 2 : ℤ) ∈ T ∧ (2 * n - 3 : ℤ) ∉ T ∧ (3 - 2 * n : ℤ) ∉ T ∧ (2 - 2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            (T.erase (2 - 2 * n : ℤ)))))

/-- Recursive Structure Theorem, second version, for `n ≥ 1`, with the odd and
even Lucas intervals `Λ_{2j} = [L_{2j}, L_{2j+1}]`,
`Λ_{2j+1} = [L_{2j+1}+1, L_{2j+2}-1]`. Odd part, for `M` in the indicated
interval:
(a) `β(M + L_{2n}) = 1000 (10)⁻¹ β(M) (01)⁻¹ 1001`, `M ∈ Λ_{2n-1}`;
(b) `β(M + L_{2n+1}) = 100 β(M) (01)⁻¹ 001001`, `M ∈ Λ_{2n-2}`;
(c) `β(M + L_{2n+1}) = 10 β(M) (01)⁻¹ 0001`, `M ∈ Λ_{2n-1}`.
Even part:
(a) `β(M + L_{2n+1}) = 1000 (10)⁻¹ β(M) (01)⁻¹ 0001`, `M ∈ Λ_{2n}`;
(b) `β(M + L_{2n+2}) = 100 β(M) 01`, `M ∈ Λ_{2n-1}`;
(c) `β(M + L_{2n+2}) = 10 β(M) 01`, `M ∈ Λ_{2n}`.
In (B)(c) the record writes `β(N - L_{2n+1})` for `N ∈ Λ^{(c)}_{2n} = Λ_{2n} + L_{2n+2}`;
the shift `L_{2n+2}` of that same definition is used (as printed, `n = 1`,
`N = 10` gives `10 β(6) 01 = 101010 · 000101 ≠ 10100 · 0101 = β(10)`). The
partition identities `Λ_{2n+1} = Λ^{(a)} ∪ Λ^{(b)} ∪ Λ^{(c)}` and the even analogue
are not included.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 3 (`integers-2024-A24-thm-3`). -/
public theorem_wanted basePhi_recursive_structure_lucas_intervals (n : ℕ) (hn : 1 ≤ n)
    (M : ℕ) (T S : Finset ℤ) (hT : IsBasePhiExpansion M T) :
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n)) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (2 * n - 2 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            ((T.erase (2 * n - 1 : ℤ)).erase (-(2 * n : ℤ)))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 2)) (lucasNumber (2 * n - 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (3 - 2 * n : ℤ) ∉ T ∧ (2 - 2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
            (T.erase (2 - 2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (2 * n - 1 : ℤ) ∈ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 1 : ℤ) (insert (-2 * n - 2 : ℤ) (T.erase (-(2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        (2 * n : ℤ) ∈ T ∧ (2 * n - 1 : ℤ) ∉ T ∧ (1 - 2 * n : ℤ) ∉ T ∧ -(2 * n : ℤ) ∈ T ∧
          S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) ((T.erase (2 * n : ℤ)).erase (-(2 * n : ℤ))))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) T)) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S = insert (2 * n + 2 : ℤ) (insert (-2 * n - 2 : ℤ) T))

/-- Short end blocks: `R_1 = V₀(1,2,1)`, `R_{10} = V(1,2,-1)`,
`R_{00·0} = V₀(1,2,0)`, `R_{00·1} = V(3,1,1)`, for `N ≥ 1`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 6 (`integers-2024-A24-thm-6`). -/
public theorem_wanted basePhi_short_end_blocks (N : ℕ) (hN : 1 ≤ N) :
    (N ∈ basePhiOccurrences 0 [1] ↔ (N : ℤ) ∈ beattySet₀ 1 2 1) ∧
    (N ∈ basePhiOccurrences 1 [1, 0] ↔ (N : ℤ) ∈ beattySet 1 2 (-1)) ∧
    (N ∈ basePhiOccurrences 1 [0, 0, 0] ↔ (N : ℤ) ∈ beattySet₀ 1 2 0) ∧
    (N ∈ basePhiOccurrences 1 [0, 0, 1] ↔ (N : ℤ) ∈ beattySet 3 1 1)

/-- End blocks ending in `0` are Lucas-Wythoff sequences: for a `0/1` word
`w = w_{m-1} ⋯ w_0` of length `m ≥ 2` with no `11`, `w_0 = 0` and `w ≠ 0^m`,
there is an integer `γ_w ≤ 0` with `R_w = V(L_{m-2}, L_{m-3}, γ_w)` if
`w_{m-1} = 0` and `R_w = V(L_{m-1}, L_{m-2}, γ_w)` if `w_{m-1} = 1`
(terms `≥ 1`). For `m ≥ 1`, `R_{0^{2m}} = V(L_{2m}, L_{2m-1}, 1) ⊔ V₀(L_{2m-1}, L_{2m-2}, 0)`
and `R_{0^{2m+1}} = V₀(L_{2m+1}, L_{2m}, 0) ⊔ V(L_{2m}, L_{2m-1}, 1)`, each disjoint union
stated as a union together with a `Disjoint` conjunct.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 7 (`integers-2024-A24-thm-7`). -/
public theorem_wanted basePhi_end_blocks_lucasWythoff :
    (∀ w : List ℕ, 2 ≤ w.length → (∀ d ∈ w, d ≤ 1) →
      List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) w → w.getLast? = some 0 →
      w ≠ List.replicate w.length 0 →
        ∃ γ : ℤ, γ ≤ 0 ∧ ∀ N : ℕ, 1 ≤ N →
          (N ∈ basePhiOccurrences (w.length - 1) w ↔
            (N : ℤ) ∈ (if w.head? = some 0 then
              beattySet (lucasNumber (w.length - 2)) (lucasNumber (w.length - 3)) γ
            else beattySet (lucasNumber (w.length - 1)) (lucasNumber (w.length - 2)) γ))) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 1 ≤ N →
      (N ∈ basePhiOccurrences (2 * m - 1) (List.replicate (2 * m) 0) ↔
        (N : ℤ) ∈ beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1 ∪
          beattySet₀ (lucasNumber (2 * m - 1)) (lucasNumber (2 * m - 2)) 0) ∧
      (N ∈ basePhiOccurrences (2 * m) (List.replicate (2 * m + 1) 0) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 0 ∪
          beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1) ∧
      Disjoint (beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1)
        (beattySet₀ (lucasNumber (2 * m - 1)) (lucasNumber (2 * m - 2)) 0) ∧
      Disjoint (beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 0)
        (beattySet (lucasNumber (2 * m)) (lucasNumber (2 * m - 1)) 1)

/-- End blocks ending in `1` are Lucas-Wythoff sequences: for a `0/1` word
`w = w_{m-1} ⋯ w_0` of length `m ≥ 3` with no `11` and `w_0 = 1`, other than the
exceptional words `0^k 1` and `1 0^k 1` (`k ≥ 2`), if `w` occurs as an end block at all,
there is an integer `γ_w ≤ 0` with `R_w = V(L_{m-2}, L_{m-3}, γ_w)` if `w_{m-1} = 0` and
`R_w = V(L_{m-1}, L_{m-2}, γ_w)` if `w_{m-1} = 1` (terms `≥ 1`). For `m ≥ 1`,
`R_{0^{2m}1} = R_{0^{2m+1}1} = V₀(L_{2m+1}, L_{2m}, 1)`, the block `1 0^{2m} 1` never occurs,
and `R_{1 0^{2m+1} 1} = V(L_{2m+2}, L_{2m+1}, 1 - L_{2m+1})`.

The occurrence hypothesis `R_w ≠ ∅` is added: as printed the statement fails for `w = 01001`,
which never occurs (its end block `1001` is excluded), while every `V(p, q, γ)` is nonempty; the
source's proof derives `R_w = R_w̆ + 1` only "if `R_w ≠ ∅`".

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 8 (`integers-2024-A24-thm-8`). -/
public theorem_wanted basePhi_end_blocks_one_lucasWythoff :
    (∀ w : List ℕ, 3 ≤ w.length → (∀ d ∈ w, d ≤ 1) →
      List.IsChain (fun a b => ¬ (a = 1 ∧ b = 1)) w → w.getLast? = some 1 →
      (∀ k : ℕ, 2 ≤ k → w ≠ List.replicate k 0 ++ [1]) →
      (∀ k : ℕ, 2 ≤ k → w ≠ 1 :: List.replicate k 0 ++ [1]) →
      (basePhiOccurrences (w.length - 1) w).Nonempty →
        ∃ γ : ℤ, γ ≤ 0 ∧ ∀ N : ℕ, 1 ≤ N →
          (N ∈ basePhiOccurrences (w.length - 1) w ↔
            (N : ℤ) ∈ (if w.head? = some 0 then
              beattySet (lucasNumber (w.length - 2)) (lucasNumber (w.length - 3)) γ
            else beattySet (lucasNumber (w.length - 1)) (lucasNumber (w.length - 2)) γ))) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 1 ≤ N →
      (N ∈ basePhiOccurrences (2 * m) (List.replicate (2 * m) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 1) ∧
      (N ∈ basePhiOccurrences (2 * m + 1) (List.replicate (2 * m + 1) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet₀ (lucasNumber (2 * m + 1)) (lucasNumber (2 * m)) 1) ∧
      N ∉ basePhiOccurrences (2 * m + 1) (1 :: List.replicate (2 * m) 0 ++ [1]) ∧
      (N ∈ basePhiOccurrences (2 * m + 2) (1 :: List.replicate (2 * m + 1) 0 ++ [1]) ↔
        (N : ℤ) ∈ beattySet (lucasNumber (2 * m + 2)) (lucasNumber (2 * m + 1))
          (1 - (lucasNumber (2 * m + 1) : ℤ)))

/-- Every Zeckendorf word of even length `2n ≥ 2` ending in `1` is the negative
part `β⁻(N)` of some base phi expansion: for every Bergman set
`T ⊆ [-2n, -1]` containing `-2n` there are `N` and its expansion `S` with
`S ∩ (-∞, 0) = T`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 9 (`integers-2024-A24-thm-9`). -/
public theorem_wanted basePhi_negative_parts_surject (n : ℕ) (hn : 1 ≤ n) (T : Finset ℤ)
    (hT : T ⊆ Finset.Icc (-(2 * n : ℤ)) (-1)) (hlast : -(2 * n : ℤ) ∈ T)
    (hB : IsBergmanExpansion T) :
    ∃ N S, IsBasePhiExpansion N S ∧ S.filter (· < 0) = T

/-- Recursive Structure Theorem, `γ⁻` version, for `n ≥ 1`. The words
`γ⁻(N) = β⁻(N) (01)⁻¹` are stated through the negative parts: if `M` has
`β⁻(M)` of length `2j` then `γ⁻(M)` is `T ∩ [2-2j, -1]`, and
`γ⁻(N) = γ⁻(M) u` becomes `β⁻(N) = γ⁻(M) u 01`. Odd part:
(a) `γ⁻(M + L_{2n}) = γ⁻(M) 10`, `M ∈ Λ_{2n-1}`;
(b) `γ⁻(M + L_{2n+1}) = γ⁻(M) 0010`, `M ∈ Λ_{2n-2}`;
(c) `γ⁻(M + L_{2n+1}) = γ⁻(M) 00`, `M ∈ Λ_{2n-1}`.
Even part:
(a) `γ⁻(M + L_{2n+1}) = γ⁻(M) 00`, `M ∈ Λ_{2n}`;
(b) `γ⁻(M + L_{2n+2}) = γ⁻(M) 01`, `M ∈ Λ_{2n-1}`;
(c) `γ⁻(M + L_{2n+2}) = γ⁻(M) 01`, `M ∈ Λ_{2n}`.
In (B)(c) the record writes `γ⁻(N - L_{2n+1})` for `N ∈ Λ^{(c)}_{2n} = Λ_{2n} + L_{2n+2}`;
the shift `L_{2n+2}` of that definition is used (as printed, `n = 1`, `N = 10`:
`γ⁻(6) 01 = 0001` while `γ⁻(10) = 01`). The partition identities and the tables
are not included.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 10 (`integers-2024-A24-thm-10`). -/
public theorem_wanted basePhi_recursive_structure_gamma (n : ℕ) (hn : 1 ≤ n)
    (M : ℕ) (T S : Finset ℤ) (hT : IsBasePhiExpansion M T) :
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n)) S →
        S.filter (· < 0) = insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 2)) (lucasNumber (2 * n - 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (1 - 2 * n : ℤ) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (4 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (-2 * n - 2 : ℤ) (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 1)) S →
        S.filter (· < 0) = insert (-2 * n - 2 : ℤ) (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n) - 1) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S.filter (· < 0) = insert (-(2 * n : ℤ)) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0)))) ∧
    (M ∈ Finset.Icc (lucasNumber (2 * n)) (lucasNumber (2 * n + 1)) →
      IsBasePhiExpansion (M + lucasNumber (2 * n + 2)) S →
        S.filter (· < 0) = insert (-(2 * n : ℤ)) (insert (-2 * n - 2 : ℤ)
          (T.filter (fun i => (2 - 2 * n : ℤ) ≤ i ∧ i < 0))))

/-- The order of the `β⁻`-words on `Ξ_n = [L_{2n-1}+1, L_{2n+1}]`, `n ≥ 1`:
coding each `N ∈ Ξ_n` by `C(N) = Z⁻¹(γ⁻(N)) = ∑_{i ∈ β⁻(N)} F_{i+2n}` and
merging runs of equal consecutive codes (tridents), the codes in increasing
order of `N` are `F_{2n} - 1 + j F_{2n-2} mod F_{2n}`, `j = 0, …, F_{2n} - 1`:
the orbit of `F_{2n} - 1` under addition of `F_{2n-2}` in `ℤ/F_{2n}ℤ`. The code
function `c` is any function agreeing with `C` on base phi expansions.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 11 (`integers-2024-A24-thm-11`). -/
public theorem_wanted basePhi_negative_part_order_orbit (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℕ)
    (hc : ∀ N S, IsBasePhiExpansion N S →
      c N = ∑ i ∈ S.filter (· < 0), Nat.fib (i + 2 * n).toNat) :
    ((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·) =
      (List.range (Nat.fib (2 * n))).map
        (fun j => (Nat.fib (2 * n) - 1 + j * Nat.fib (2 * n - 2)) % Nat.fib (2 * n))


/-- The left end of the Lucas interval `Λ_m`, where `Λ_{2n} = [L_{2n}, L_{2n+1}]` and
`Λ_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]`: it is `L_m` for even `m` and `L_m + 1` for odd `m`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3 (Lucas intervals). -/
def lucasIntervalLo (m : ℕ) : ℕ := if Even m then lucasNumber m else lucasNumber m + 1

/-- The right end of the Lucas interval `Λ_m`: `L_{m+1}` for even `m` and `L_{m+1} - 1` for
odd `m`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3 (Lucas intervals). -/
def lucasIntervalHi (m : ℕ) : ℕ := if Even m then lucasNumber (m + 1) else lucasNumber (m + 1) - 1

/-- `Λ_3 = [5, 6]`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_three : lucasIntervalLo 3 = 5 ∧ lucasIntervalHi 3 = 6 := by decide

/-- `Λ_4 = [7, 11]`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_four : lucasIntervalLo 4 = 7 ∧ lucasIntervalHi 4 = 11 := by decide

/-- `Λ_5 = [12, 17]`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 3. -/
theorem lucasInterval_five : lucasIntervalLo 5 = 12 ∧ lucasIntervalHi 5 = 17 := by decide

/-- `IsLucasTiling a b P`: the translated Lucas intervals `Λ_k + t`, `(k, t) ∈ P`, taken in
the order of `P`, are adjacent and their union is `[a, b]`. The first starts at `a`, each next
one starts right after the previous one ends, and the last ends at `b` (for `P = []` the
interval `[a, b]` is empty, `a = b + 1`).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4 ("a union of adjacent translations" of Lucas intervals). -/
def IsLucasTiling : ℕ → ℕ → List (ℕ × ℕ) → Prop
  | a, b, [] => a = b + 1
  | a, b, p :: P => lucasIntervalLo p.1 + p.2 = a ∧ IsLucasTiling (lucasIntervalHi p.1 + p.2 + 1) b P

/-- The empty list tiles exactly the empty interval `[b + 1, b]`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem isLucasTiling_nil (a b : ℕ) : IsLucasTiling a b [] ↔ a = b + 1 := Iff.rfl

/-- A tiling starts with a translated interval that begins at `a`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem isLucasTiling_cons (a b : ℕ) (p : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    IsLucasTiling a b (p :: P) ↔
      lucasIntervalLo p.1 + p.2 = a ∧ IsLucasTiling (lucasIntervalHi p.1 + p.2 + 1) b P :=
  Iff.rfl

/-- The canonical splitting of the Lucas interval `Λ_m` into translations `Λ_k + t` of
`Λ_3, Λ_4, Λ_5`, as the list of pairs `(k, t)` in increasing order. For `m ≤ 5` it is `Λ_m`
itself; for `m ≥ 6` it is obtained from the second Recursive Structure Theorem
`Λ_m = (Λ_{m-2} + L_{m-1}) ∪ (Λ_{m-3} + L_m) ∪ (Λ_{m-2} + L_m)` by splitting the three pieces
canonically (the paper's splittings of `Λ_6, Λ_7, Λ_8`, "continuing in this fashion"). Only
`m ≥ 3` is used.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4 (canonical splitting). -/
def canonicalLucasSplitting : ℕ → List (ℕ × ℕ)
  | m + 6 =>
      (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 5))) ++
        (canonicalLucasSplitting (m + 3)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) ++
        (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 6)))
  | m => [(m, 0)]

/-- For `m ≤ 5` the canonical splitting of `Λ_m` is `Λ_m` itself.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_of_lt_six (m : ℕ) (hm : m < 6) :
    canonicalLucasSplitting m = [(m, 0)] := by
  rcases m with _ | _ | _ | _ | _ | _ | m <;> first | rfl | omega

/-- The recursion of the canonical splitting.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_add_six (m : ℕ) :
    canonicalLucasSplitting (m + 6) =
      (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 5))) ++
        (canonicalLucasSplitting (m + 3)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) ++
        (canonicalLucasSplitting (m + 4)).map (fun p => (p.1, p.2 + lucasNumber (m + 6))) := by
  rw [canonicalLucasSplitting]

/-- `Λ_6 = [Λ_4 + L_5] ∪ [Λ_3 + L_6] ∪ [Λ_4 + L_6]`, with `L_5 = 11`, `L_6 = 18`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Section 4. -/
theorem canonicalLucasSplitting_six :
    canonicalLucasSplitting 6 = [(4, 11), (3, 18), (4, 18)] := by decide

/-- Theorem 4: for `n ≥ 3` the canonical splitting of `Λ_n` consists of adjacent translations
of `Λ_3, Λ_4, Λ_5` whose union is `Λ_n`, and its coding `C` (the list of indices) satisfies
`C(Λ_{2n+4}) = κⁿ(4)` and `C(Λ_{2n+5}) = κⁿ(5)` for `n ≥ 0`, where `κ` is the morphism
`3 ↦ 5, 4 ↦ 434, 5 ↦ 545` acting on words by `List.flatMap` (letters other than `3, 4` are
sent to `545`; only `3, 4, 5` occur). The canonical splitting is `canonicalLucasSplitting`,
built from the recursion of the paper's Section 4.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 4 (`integers-2024-A24-thm-4`). -/
public theorem_wanted lucasInterval_canonical_splitting_coding :
    (∀ n : ℕ, 3 ≤ n →
      (∀ p ∈ canonicalLucasSplitting n, p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) ∧
        IsLucasTiling (lucasIntervalLo n) (lucasIntervalHi n) (canonicalLucasSplitting n)) ∧
    ∀ n : ℕ,
      (canonicalLucasSplitting (2 * n + 4)).map Prod.fst =
          (List.flatMap (fun x : ℕ => if x = 3 then [5] else if x = 4 then [4, 3, 4]
            else [5, 4, 5]))^[n] [4] ∧
        (canonicalLucasSplitting (2 * n + 5)).map Prod.fst =
          (List.flatMap (fun x : ℕ => if x = 3 then [5] else if x = 4 then [4, 3, 4]
            else [5, 4, 5]))^[n] [5]

/-- Theorem 5: for `n ≥ 2` the interval `Ξ_n = Λ_{2n-1} ∪ Λ_{2n} = [L_{2n-1} + 1, L_{2n+1}]`
is a union of adjacent translations of `Λ_3, Λ_4, Λ_5`, namely the canonical splittings of
`Λ_{2n-1}` and `Λ_{2n}` in order (as in the paper's proof,
`C(Ξ_{n+2}) = C(Λ_{2n+3}) C(Λ_{2n+4})`), and for `n ≥ 0` its coding is
`C(Ξ_{n+2}) = δ(hⁿ(b))`, where `h` is the morphism `a ↦ aab, b ↦ ab` of the paper's
Equation (Fib3) and `δ` the decoration morphism `a ↦ 54, b ↦ 34`. Letters are the characters
`'a'`, `'b'`; any letter other than `'a'` is treated as `'b'`.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 5 (`integers-2024-A24-thm-5`). -/
public theorem_wanted xi_canonical_splitting_coding :
    (∀ n : ℕ, 2 ≤ n →
      (∀ p ∈ canonicalLucasSplitting (2 * n - 1) ++ canonicalLucasSplitting (2 * n),
          p.1 = 3 ∨ p.1 = 4 ∨ p.1 = 5) ∧
        IsLucasTiling (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n + 1))
          (canonicalLucasSplitting (2 * n - 1) ++ canonicalLucasSplitting (2 * n))) ∧
    ∀ n : ℕ,
      (canonicalLucasSplitting (2 * n + 3) ++ canonicalLucasSplitting (2 * n + 4)).map Prod.fst =
        ((List.flatMap (fun c : Char => if c = 'a' then ['a', 'a', 'b'] else ['a', 'b']))^[n]
          ['b']).flatMap (fun c : Char => if c = 'a' then [5, 4] else [3, 4])

/-- Lemma 8 (Trident splitting): for `n ≥ 1` the last number `L_{2n} - 1` of `Λ_{2n-1}` and the
first two numbers `L_{2n}`, `L_{2n} + 1` of `Λ_{2n}` form a trident, i.e. their negative parts
`β⁻` agree (the paper calls three consecutive numbers `N, N+1, N+2` a trident when
`β⁻(N) = β⁻(N+1) = β⁻(N+2)`).

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Lemma 8 (`integers-2024-A24-lem-8`). -/
public theorem_wanted basePhi_trident_splitting (n : ℕ) (hn : 1 ≤ n) (S₁ S₂ S₃ : Finset ℤ)
    (h₁ : IsBasePhiExpansion (lucasNumber (2 * n) - 1) S₁)
    (h₂ : IsBasePhiExpansion (lucasNumber (2 * n)) S₂)
    (h₃ : IsBasePhiExpansion (lucasNumber (2 * n) + 1) S₃) :
    S₁.filter (· < 0) = S₂.filter (· < 0) ∧ S₂.filter (· < 0) = S₃.filter (· < 0)

/-- Theorem 12: for `n ≥ 1` the permutation `Π^β_{2n}` (the codes `C(N) = Z⁻¹(γ⁻(N))` of the
`N ∈ Ξ_n` in increasing order, tridents merged, as in Theorem 11) is the order in which the
first `F_{2n}` iterates of the rotation `z ↦ exp(2πi(z - φ))` occur on the circle: listing it
as `k - 1` for the iterates `k = 1, …, F_{2n}`, the iterate angles `{-kφ}` increase, i.e. the
fractional parts `{kφ}` decrease. This is the reading fixed by the paper's worked case
`n = 3`, where `Π^β_6 = 7 2 5 0 3 6 1 4`. The code function `c` is any function agreeing with
`C` on base phi expansions.

Source: F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24
(2024), Article A24, Theorem 12 (`integers-2024-A24-thm-12`). -/
public theorem_wanted basePhi_negative_part_order_rotation (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℕ)
    (hc : ∀ N S, IsBasePhiExpansion N S →
      c N = ∑ i ∈ S.filter (· < 0), Nat.fib (i + 2 * n).toNat) :
    (((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·)).Perm (List.range (Nat.fib (2 * n))) ∧
      (((List.range' (lucasNumber (2 * n - 1) + 1) (lucasNumber (2 * n))).map c).destutter
        (· ≠ ·)).Pairwise
          (fun i j => Int.fract (((j : ℝ) + 1) * φ) < Int.fract (((i : ℝ) + 1) * φ))

end

end MetaMathlibExt
