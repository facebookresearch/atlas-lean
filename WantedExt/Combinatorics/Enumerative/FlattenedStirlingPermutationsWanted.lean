/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flattened Stirling permutations

Statements from Adam Buck, Jennifer Elder, Azia A. Figueroa, Pamela E. Harris,
Kimberly J. Harry, and Anthony Simpson, "Flattened Stirling Permutations",
*INTEGERS* 24 (2024), Article A104 (arXiv:2306.13034).

Stirling permutations of order `n` are MathlibExt's `IsStirlingPermutation n`
on words `Fin (2 * n) → ℕ`. A *run* of a word is a maximal contiguous weakly
increasing subword, so position `i` starts a run iff `i = 0` or the previous
letter is larger (`wordRunStart`). A word is *flattened* when the leading
letters of its runs are weakly increasing (`IsFlattenedWord`). For a
permutation the runs are increasing and the same predicates apply.

Type `B` set partitions of `[-n, n]` are Mathlib `Finpartition`s of
`Finset.Icc (-n) n` closed under negation with exactly one self-negative block
(`IsTypeBSetPartition`). The Dowling number `D_n` is MathlibExt's
`qrDowlingNumber` of the Whitney numbers `QRWhitney.whitneySecond 2 1 1`
(Whitney numbers of the second kind of the Dowling lattice over a group of
order `2`: `W(n+1, k+1) = W(n, k) + (2(k+1) + 1) W(n, k+1)`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Partition.Finpartition
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation
public import MathlibExt.NumberTheory.QRDowlingPolynomial

namespace MetaMathlibExt

@[expose] public section

/-- Position `i` of a word starts a run: `i = 0`, or the letter before it is
larger (runs are maximal contiguous weakly increasing subwords).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunStart {m : ℕ} (w : Fin m → ℕ) (i : Fin m) : Prop :=
  i.val = 0 ∨ ∃ j : Fin m, j.val + 1 = i.val ∧ w i < w j

instance {m : ℕ} (w : Fin m → ℕ) : DecidablePred (wordRunStart w) := fun _ => by
  unfold wordRunStart; infer_instance

/-- The number of runs of a word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunCount {m : ℕ} (w : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter (wordRunStart w)).card

/-- A word is flattened when the leading letters of its runs, read left to
right, are weakly increasing.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened). -/
def IsFlattenedWord {m : ℕ} (w : Fin m → ℕ) : Prop :=
  ∀ i j : Fin m, i < j → wordRunStart w i → wordRunStart w j → w i ≤ w j

instance {m : ℕ} (w : Fin m → ℕ) : Decidable (IsFlattenedWord w) := by
  unfold IsFlattenedWord; infer_instance

/-- `|flat(Q_n)|`: the number of flattened Stirling permutations of order `n`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingCount (n : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ | IsStirlingPermutation n w ∧ IsFlattenedWord w}

/-- `|flat_k(Q_n)|`: the number of flattened Stirling permutations of order `n`
with exactly `k` runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingRunCount (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ |
    IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = k}

/-- `f_{n,k}`: the number of flattened partitions of length `n` (permutations
of `[n]`, here of `Fin n`, whose runs have increasing leading terms) with
exactly `k` runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened
partitions, after Nabawanda, Rakotondrajao, and Bamunoba). -/
def flattenedPermRunCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    IsFlattenedWord (fun i => (σ i : ℕ)) ∧ wordRunCount (fun i => (σ i : ℕ)) = k).card

/-- A type `B` set partition of `[-n, n]`: a set partition closed under
negation of blocks with exactly one block equal to its own negative.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1. -/
def IsTypeBSetPartition {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Prop :=
  (∀ b ∈ P.parts, b.image (fun x => -x) ∈ P.parts) ∧
    ∃! b, b ∈ P.parts ∧ b.image (fun x => -x) = b

/-- The paper's example `112299388346677455 ∈ Q_9` is flattened, with the four
runs led by `1, 3, 3, 4`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem isFlattenedWord_example :
    IsFlattenedWord ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] ∧
      wordRunCount ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] = 4 := by
  decide

/-- The paper's example `123321445566778899 ∈ Q_9` is not flattened: its run
leaders are `1, 2, 1`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem not_isFlattenedWord_example :
    ¬ IsFlattenedWord ![1, 2, 3, 3, 2, 1, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] := by
  decide

/-- The one-block partition of `[-n, n]` is a type `B` set partition (its only
block is the zero-block).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1; characteristic
check of `IsTypeBSetPartition`. -/
theorem isTypeBSetPartition_indiscrete (n : ℕ) :
    IsTypeBSetPartition
      (Finpartition.indiscrete (a := Finset.Icc (-(n : ℤ)) n)
        (by rw [Finset.bot_eq_empty]; exact (Finset.nonempty_Icc.2 (by omega)).ne_empty)) := by
  refine ⟨?_, ⟨Finset.Icc (-(n : ℤ)) n, ⟨by simp, ?_⟩, ?_⟩⟩
  · intro b hb
    simp only [Finpartition.indiscrete_parts, Finset.mem_singleton] at hb ⊢
    subst hb
    ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · rintro b ⟨hb, -⟩
    simpa using hb

/-- Nabawanda, Rakotondrajao, and Bamunoba's recursion as quoted in the paper:
`f_{n,k} = ∑_{m=1}^{n-2} (C(n-1, m) - 1) f_{m,k-1}`, with `f_{n,1} = 1` for
`n ≥ 1` and `f_{n,k} = 0` for `k ≥ n ≥ 2`. The recursion is stated for
`k ≥ 2` (at `k = 1` the initial condition applies instead).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 1 (quoting
Nabawanda et al., Theorem 1). -/
public theorem_wanted flattenedPermRunCount_recursion :
    (∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
      (flattenedPermRunCount n k : ℤ) =
        ∑ m ∈ Finset.Icc 1 (n - 2),
          (((n - 1).choose m : ℤ) - 1) * flattenedPermRunCount m (k - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → flattenedPermRunCount n 1 = 1) ∧
    (∀ n k : ℕ, 2 ≤ n → n ≤ k → flattenedPermRunCount n k = 0)

/-- For `n ≥ 1`, the flattened Stirling permutations of order `n + 1` are in
bijection with the type `B` set partitions of `[-n, n]`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 2. -/
public theorem_wanted nonempty_flattenedStirling_equiv_typeBSetPartition (n : ℕ)
    (hn : 1 ≤ n) :
    Nonempty ({w : Fin (2 * (n + 1)) → ℕ //
        IsStirlingPermutation (n + 1) w ∧ IsFlattenedWord w} ≃
      {P : Finpartition (Finset.Icc (-(n : ℤ)) n) // IsTypeBSetPartition P})

/-- For `n ≥ 1`, `|flat(Q_{n+1})| = D_n`, the `n`-th Dowling number.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 1. -/
public theorem_wanted flattenedStirlingCount_succ_eq_dowling (n : ℕ) (hn : 1 ≤ n) :
    (flattenedStirlingCount (n + 1) : ℂ) = qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n

/-- The maximum number of runs of a flattened Stirling permutation of order
`n ≥ 1` is `⌈2n/3⌉`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 5. -/
public theorem_wanted isGreatest_flattenedStirling_runCount (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {r : ℕ | ∃ w : Fin (2 * n) → ℕ,
        IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = r}
      ⌈(2 * n : ℚ) / 3⌉₊

/-- For `n ≥ 1`, exactly one flattened Stirling permutation of order `n` has one
run.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 1. -/
public theorem_wanted flattenedStirlingRunCount_one (n : ℕ) (hn : 1 ≤ n) :
    flattenedStirlingRunCount n 1 = 1

/-- For `n ≥ 1`, `|flat_2(Q_{n+1})| = 2|flat_2(Q_n)| + 2n - 1`, with
`|flat_2(Q_1)| = 0`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 2. -/
public theorem_wanted flattenedStirlingRunCount_two_recursion :
    flattenedStirlingRunCount 1 2 = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        flattenedStirlingRunCount (n + 1) 2 = 2 * flattenedStirlingRunCount n 2 + 2 * n - 1

/-- For `n ≥ 1`, `|flat_2(Q_{n+1})| = 3(2ⁿ - 1) - 2n`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 2. -/
public theorem_wanted flattenedStirlingRunCount_two_closed (n : ℕ) (hn : 1 ≤ n) :
    (flattenedStirlingRunCount (n + 1) 2 : ℤ) = 3 * (2 ^ n - 1) - 2 * n

/-- For `n ≥ 0`,
`|flat(Q_{n+1})| = ∑_{i=0}^{n} C(n, i) ∑_{k=0}^{n-i} 2^{n-i-k} S(n-i, k)`,
with Mathlib's Stirling numbers of the second kind (`S(0, 0) = 1`).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 4. -/
public theorem_wanted flattenedStirlingCount_succ_eq_sum (n : ℕ) :
    flattenedStirlingCount (n + 1) =
      ∑ i ∈ Finset.range (n + 1), n.choose i *
        ∑ k ∈ Finset.range (n - i + 1), 2 ^ (n - i - k) * Nat.stirlingSecond (n - i) k

/-- For `n ≥ 1`,
`D_n = ∑_{i=0}^{n} C(n, i) ∑_{k=0}^{n-i} 2^{n-i-k} S(n-i, k)`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 3, formula. -/
public theorem_wanted dowling_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n =
      ((∑ i ∈ Finset.range (n + 1), n.choose i *
        ∑ k ∈ Finset.range (n - i + 1), 2 ^ (n - i - k) * Nat.stirlingSecond (n - i) k : ℕ) : ℂ)

/-- The Dowling numbers have exponential generating function
`exp(x + (exp(2x) - 1)/2)`, stated as a convergent series for every complex `x`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 3, generating
function. -/
public theorem_wanted hasSum_dowling_egf (x : ℂ) :
    HasSum (fun n : ℕ => qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n * x ^ n / n.factorial)
      (Complex.exp (x + (Complex.exp (2 * x) - 1) / 2))

/-- The map `h(S) = {|i| + 1 : i ∈ S}` from subsets of `[-n, n]` to subsets of
`[n + 1]`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
def typeBShift (S : Finset ℤ) : Finset ℕ :=
  S.image fun i => i.natAbs + 1

/-- The word `f(S) = s₁ s₁ s₂ s₂ ⋯ s_k s_k` for `S = {s₁ < ⋯ < s_k}` (empty for
`S = ∅`).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
def doubledWord (S : Finset ℕ) : List ℕ :=
  (S.sort (· ≤ ·)).flatMap fun s => [s, s]

/-- The word `g(S) = s₁ s₂ s₂ ⋯ s_k s_k s₁` for `S = {s₁ < ⋯ < s_k}` (empty for
`S = ∅`).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
def wrappedWord (S : Finset ℕ) : List ℕ :=
  match S.sort (· ≤ ·) with
  | [] => []
  | s :: t => s :: t.flatMap (fun x => [x, x]) ++ [s]

/-- `h` on a small set: `h({-2, 0, 1}) = {1, 2, 3}`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
theorem typeBShift_example : typeBShift {-2, 0, 1} = {1, 2, 3} := by
  decide

/-- `f({s}) = s s`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem doubledWord_singleton (s : ℕ) : doubledWord {s} = [s, s] := by
  simp [doubledWord]

/-- `f(S)` has length `2|S|`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem length_doubledWord (S : Finset ℕ) : (doubledWord S).length = 2 * S.card := by
  simp [doubledWord, List.length_flatMap, mul_comm]

/-- `g(∅)` is the empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_empty : wrappedWord ∅ = [] := by
  simp [wrappedWord]

/-- `g({s}) = s s`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_singleton (s : ℕ) : wrappedWord {s} = [s, s] := by
  simp [wrappedWord]

/-- `g(S)` has length `2|S|`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem length_wrappedWord (S : Finset ℕ) : (wrappedWord S).length = 2 * S.card := by
  rw [← Finset.length_sort (· ≤ ·) (s := S)]
  unfold wrappedWord
  split <;> simp_all [List.length_flatMap]
  omega

/-- Adler's canonical labels of the nonzero blocks of a type `B` set partition of
`[-n, n]` (Notation 2.3): the positive `p ≤ n` that are the least positive element of
their block `P.part p` and smaller than the magnitude of every negative element of that
block.  From each block pair this keeps exactly the block containing the least
magnitude as a positive element (step 1), labelled by its least positive element;
sorting the labels orders the kept blocks `β₁, …, β_m` (step 3).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3 (arXiv:2306.13034). -/
def adlerBlockLabels {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Finset ℤ :=
  (Finset.Icc 1 (n : ℤ)).filter fun p =>
    ∀ q ∈ P.part p, (0 < q → p ≤ q) ∧ (q < 0 → p < -q)

/-- The labels of Adler's kept blocks are positive and at most `n`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3. -/
theorem adlerBlockLabels_subset {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    adlerBlockLabels P ⊆ Finset.Icc 1 (n : ℤ) :=
  Finset.filter_subset _ _

/-- The word `φ(π) = g(h(P₀)) f(h(N₁)) g(h(P₁)) ⋯ f(h(N_m)) g(h(P_m))` of
Proposition 1, as a list: `P₀` is the set of nonnegative elements of the zero-block
`P.part 0`, and for the kept block `β_i = P.part p` (label `p`), `N_i` and `P_i` are
its negative and positive elements (Definition 2).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`), with
Definition 2. -/
def typeBFlattenedWordList {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    List ℕ :=
  wrappedWord (typeBShift ((P.part 0).filter (0 ≤ ·))) ++
    ((adlerBlockLabels P).sort (· ≤ ·)).flatMap fun p =>
      doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))

/-- The map `φ : Π^B_n → flat(Q_{n+1})` of Proposition 1, with the word read as a
function `Fin (2 * (n + 1)) → ℕ` (positions past the end of the list read `0`).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`). -/
def typeBFlattenedWord {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    Fin (2 * (n + 1)) → ℕ :=
  fun i => (typeBFlattenedWordList P).getD i 0

/-- `φ` is well defined: for every type `B` set partition `π` of `[-n, n]`, `φ(π)` is
a flattened Stirling permutation of order `n + 1`.  The record is truncated after
"let `π_i = N_i P_i` be as in"; the statement is completed from the arXiv text
(arXiv:2306.13034, Proposition 3.6).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1. -/
public theorem_wanted typeBFlattenedWord_mem_flattenedStirling {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    IsStirlingPermutation (n + 1) (typeBFlattenedWord P) ∧
      IsFlattenedWord (typeBFlattenedWord P)

/-- `φ : Π^B_n → flat(Q_{n+1})` is a bijection.  Stated for every `n ≥ 0`.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Theorem 3. -/
public theorem_wanted bijOn_typeBFlattenedWord (n : ℕ) :
    Set.BijOn (typeBFlattenedWord (n := n))
      {P : Finpartition (Finset.Icc (-(n : ℤ)) n) | IsTypeBSetPartition P}
      {w : Fin (2 * (n + 1)) → ℕ | IsStirlingPermutation (n + 1) w ∧ IsFlattenedWord w}

/-- Runs of `φ(π)`: for a type `B` set partition `π = π₀ | π₁ | ⋯ | π_m` of `[-n, n]`
with `π_i = N_i P_i`, the word `φ(π)` has
`1 + |{i ≥ 1 : |N_i| ≥ 1}| + |{i ≥ 0 : |P_i| ≥ 2}|` runs.  The paper states this for
`w ∈ flat(Q_{n+1})` and its partition `φ⁻¹(w)`; by Theorem 3 this is the same as the
statement for `w = φ(π)` over all `π`.  Blocks are indexed by Adler labels (label `0`
for the zero-block, whose nonnegative part is `P₀`).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 4. -/
public theorem_wanted wordRunCount_typeBFlattenedWord {n : ℕ}
    (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) (hP : IsTypeBSetPartition P) :
    wordRunCount (typeBFlattenedWord P) =
      1 + ((adlerBlockLabels P).filter fun p => ((P.part p).filter (· < 0)).Nonempty).card +
        ((insert 0 (adlerBlockLabels P)).filter fun p =>
          2 ≤ ((P.part p).filter (0 ≤ ·)).card).card

end

end MetaMathlibExt
