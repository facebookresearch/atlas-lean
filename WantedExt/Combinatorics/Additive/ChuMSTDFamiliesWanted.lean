/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chu et al.'s families of MSTD sets

Statements from Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a
New Family of MSTD Sets*, INTEGERS 24 (2024), Article A32.

Sets are written by their sequence of consecutive differences (Spohn's notation, Theorem 5's
notation paragraph): `(a₁ | g₁, …, g_r)` is `{a₁, a₁ + g₁, a₁ + g₁ + g₂, …}`, and
`M^k` is the difference sequence `1, 4, …, 4, 3` with `k` fours. A set `A` is MSTD
(sum-dominated) when `|A + A| > |A - A|`, balanced when `|A + A| = |A - A|`, and
difference-dominated when `|A + A| < |A - A|`; a family has one of these properties when
every member has it.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-- The finset of partial sums `(a | g₁, …, g_r) = {a, a + g₁, a + g₁ + g₂, …, a + g₁ + ⋯ + g_r}`.
When every gap `gᵢ` is positive (as in all uses below) its sorted sequence of consecutive
differences is `g₁, …, g_r`; a zero gap repeats a partial sum, which the finset records once.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public def setOfConsecutiveDifferences : ℤ → List ℕ → Finset ℤ
  | a, [] => {a}
  | a, g :: l => insert a (setOfConsecutiveDifferences (a + g) l)

/-- Prepending a difference `g` to `(a + g | l)` inserts `a` (the new minimum when `g > 0`).

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_cons (a : ℤ) (g : ℕ) (l : List ℕ) :
    setOfConsecutiveDifferences a (g :: l) = insert a (setOfConsecutiveDifferences (a + g) l) :=
  rfl

/-- The paper's example: `(0 | 1, 5, 1, 1, 9, 7) = {0, 1, 6, 7, 8, 17, 24}`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_example :
    setOfConsecutiveDifferences 0 [1, 5, 1, 1, 9, 7] = {0, 1, 6, 7, 8, 17, 24} := by
  decide

/-- The difference block `M^k = 1, 4, …, 4, 3` with `k` fours.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public def chuBlock (k : ℕ) : List ℕ :=
  1 :: List.replicate k 4 ++ [3]

/-- `M^1 = 1, 4, 3` and `M^2 = 1, 4, 4, 3`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public theorem chuBlock_one_two : chuBlock 1 = [1, 4, 3] ∧ chuBlock 2 = [1, 4, 4, 3] :=
  ⟨rfl, rfl⟩

/-- Theorem 1: for every positive integer `k`, `A = (0 | 1, 1, 2, M^k, M^{k+1}, 1, 1)` is
balanced: `|A + A| = |A - A|`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 1 (`integers-2024-A32-thm-1`). -/
public theorem_wanted chu_family_balanced {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card = (A - A).card

/-- Theorem 2: for every positive integer `k`,
`A = (0 | 1, 1, 2, M^k, M^{k+1}, M^{k+1}, 1, 1)` is difference-dominated:
`|A + A| < |A - A|`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 2 (`integers-2024-A32-thm-2`). -/
public theorem_wanted chu_family_difference_dominated {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card < (A - A).card

/-- Theorem 3: for every positive integer `k` and `M₁ ∈ {(1, 1, 2), (1, 1, 2, 1)}`,
`A = (0 | 1, 1, 2, M^k, M^{k+1}, M₁)` is MSTD: `|A - A| < |A + A|`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 3 (`integers-2024-A32-thm-3`). -/
public theorem_wanted chu_family_mstd_increasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ M₁)
    (A - A).card < (A + A).card

/-- Theorem 4: for every positive integer `k` and
`M₁ ∈ {(1, 1), (1, 1, 2), (1, 1, 2, 1)}`, `A = (0 | 1, 1, 2, M^{k+1}, M^k, M₁)` is MSTD:
`|A - A| < |A + A|`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 4 (`integers-2024-A32-thm-4`). -/
public theorem_wanted chu_family_mstd_decreasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1] ∨ M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock (k + 1) ++ chuBlock k ++ M₁)
    (A - A).card < (A + A).card

/-- The family of Section 3: `A = (0 | 1, 1, 2, M^k, …, M^k, …, 1, 1, 2, M^k, …, M^k, 1, 1, 2, 1)`,
where each run `M^k, …, M^k` has `l` copies and the block `1, 1, 2, M^k, …, M^k` is repeated `t`
times. (Each block spans `4(kl + l + 1)`, matching the bounds `t(kl + l + 1)` printed in
Lemmas 1-7.)

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public def chuFamilyKLT (k l t : ℕ) : Finset ℤ :=
  setOfConsecutiveDifferences 0
    ((List.replicate t ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten ++
      [1, 1, 2, 1])

/-- Smallest case: `k = l = t = 1` gives `(0 | 1, 1, 2, 1, 4, 3, 1, 1, 2, 1)`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public theorem chuFamilyKLT_one_one_one :
    chuFamilyKLT 1 1 1 = {0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17} := by
  decide

/-- Lemma 1: with `T = t(kl + l + 1)`, the positive differences of `A` include `4i` and
`1 + 4i` for `1 ≤ i ≤ 1 + T`, and `3 + 4i` for `0 ≤ i ≤ T`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 1 (`integers-2024-A32-lem-1`). -/
public theorem_wanted chuFamilyKLT_mem_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, 1 ≤ i → i ≤ 1 + t * (k * l + l + 1) →
        4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t ∧
          1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ t * (k * l + l + 1) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t

/-- Lemma 3: `(A - A)⁺` contains exactly `lt + t` elements of the form `6 + 4m`, `m ≥ 0`
(written `6 ≤ d ∧ d % 4 = 2`).

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 3 (`integers-2024-A32-lem-3`). -/
public theorem_wanted chuFamilyKLT_card_sub_six_add_four_mul {k l t : ℕ} (hk : 0 < k)
    (hl : 0 < l) (ht : 0 < t) :
    ((chuFamilyKLT k l t - chuFamilyKLT k l t).filter
        fun d => 6 ≤ d ∧ d % 4 = 2).card = l * t + t

/-- Lemma 4: with `T = t(kl + l + 1)`, `1 + 4i ∈ A` for `0 ≤ i ≤ 1 + T`, and `2 + 4T`,
`4 + 4T ∈ A`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 4 (`integers-2024-A32-lem-4`). -/
public theorem_wanted chuFamilyKLT_mem {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 1 + t * (k * l + l + 1) → 1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t) ∧
      2 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t ∧
      4 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t

/-- Lemma 5: with `T = t(kl + l + 1)`, `1 + 4i, 2 + 4i ∈ A + A` for `0 ≤ i ≤ 2 + 2T` and
`3 + 4i ∈ A + A` for `0 ≤ i ≤ 1 + 2T`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 5 (`integers-2024-A32-lem-5`). -/
public theorem_wanted chuFamilyKLT_mem_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 2 + 2 * (t * (k * l + l + 1)) →
        1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
          2 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ 1 + 2 * (t * (k * l + l + 1)) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t

/-- Lemma 6: `4 + (4k + 4)i + (4kl + 4l + 4)j ∈ A` for `0 ≤ i ≤ l` and `0 ≤ j ≤ t - 1`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 6 (`integers-2024-A32-lem-6`). -/
public theorem_wanted chuFamilyKLT_mem_block_starts {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
    4 + (4 * k + 4) * (i : ℤ) + (4 * k * l + 4 * l + 4) * (j : ℤ) ∈ chuFamilyKLT k l t

/-- Theorem 6: `|A - A| = 11 + 6klt + 8lt + 8t`.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 6 (`integers-2024-A32-thm-6`). -/
public theorem_wanted chuFamilyKLT_card_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (chuFamilyKLT k l t - chuFamilyKLT k l t).card = 11 + 6 * k * l * t + 8 * l * t + 8 * t

/-- Theorem 7: `|A + A| ≥ 11 + 6klt + 10lt + 8t`; with Theorem 6, `A` is MSTD.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 7 (`integers-2024-A32-thm-7`). -/
public theorem_wanted chuFamilyKLT_card_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    11 + 6 * k * l * t + 10 * l * t + 8 * t ≤ (chuFamilyKLT k l t + chuFamilyKLT k l t).card

/-- Lemma 7: with `P = 8kl + 8l + 8`, the sumset `A + A` contains `{0, 4, 8}` and the six
families `X₁ = {Pj + (4k + 4)i + 4}`, `X₂ = {Pj + (4k + 4)i + 8}`, `X₃ = {Pj + 4kl + 4l + 12}`,
`X₄ = {Pj + 4kl + 4l + (4k + 4)i + 8}`, `X₅ = {Pj + 4kl + 4l + (4k + 4)i + 12}` and
`X₆ = {Pj + 8kl + 8l + 16}` (`1 ≤ i ≤ l`, `0 ≤ j ≤ t - 1`), and the six families are pairwise
disjoint.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 7 (`integers-2024-A32-lem-7`). -/
public theorem_wanted chuFamilyKLT_add_supset_six_families {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) :
    let P : ℤ := 8 * k * l + 8 * l + 8
    let X₁ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 4
    let X₂ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 8
    let X₃ := (Finset.range t).image fun j : ℕ => P * j + (4 * k * l + 4 * l) + 12
    let X₄ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 8
    let X₅ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 12
    let X₆ := (Finset.range t).image fun j : ℕ => P * j + (8 * k * l + 8 * l) + 16
    {0, 4, 8} ∪ X₁ ∪ X₂ ∪ X₃ ∪ X₄ ∪ X₅ ∪ X₆ ⊆ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
      Pairwise fun a b : Fin 6 =>
        Disjoint (![X₁, X₂, X₃, X₄, X₅, X₆] a) (![X₁, X₂, X₃, X₄, X₅, X₆] b)

/-- Proposition 1: in the set of Lemma 2, the runs
`(R₁) = 1, 1, (2, M^k, …, M^k, 1, 1) × j` and `(R₃) = 2, (M^k, …, M^k, 1, 1, 2) × j`
(`j ∈ [1, t]`, each `M^k, …, M^k` with `l` copies, read from the paper's display) give the same
elements of `(A - A)⁺`, that is, the same set of run sums. The paper's `k, l, t ≥ 1` are not
needed.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Proposition 1
(`integers-2024-A32-prop-1`). -/
public theorem_wanted chuFamilyKLT_run_sums_R1_eq_R3 (k l t : ℕ) :
    (Finset.Icc 1 t).image (fun j =>
        ([1, 1] ++ (List.replicate j
          (2 :: (List.replicate l (chuBlock k)).flatten ++ [1, 1])).flatten).sum) =
      (Finset.Icc 1 t).image (fun j =>
        (2 :: (List.replicate j
          ((List.replicate l (chuBlock k)).flatten ++ [1, 1, 2])).flatten).sum)

end

end MetaMathlibExt
