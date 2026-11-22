/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- `2^{0, 1, 2} = {1, 2, 3}` in `ℤ`: the restricted sumset `h^A` of the paper (all sums of
`h` distinct elements of `A`) is `MetaMathlibExt.restrictedSumset`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1 (definition of `h^A`). -/
theorem restrictedSumset_two_zero_one_two :
    restrictedSumset 2 ({0, 1, 2} : Finset ℤ) = {1, 2, 3} := by
  decide

/-- The sumset `h^{(≥ r)}A`: all sums of `h` elements of `A` (with repetition) in which at least
`r` distinct elements occur, i.e. `∑_{i ∈ I} x_i a_i` with `|I| ≥ r`, `x_i ≥ 1`, `∑ x_i = h`.
For `r = 1` (and `h ≥ 1`) it is `h • A`; for `r = h` it is `restrictedSumset h A`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1, Definition 1. -/
def atLeastDistinctSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] (h r : ℕ)
    (A : Finset G) : Finset G :=
  ((A.sym h).filter fun s : Sym G h => r ≤ (s : Multiset G).toFinset.card).image
    fun s : Sym G h => (s : Multiset G).sum

/-- `3^{(≥ 2)}{0, 1, 2} = {1, 2, 3, 4, 5}` in `ℤ` (`0` and `6` need a single repeated term).

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1, Definition 1. -/
theorem atLeastDistinctSumset_three_two_zero_one_two :
    atLeastDistinctSumset 3 2 ({0, 1, 2} : Finset ℤ) = {1, 2, 3, 4, 5} := by
  decide

/-- Cauchy–Davenport for `h`-fold sumsets: for a nonempty `A ⊆ ℤ_p` and `h ≥ 1`,
`|hA| ≥ min(p, hk - h + 1)` with `k = |A|`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 1 (Cauchy–Davenport theorem) (`integers-2025-A12-thm-1`). -/
public theorem_wanted cauchy_davenport_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (h : ℕ) (hh : 1 ≤ h) :
    min p (h * A.card - h + 1) ≤ (h • A).card

/-- Dias da Silva–Hamidoune: for a nonempty `A ⊆ ℤ_p` with `|A| = k` and `1 ≤ h ≤ k`,
`|h^A| ≥ min(p, hk - h² + 1)`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 2 (Dias da Silva–Hamidoune theorem) (`integers-2025-A12-thm-2`). -/
public theorem_wanted dias_da_silva_hamidoune {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (h : ℕ) (hh : 1 ≤ h) (hhk : h ≤ A.card) :
    min p (h * A.card - h ^ 2 + 1) ≤ (restrictedSumset h A).card

/-- Vosper's theorem for `h`-fold sumsets: if `A ⊆ ℤ_p`, `|A| = k ≥ 2`, `h ≥ 2` and
`|hA| = hk - h + 1 ≤ p - 2`, then `A` is an arithmetic progression.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 3 (Vosper's theorem) (`integers-2025-A12-thm-3`). -/
public theorem_wanted vosper_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hk : 2 ≤ A.card) (h : ℕ) (hh : 2 ≤ h) (hcard : (h • A).card = h * A.card - h + 1)
    (hsmall : h * A.card - h + 1 ≤ p - 2) :
    (A : Set (ZMod p)).IsAPOfLength A.card

/-- Nathanson: if `A ⊆ ℤ`, `|A| = k ≥ 5`, `2 ≤ h ≤ k - 2` and `|h^A| = hk - h² + 1`, then `A` is
an arithmetic progression.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 4 (Nathanson) (`integers-2025-A12-thm-4`). -/
public theorem_wanted nathanson_restrictedSumset_inverse (A : Finset ℤ) (hk : 5 ≤ A.card)
    (h : ℕ) (hh : 2 ≤ h) (hhk : h ≤ A.card - 2)
    (hcard : (restrictedSumset h A).card = h * A.card - h ^ 2 + 1) :
    (A : Set ℤ).IsAPOfLength A.card

/-- Freiman's `3k - 4` theorem: let `A ⊆ ℤ` with `|A| = k ≥ 3`, `min A = 0` and `gcd(A) = 1`. If
`|2A| = 2k - 1 + b ≤ 3k - 4`, then `A` lies in an arithmetic progression of length at most
`k + b`. (`|2A| ≥ 2k - 1` always, so `b` ranges over `ℕ`.)

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 5 (Freiman's `3k - 4` theorem) (`integers-2025-A12-thm-5`). -/
public theorem_wanted freiman_three_k_sub_four (A : Finset ℤ) (hk : 3 ≤ A.card) (h0 : 0 ∈ A)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hgcd : A.gcd id = 1) (b : ℕ)
    (hcard : (2 • A).card = 2 * A.card - 1 + b) (hb : 2 * A.card - 1 + b ≤ 3 * A.card - 4) :
    ∃ (P : Set ℤ) (l : ℕ), l ≤ A.card + b ∧ P.IsAPOfLength l ∧ (A : Set ℤ) ⊆ P

/-- Plagne: for `1 ≤ k ≤ m` and `h ≥ 1`,
`μ(ℤ_m, k, h) = min{|hA| : A ⊆ ℤ_m, |A| = k} = min{(h⌈k/d⌉ - h + 1) d : d ∣ m}`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 6 (Plagne) (`integers-2025-A12-thm-6`). -/
public theorem_wanted plagne_min_nsmul_card (m k h : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hh : 1 ≤ h) :
    sInf ((fun A : Finset (ZMod m) => (h • A).card) '' {A | A.card = k}) =
      sInf ((fun d => (h * ((k + d - 1) / d) - h + 1) * d) '' (m.divisors : Set ℕ))

/-- Bajnok's lemma: for `1 ≤ t ≤ d - 1` and `ℓ ∈ ℤ_d` there is a `t`-element set
`L ⊆ ℤ_d` with `∑ L = ℓ`. (The corpus record runs on into the proof of Theorem 8; only the
lemma statement is formalized.)

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 1 (Bajnok) (`integers-2025-A12-lem-1`). -/
public theorem_wanted exists_card_eq_sum_eq_zmod (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d - 1)
    (ℓ : ZMod d) :
    ∃ L : Finset (ZMod d), L.card = t ∧ L.sum id = ℓ

/-- For a nonempty finite `A` in an abelian group with `1 ≤ r ≤ |A|` and `h ≥ r`,
`h^{(≥ r)}A = (h - r)A + r^A` (with `0A = {0}`).

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 2, equation (5) (`integers-2025-A12-lem-2`). -/
public theorem_wanted atLeastDistinctSumset_eq_nsmul_add_restrictedSumset {G : Type*}
    [AddCommGroup G] [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (r h : ℕ) (hr : 1 ≤ r)
    (hrk : r ≤ A.card) (hrh : r ≤ h) :
    atLeastDistinctSumset h r A = (h - r) • A + restrictedSumset r A

/-- For a nonempty `A ⊆ ℤ_p` with `|A| = k`, `1 ≤ r ≤ k` and `h ≥ r`,
`|h^{(≥ r)}A| ≥ min{p, h(k - 1) - r(r - 1) + 1}`; the bound is sharp: whenever
`h(k - 1) - r(r - 1) + 1 ≤ p` (and `k ≤ p`) some `k`-element set attains it.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 9, equation (6) (`integers-2025-A12-thm-9`). -/
public theorem_wanted atLeastDistinctSumset_card_ge_zmod {p : ℕ} (hp : p.Prime) :
    (∀ (A : Finset (ZMod p)), A.Nonempty → ∀ r h : ℕ, 1 ≤ r → r ≤ A.card → r ≤ h →
      min p (h * (A.card - 1) - r * (r - 1) + 1) ≤ (atLeastDistinctSumset h r A).card) ∧
    ∀ k r h : ℕ, 1 ≤ r → r ≤ k → k ≤ p → r ≤ h → h * (k - 1) - r * (r - 1) + 1 ≤ p →
      ∃ A : Finset (ZMod p), A.card = k ∧
        (atLeastDistinctSumset h r A).card = h * (k - 1) - r * (r - 1) + 1

/-- If `A ⊆ ℤ_p`, `|A| = k ≥ 2`, `1 ≤ r ≤ k`, `h ≥ r + 2` and
`|h^{(≥ r)}A| = h(k - 1) - r(r - 1) + 1 ≤ p - 2`, then `A` is an arithmetic progression.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 11 (`integers-2025-A12-thm-11`). -/
public theorem_wanted atLeastDistinctSumset_inverse_zmod {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 2 ≤ A.card) (r h : ℕ) (hr : 1 ≤ r) (hrk : r ≤ A.card)
    (hh : r + 2 ≤ h)
    (hcard : (atLeastDistinctSumset h r A).card = h * (A.card - 1) - r * (r - 1) + 1)
    (hsmall : h * (A.card - 1) - r * (r - 1) + 1 ≤ p - 2) :
    (A : Set (ZMod p)).IsAPOfLength A.card

/-- For a nonempty `A ⊆ ℤ` with `|A| = k`, `1 ≤ r ≤ k` and `h ≥ max{r, 2}`,
`|h^{(≥ r)}A| ≥ h(k - 1) - r(r - 1) + 1`; if equality holds and either `k ≥ 2` and `h ≥ r + 2`,
or `k ≥ 5`, `2 ≤ r ≤ k - 2` and `h ∈ {r, r + 1}`, then `A` is an arithmetic progression.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 12, equation (7) (`integers-2025-A12-thm-12`). -/
public theorem_wanted atLeastDistinctSumset_card_ge_int (A : Finset ℤ) (hA : A.Nonempty)
    (r h : ℕ) (hr : 1 ≤ r) (hrk : r ≤ A.card) (hrh : r ≤ h) (h2 : 2 ≤ h) :
    h * (A.card - 1) - r * (r - 1) + 1 ≤ (atLeastDistinctSumset h r A).card ∧
    ((atLeastDistinctSumset h r A).card = h * (A.card - 1) - r * (r - 1) + 1 →
      ((2 ≤ A.card ∧ r + 2 ≤ h) ∨
        (5 ≤ A.card ∧ 2 ≤ r ∧ r ≤ A.card - 2 ∧ (h = r ∨ h = r + 1))) →
      (A : Set ℤ).IsAPOfLength A.card)

/-- Lev: let `A ⊆ ℤ` with `|A| = k ≥ 3`, `min A = 0` and `gcd(A) = 1`. Then for `h ≥ 2`,
`|hA| ≥ |(h - 1)A| + min{max A, h(k - 2) + 1}`.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 13 (Lev) (`integers-2025-A12-thm-13`). -/
public theorem_wanted lev_nsmul_card_ge (A : Finset ℤ) (hk : 3 ≤ A.card) (h0 : 0 ∈ A)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hgcd : A.gcd id = 1) (h : ℕ) (hh : 2 ≤ h) :
    (((h - 1) • A).card : ℤ) + min (A.max' ⟨0, h0⟩) ((h : ℤ) * (A.card - 2) + 1) ≤
      ((h • A).card : ℤ)

end

end MetaMathlibExt
