/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-!
# Domination polynomial of the rook graph

A placement is a finset of cells in `Fin n × Fin m`. We count the
`k`-rook placements that dominate the rook graph
(`rookDominatingCount`, Mertens' `d_{R_{n,m}}(k)`), the placements
meeting every row and every column (`rookCoverCount`, Mertens'
`E_{n,m}(k)`), and the rook domination polynomial
(`rookDominationPolynomial`), and prove Mertens' formulas for them.

By `SimpleGraph.rookGraph_isDominating_iff_or`, a placement dominates
exactly when it meets every row or every column. Grouping placements
by their sets of occupied rows and columns gives the recursions of
Theorems 1 and 2 and the high-density formula of Corollary 3. For the
polynomial, inclusion–exclusion over sets of forbidden rows and columns
evaluates the generating polynomials of the placements meeting every
column, every row, or both, which gives Theorem 4 and Corollary 5.

## Main results

* `card_powersetCard_filter_image_eq`: the `k`-placements with
  occupied rows `R` and occupied columns `C` are counted by
  `rookCoverCount R.card C.card k`.
* `rookDominatingCount_eq_choose_sub_sum_rookCoverCount`,
  `rookCoverCount_eq_choose_sub_sum_rookCoverCount`: Theorems 1 and 2.
* `rookDominatingCount_eq_choose_sub_mul_choose`: Corollary 3.
* `sum_pow_card_filter_image_fst_eq_univ`,
  `sum_pow_card_filter_image_snd_eq_univ`,
  `sum_pow_card_filter_image_eq_univ`: the generating polynomials of
  the placements on a finite board `α × β` meeting every row, meeting
  every column, and meeting both.
* `sum_rookCoverCount_mul_X_pow`: the generating polynomial of
  `rookCoverCount`.
* `rookDominationPolynomial_eq`,
  `rookDominationPolynomial_eq_symmetric`: Theorem 4 and Corollary 5.

## References

* Stephan Mertens, "Domination Polynomial of the Rook Graph",
  *Journal of Integer Sequences* 27 (2024), Article 24.3.7
  (<https://cs.uwaterloo.ca/journals/JIS/VOL27/Mertens/mertens6.html>).
-/

@[expose] public section

open Finset

namespace MathlibExt.Combinatorics.SimpleGraph.RookDominationPolynomial

/-- The number of `k`-rook placements on an `n × m` board meeting
every row and every column (Mertens' `E_{n,m}(k)`). -/
def rookCoverCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s => (∀ i : Fin n, ∃ j : Fin m, (i, j) ∈ s) ∧
      ∀ j : Fin m, ∃ i : Fin n, (i, j) ∈ s)).card

/-- The number of dominating `k`-rook placements on an `n × m`
board (Mertens' `d_{R_{n,m}}(k)`), using the canonical
`SimpleGraph.IsDominating` predicate for `SimpleGraph.rookGraph`. -/
def rookDominatingCount (n m k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n × Fin m)).powersetCard k).filter
    (fun s : Finset (Fin n × Fin m) =>
      (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m)))).card

/-- The rook domination polynomial over `ℤ`, as the generating
polynomial of `rookDominatingCount`. -/
noncomputable def rookDominationPolynomial (n m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n * m + 1),
    Polynomial.C (rookDominatingCount n m k : ℤ) * Polynomial.X ^ k

/-! ### Occupied rows and columns -/

section Board

variable {α β : Type*}

/-- A placement meets every row exactly when its set of occupied rows
is everything. -/
private theorem image_fst_eq_univ_iff [Fintype α] [DecidableEq α]
    {s : Finset (α × β)} :
    s.image Prod.fst = univ ↔ ∀ i : α, ∃ j : β, (i, j) ∈ s := by
  simp only [eq_univ_iff_forall, mem_image, Prod.exists, exists_and_right,
    exists_eq_right]

/-- A placement meets every column exactly when its set of occupied
columns is everything. -/
private theorem image_snd_eq_univ_iff [Fintype β] [DecidableEq β]
    {s : Finset (α × β)} :
    s.image Prod.snd = univ ↔ ∀ j : β, ∃ i : α, (i, j) ∈ s := by
  simp only [eq_univ_iff_forall, mem_image, Prod.exists, exists_eq_right]

/-- A placement avoids the rows in `L` and the columns in `K` exactly
when every row of `L` and every column of `K` is empty. -/
private theorem subset_compl_product_compl_iff [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] {s : Finset (α × β)}
    {L : Finset α} {K : Finset β} :
    s ⊆ Lᶜ ×ˢ Kᶜ ↔
      L ⊆ (s.image Prod.fst)ᶜ ∧ K ⊆ (s.image Prod.snd)ᶜ := by
  simp only [subset_iff, mem_product, mem_compl, mem_image, Prod.exists,
    exists_and_right, exists_eq_right, not_exists]
  constructor
  · intro h
    exact ⟨fun i hi j hij => (h hij).1 hi, fun j hj i hij => (h hij).2 hj⟩
  · intro h p hp
    exact ⟨fun hi => h.1 hi p.2 hp, fun hj => h.2 hj p.1 hp⟩

end Board

/-- A placement on the rook board dominates the rook graph exactly when
its occupied rows or its occupied columns are everything. -/
theorem isDominating_iff_image_eq_univ {n m : ℕ}
    {s : Finset (Fin n × Fin m)} :
    (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m)) ↔
      s.image Prod.fst = univ ∨ s.image Prod.snd = univ := by
  rw [SimpleGraph.rookGraph_isDominating_iff_or, image_fst_eq_univ_iff,
    image_snd_eq_univ_iff]

/-- `rookCoverCount` counts the `k`-placements whose occupied rows and
occupied columns are everything. -/
theorem rookCoverCount_eq_card_filter (n m k : ℕ) :
    rookCoverCount n m k =
      (((univ : Finset (Fin n × Fin m)).powersetCard k).filter
        (fun s => s.image Prod.fst = univ ∧
          s.image Prod.snd = univ)).card := by
  simp only [rookCoverCount, image_fst_eq_univ_iff, image_snd_eq_univ_iff]

/-! ### Grouping placements by occupied rows and columns -/

/-- The `k`-placements whose occupied rows are `R` and whose occupied
columns are `C` are counted by `rookCoverCount R.card C.card k`. -/
theorem card_powersetCard_filter_image_eq {n m : ℕ} (R : Finset (Fin n))
    (C : Finset (Fin m)) (k : ℕ) :
    (((univ : Finset (Fin n × Fin m)).powersetCard k).filter
        (fun s => s.image Prod.fst = R ∧ s.image Prod.snd = C)).card =
      rookCoverCount R.card C.card k := by
  set eR := (R.orderEmbOfFin rfl).toEmbedding
  set eC := (C.orderEmbOfFin rfl).toEmbedding
  have hR : univ.map eR = R := R.map_orderEmbOfFin_univ rfl
  have hC : univ.map eC = C := C.map_orderEmbOfFin_univ rfl
  have hfst : ∀ t : Finset (Fin R.card × Fin C.card),
      (t.map (eR.prodMap eC)).image Prod.fst = (t.image Prod.fst).map eR := by
    intro t
    rw [map_eq_image, map_eq_image, image_image, image_image]
    rfl
  have hsnd : ∀ t : Finset (Fin R.card × Fin C.card),
      (t.map (eR.prodMap eC)).image Prod.snd = (t.image Prod.snd).map eC := by
    intro t
    rw [map_eq_image, map_eq_image, image_image, image_image]
    rfl
  rw [rookCoverCount_eq_card_filter,
    ← card_map (mapEmbedding (eR.prodMap eC)).toEmbedding]
  congr 1
  ext s
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_map,
    RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · rintro ⟨hs, hsR, hsC⟩
    have hsub : s ⊆ univ.map (eR.prodMap eC) := by
      intro p hp
      have h1 : p.1 ∈ univ.map eR := by
        rw [hR, ← hsR]
        exact mem_image_of_mem _ hp
      have h2 : p.2 ∈ univ.map eC := by
        rw [hC, ← hsC]
        exact mem_image_of_mem _ hp
      obtain ⟨i, -, hi⟩ := mem_map.1 h1
      obtain ⟨j, -, hj⟩ := mem_map.1 h2
      exact mem_map.2 ⟨(i, j), mem_univ _, Prod.ext hi hj⟩
    obtain ⟨t, -, rfl⟩ := subset_map_iff.1 hsub
    refine ⟨t, ⟨?_, ?_, ?_⟩, rfl⟩
    · rwa [card_map] at hs
    · rw [← map_inj (f := eR), ← hfst, hsR, hR]
    · rw [← map_inj (f := eC), ← hsnd, hsC, hC]
  · rintro ⟨t, ⟨ht, htR, htC⟩, rfl⟩
    exact ⟨by rw [card_map, ht], by rw [hfst, htR, hR],
      by rw [hsnd, htC, hC]⟩

/-- Grouping the `k`-placements by their occupied rows and columns:
those whose occupied rows lie in `𝓡` and whose occupied columns lie
in `𝓒` are counted by a double sum of `rookCoverCount`. -/
theorem card_powersetCard_filter_image_mem {n m : ℕ}
    (𝓡 : Finset (Finset (Fin n))) (𝓒 : Finset (Finset (Fin m))) (k : ℕ) :
    (((univ : Finset (Fin n × Fin m)).powersetCard k).filter
        (fun s => s.image Prod.fst ∈ 𝓡 ∧ s.image Prod.snd ∈ 𝓒)).card =
      ∑ R ∈ 𝓡, ∑ C ∈ 𝓒, rookCoverCount R.card C.card k := by
  refine (card_eq_sum_card_fiberwise
    (f := fun s : Finset (Fin n × Fin m) =>
      (s.image Prod.fst, s.image Prod.snd)) (t := 𝓡 ×ˢ 𝓒)
    (fun s hs => mem_product.2 (mem_filter.1 hs).2)).trans ?_
  rw [sum_product]
  refine sum_congr rfl fun R hR => sum_congr rfl fun C hC => ?_
  rw [← card_powersetCard_filter_image_eq, filter_filter]
  congr 1
  refine filter_congr fun s _ => ?_
  rw [Prod.mk.injEq]
  constructor
  · exact fun h => h.2
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨hR, hC⟩, rfl, rfl⟩

/-- A `k`-placement on an `a × b` board with `a * b < k` cannot exist. -/
theorem rookCoverCount_eq_zero_of_lt {a b k : ℕ} (h : a * b < k) :
    rookCoverCount a b k = 0 := by
  rw [rookCoverCount, powersetCard_eq_empty.2, filter_empty, card_empty]
  rwa [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- If `k` exceeds both the number `(a - 1) * b` of cells off a row and
the number `a * (b - 1)` of cells off a column, every `k`-placement on
an `a × b` board meets every row and every column. -/
theorem rookCoverCount_eq_choose_of_lt {a b k : ℕ} (ha : (a - 1) * b < k)
    (hb : a * (b - 1) < k) :
    rookCoverCount a b k = (a * b).choose k := by
  rw [rookCoverCount, filter_true_of_mem, card_powersetCard, card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  intro s hs
  rw [mem_powersetCard] at hs
  constructor
  · intro i
    by_contra hi
    rw [not_exists] at hi
    have hsub : s ⊆ (univ.erase i) ×ˢ univ := by
      rintro ⟨i', j'⟩ hp
      refine mem_product.2 ⟨mem_erase.2 ⟨?_, mem_univ _⟩, mem_univ _⟩
      rintro rfl
      exact hi j' hp
    have hcard := card_le_card hsub
    rw [card_product, card_erase_of_mem (mem_univ _), card_univ, card_univ,
      Fintype.card_fin, Fintype.card_fin, hs.2] at hcard
    exact absurd ha (not_lt.2 hcard)
  · intro j
    by_contra hj
    rw [not_exists] at hj
    have hsub : s ⊆ univ ×ˢ (univ.erase j) := by
      rintro ⟨i', j'⟩ hp
      refine mem_product.2 ⟨mem_univ _, mem_erase.2 ⟨?_, mem_univ _⟩⟩
      rintro rfl
      exact hj i' hp
    have hcard := card_le_card hsub
    rw [card_product, card_erase_of_mem (mem_univ _), card_univ, card_univ,
      Fintype.card_fin, Fintype.card_fin, hs.2] at hcard
    exact absurd hb (not_lt.2 hcard)

/-- A sum over all row sets of a function of their size, indexed by the
number `r` of rows they miss. -/
private theorem sum_finset_fin (n : ℕ) (g : ℕ → ℤ) :
    ∑ R : Finset (Fin n), g R.card =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * g (n - r) := by
  rw [← powerset_univ, sum_powerset_apply_card, card_univ, Fintype.card_fin]
  refine (sum_range_reflect _ (n + 1)).symm.trans
    (sum_congr rfl fun r hr => ?_)
  rw [nsmul_eq_mul, add_tsub_cancel_right,
    Nat.choose_symm (Nat.lt_succ_iff.1 (mem_range.1 hr))]

/-- A sum over the row sets missing at least one row of a function of
their size, indexed by the number `r` of rows they miss. -/
private theorem sum_erase_univ_finset_fin (n : ℕ) (g : ℕ → ℤ) :
    ∑ R ∈ (univ : Finset (Finset (Fin n))).erase univ, g R.card =
      ∑ r ∈ Icc 1 n, (n.choose r : ℤ) * g (n - r) := by
  rw [sum_erase_eq_sub (mem_univ _), sum_finset_fin, card_univ,
    Fintype.card_fin, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot (by omega : 0 < n + 1), zero_add,
    Ico_add_one_right_eq_Icc, Nat.choose_zero_right, Nat.sub_zero,
    Nat.cast_one, one_mul, add_sub_cancel_left]

/-- The two-dimensional form of `sum_finset_fin`. -/
private theorem sum_finset_fin₂ (n m : ℕ) (g : ℕ → ℕ → ℤ) :
    ∑ R : Finset (Fin n), ∑ C : Finset (Fin m), g R.card C.card =
      ∑ r ∈ range (n + 1), ∑ c ∈ range (m + 1),
        (n.choose r : ℤ) * (m.choose c : ℤ) * g (n - r) (m - c) := by
  refine (sum_finset_fin n
    (fun a => ∑ C : Finset (Fin m), g a C.card)).trans
    (sum_congr rfl fun r _ => ?_)
  rw [sum_finset_fin m (g (n - r)), mul_sum]
  exact sum_congr rfl fun c _ => by ring

/-- The two-dimensional form of `sum_erase_univ_finset_fin`. -/
private theorem sum_erase_univ_finset_fin₂ (n m : ℕ) (g : ℕ → ℕ → ℤ) :
    ∑ R ∈ (univ : Finset (Finset (Fin n))).erase univ,
        ∑ C ∈ (univ : Finset (Finset (Fin m))).erase univ,
          g R.card C.card =
      ∑ r ∈ Icc 1 n, ∑ c ∈ Icc 1 m,
        (n.choose r : ℤ) * (m.choose c : ℤ) * g (n - r) (m - c) := by
  refine (sum_erase_univ_finset_fin n (fun a =>
    ∑ C ∈ (univ : Finset (Finset (Fin m))).erase univ, g a C.card)).trans
    (sum_congr rfl fun r _ => ?_)
  rw [sum_erase_univ_finset_fin m (g (n - r)), mul_sum]
  exact sum_congr rfl fun c _ => by ring

-- The positivity hypotheses `hn` and `hm` are not needed.
set_option linter.unusedVariables false in
/-- Mertens' Theorem 1, over `ℤ`: the dominating count is the
total placement count minus the placements whose nonempty rows
and columns form a smaller covered board.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 1 (`thm:R-E`).

Proves `Wanted` entry
`rookDominatingCount_eq_choose_sub_sum_rookCoverCount`. -/
theorem rookDominatingCount_eq_choose_sub_sum_rookCoverCount
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        ∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 m,
          (n.choose r : ℤ) * (m.choose c : ℤ) *
            (rookCoverCount (n - r) (m - c) k : ℤ) := by
  have hnon : (((univ : Finset (Fin n × Fin m)).powersetCard k).filter
      (fun s : Finset (Fin n × Fin m) =>
        ¬(SimpleGraph.rookGraph n m).IsDominating
        (s : Set (Fin n × Fin m)))).card =
      ∑ R ∈ (univ : Finset (Finset (Fin n))).erase univ,
        ∑ C ∈ (univ : Finset (Finset (Fin m))).erase univ,
          rookCoverCount R.card C.card k := by
    rw [← card_powersetCard_filter_image_mem]
    congr 1
    refine filter_congr fun s _ => ?_
    rw [isDominating_iff_image_eq_univ, not_or, mem_erase, mem_erase]
    simp only [ne_eq, mem_univ, and_true]
  have htot := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n × Fin m)).powersetCard k)
    (fun s : Finset (Fin n × Fin m) =>
      (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m)))
  rw [card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, hnon] at htot
  have hsum : ((∑ R ∈ (univ : Finset (Finset (Fin n))).erase univ,
      ∑ C ∈ (univ : Finset (Finset (Fin m))).erase univ,
        rookCoverCount R.card C.card k : ℕ) : ℤ) =
      ∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 m,
        (n.choose r : ℤ) * (m.choose c : ℤ) *
          (rookCoverCount (n - r) (m - c) k : ℤ) := by
    simp only [Nat.cast_sum]
    exact sum_erase_univ_finset_fin₂ n m
      (fun a b => (rookCoverCount a b k : ℤ))
  rw [rookDominatingCount, ← htot, Nat.cast_add, hsum, add_sub_cancel_right]

/-- Removing the `(a, b)` summand from a double sum. -/
private theorem sum_sum_mul_ite_eq_sub {s t : Finset ℕ} {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ t) (f : ℕ → ℕ → ℤ) :
    ∑ r ∈ s, ∑ c ∈ t, f r c * (if r = a ∧ c = b then 0 else 1) =
      ∑ r ∈ s, ∑ c ∈ t, f r c - f a b := by
  have h : ∀ r c, f r c * (if r = a ∧ c = b then 0 else 1) =
      f r c - if r = a then (if c = b then f r c else 0) else 0 := by
    intro r c
    by_cases hr : r = a <;> by_cases hc : c = b <;>
      simp only [hr, hc, and_self, and_true, and_false, ite_true, ite_false,
        mul_zero, mul_one, sub_self, sub_zero]
  simp only [h, sum_sub_distrib, sum_ite_irrel, sum_const_zero, sum_ite_eq',
    ha, hb, ite_true]

-- The positivity hypotheses `hn` and `hm` are not needed.
set_option linter.unusedVariables false in
/-- Mertens' Theorem 2, over `ℤ`: the recursion for the cover
count, with the `(0,0)` summand excluded.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 2 (`thm:E-recursion`).

Proves `Wanted` entry
`rookCoverCount_eq_choose_sub_sum_rookCoverCount`. -/
theorem rookCoverCount_eq_choose_sub_sum_rookCoverCount
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (rookCoverCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        ∑ r ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (m + 1),
          (n.choose r : ℤ) * (m.choose c : ℤ) *
            (rookCoverCount (n - r) (m - c) k : ℤ) *
            (if r = 0 ∧ c = 0 then 0 else 1) := by
  have htot := card_powersetCard_filter_image_mem
    (univ : Finset (Finset (Fin n))) (univ : Finset (Finset (Fin m))) k
  rw [filter_true_of_mem (fun s _ => ⟨mem_univ _, mem_univ _⟩),
    card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at htot
  rw [sum_sum_mul_ite_eq_sub (mem_range.2 n.succ_pos)
      (mem_range.2 m.succ_pos)
      (fun r c => (n.choose r : ℤ) * (m.choose c : ℤ) *
        (rookCoverCount (n - r) (m - c) k : ℤ)),
    htot, Nat.cast_sum]
  simp only [Nat.cast_sum]
  rw [sum_finset_fin₂ n m (fun a b => (rookCoverCount a b k : ℤ))]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    sub_sub_cancel]

/-- Mertens' Corollary 3, over `ℤ`: the high-density formula for
the dominating count.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Corollary 3 (`cor:high-density`).

Proves `Wanted` entry `rookDominatingCount_eq_choose_sub_mul_choose`. -/
theorem rookDominatingCount_eq_choose_sub_mul_choose
    (n m k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hk : (n : ℤ) * m - n - m - (min n m : ℤ) + 2 < k) :
    (rookDominatingCount n m k : ℤ) =
      ((n * m).choose k : ℤ) -
        (n : ℤ) * m * (((n - 1) * (m - 1)).choose k : ℤ) := by
  have hmin₁ : (min n m : ℤ) ≤ n := min_le_left _ _
  have hmin₂ : (min n m : ℤ) ≤ m := min_le_right _ _
  -- Placements missing a row, or missing a column, have fewer than `k`
  -- cells.
  have hrow : (n - 2) * (m - 1) < k := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      have : (min 1 m : ℤ) = 1 := min_eq_left (by exact_mod_cast hm)
      simp only [Nat.cast_one, one_mul, this] at hk
      rw [Nat.zero_mul]
      exact_mod_cast (by linarith : (0 : ℤ) < k)
    · zify [hn2, hm]
      nlinarith
  have hcol : (n - 1) * (m - 2) < k := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      have : (min n 1 : ℤ) = 1 := min_eq_right (by exact_mod_cast hn)
      simp only [Nat.cast_one, mul_one, this] at hk
      rw [Nat.mul_zero]
      exact_mod_cast (by linarith : (0 : ℤ) < k)
    · zify [hm2, hn]
      nlinarith
  rw [rookDominatingCount_eq_choose_sub_sum_rookCoverCount n m k hn hm,
    sum_eq_single_of_mem 1 (mem_Icc.2 ⟨le_rfl, hn⟩),
    sum_eq_single_of_mem 1 (mem_Icc.2 ⟨le_rfl, hm⟩),
    rookCoverCount_eq_choose_of_lt (by omega) (by omega)]
  · rw [Nat.choose_one_right, Nat.choose_one_right]
  · intro c hc hc1
    rw [rookCoverCount_eq_zero_of_lt, Nat.cast_zero, mul_zero]
    have := mem_Icc.1 hc
    exact lt_of_le_of_lt (Nat.mul_le_mul le_rfl (by omega)) hcol
  · intro r hr hr1
    refine sum_eq_zero fun c hc => ?_
    rw [rookCoverCount_eq_zero_of_lt, Nat.cast_zero, mul_zero]
    have := mem_Icc.1 hr
    have := mem_Icc.1 hc
    exact lt_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) hrow

/-! ### Generating polynomials -/

section GeneratingPolynomial

/-- Summing `x ^ #s` over the subsets `s` of a finset `t` gives
`(1 + x) ^ #t`. -/
private theorem sum_powerset_pow_card {R ι : Type*} [CommSemiring R] (x : R)
    (t : Finset ι) :
    ∑ s ∈ t.powerset, x ^ s.card = (1 + x) ^ t.card := by
  rw [add_comm, ← sum_pow_mul_eq_add_pow]
  simp only [one_pow, mul_one]

/-- Grouping a family of subsets of a finite type by cardinality: the
generating polynomial of the numbers of `k`-subsets with property `P`
is the sum of `x ^ #s` over the subsets `s` with property `P`. -/
private theorem sum_card_filter_powersetCard_mul_pow {R α : Type*}
    [CommSemiring R] [Fintype α] (P : Finset α → Prop) [DecidablePred P]
    (x : R) :
    ∑ k ∈ range (Fintype.card α + 1),
        ((((univ : Finset α).powersetCard k).filter P).card : R) * x ^ k =
      ∑ s ∈ univ.filter P, x ^ s.card := by
  refine ((sum_fiberwise_of_maps_to (g := Finset.card)
    (t := range (Fintype.card α + 1)) (fun s _ => ?_) _).symm.trans
      (sum_congr rfl fun k _ => ?_)).symm
  · exact mem_range.2 (Nat.lt_succ_of_le (card_le_univ s))
  · rw [sum_congr rfl fun s hs => by rw [(mem_filter.1 hs).2], sum_const,
      nsmul_eq_mul, filter_filter]
    congr 3
    ext s
    simp only [mem_filter, mem_powersetCard, mem_univ, subset_univ, true_and,
      and_comm]

variable {R : Type*} [CommRing R]
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

/-- The alternating sum over the subsets of the complement of `A`
detects `A = univ`. -/
private theorem sum_powerset_compl_neg_one_pow (A : Finset α) :
    ∑ L ∈ Aᶜ.powerset, (-1 : R) ^ L.card = if A = univ then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → R)
    (sum_powerset_neg_one_pow_card (x := Aᶜ))
  push_cast at h
  rw [h]
  exact if_congr (compl_eq_empty_iff A) rfl rfl

/-- Inclusion–exclusion over sets `L` of forbidden rows and `K` of
forbidden columns, with weights depending only on `#L` and `#K`. -/
private theorem sum_pow_card_mul_sum_powerset_compl (x : R)
    (a b : ℕ → R) :
    ∑ s : Finset (α × β), x ^ s.card *
        ((∑ L ∈ (s.image Prod.fst)ᶜ.powerset, a L.card) *
          ∑ K ∈ (s.image Prod.snd)ᶜ.powerset, b K.card) =
      ∑ ℓ ∈ range (Fintype.card α + 1), ∑ k ∈ range (Fintype.card β + 1),
        ((Fintype.card α).choose ℓ : R) * ((Fintype.card β).choose k : R) *
          a ℓ * b k *
            (1 + x) ^ ((Fintype.card α - ℓ) * (Fintype.card β - k)) := by
  have hinner : ∀ s : Finset (α × β),
      (∑ L ∈ (s.image Prod.fst)ᶜ.powerset, a L.card) *
          ∑ K ∈ (s.image Prod.snd)ᶜ.powerset, b K.card =
        ∑ L : Finset α, ∑ K : Finset β,
          if s ⊆ Lᶜ ×ˢ Kᶜ then a L.card * b K.card else 0 := by
    intro s
    rw [sum_mul_sum]
    simp only [subset_compl_product_compl_iff, ite_and,
      ← filter_subset_univ, sum_filter, sum_ite_irrel, sum_const_zero]
  calc _ = ∑ L : Finset α, ∑ K : Finset β, a L.card * b K.card *
        (1 + x) ^ ((Fintype.card α - L.card) *
          (Fintype.card β - K.card)) := by
        simp only [hinner, mul_sum, mul_ite, mul_zero]
        rw [sum_comm]
        refine sum_congr rfl fun L _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun K _ => ?_
        rw [← sum_filter, filter_subset_univ, ← card_compl, ← card_compl,
          ← card_product, ← sum_powerset_pow_card, mul_sum]
        exact sum_congr rfl fun s _ => mul_comm _ _
    _ = _ := by
        have hL := sum_powerset_apply_card (x := (univ : Finset α))
          (fun ℓ => ∑ K : Finset β, a ℓ * b K.card *
            (1 + x) ^ ((Fintype.card α - ℓ) * (Fintype.card β - K.card)))
        simp only [powerset_univ, card_univ] at hL
        rw [hL]
        refine sum_congr rfl fun ℓ _ => ?_
        have hK := sum_powerset_apply_card (x := (univ : Finset β))
          (fun k => a ℓ * b k *
            (1 + x) ^ ((Fintype.card α - ℓ) * (Fintype.card β - k)))
        simp only [powerset_univ, card_univ] at hK
        rw [hK, nsmul_eq_mul, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [nsmul_eq_mul]
        ring

omit [DecidableEq α] in
/-- The generating polynomial of the placements on a finite board
`α × β` meeting every column. -/
theorem sum_pow_card_filter_image_snd_eq_univ (x : R) :
    ∑ s ∈ univ.filter (fun s : Finset (α × β) => s.image Prod.snd = univ),
        x ^ s.card =
      ((1 + x) ^ Fintype.card α - 1) ^ Fintype.card β := by
  classical
  have h := sum_pow_card_mul_sum_powerset_compl (α := α) (β := β) x
    (fun ℓ => if ℓ = 0 then 1 else 0) (fun k => (-1) ^ k)
  simp only [card_eq_zero, sum_ite_eq', empty_mem_powerset, ite_true,
    sum_powerset_compl_neg_one_pow, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, sum_ite_irrel, sum_const_zero] at h
  rw [sum_filter, h, ite_eq_left (mem_range.2 (Nat.succ_pos _)), sub_eq_neg_add,
    add_pow]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, pow_mul]
  ring

omit [DecidableEq β] in
/-- The generating polynomial of the placements on a finite board
`α × β` meeting every row. -/
theorem sum_pow_card_filter_image_fst_eq_univ (x : R) :
    ∑ s ∈ univ.filter (fun s : Finset (α × β) => s.image Prod.fst = univ),
        x ^ s.card =
      ((1 + x) ^ Fintype.card β - 1) ^ Fintype.card α := by
  classical
  have h := sum_pow_card_mul_sum_powerset_compl (α := α) (β := β) x
    (fun ℓ => (-1) ^ ℓ) (fun k => if k = 0 then 1 else 0)
  simp only [card_eq_zero, sum_ite_eq', empty_mem_powerset, ite_true,
    sum_powerset_compl_neg_one_pow, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, sum_ite_irrel, sum_const_zero] at h
  rw [sum_filter, h, ite_eq_left (mem_range.2 (Nat.succ_pos _)), sub_eq_neg_add,
    add_pow]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, mul_comm (_ - ℓ),
    pow_mul]
  ring

/-- Reversing the order of summation over `range (N + 1)`. -/
private theorem sum_range_succ_reflect {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → M) :
    ∑ j ∈ range (N + 1), f j = ∑ j ∈ range (N + 1), f (N - j) := by
  have h := sum_range_reflect f (N + 1)
  rw [add_tsub_cancel_right] at h
  exact h.symm

private theorem neg_one_pow_sub {N j : ℕ} (h : j ≤ N) :
    (-1 : R) ^ (N - j) = (-1) ^ N * (-1) ^ j := by
  have hN : (-1 : R) ^ N = (-1) ^ (N - j) * (-1) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [hN, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    mul_one]

/-- The generating polynomial of the placements on a finite board
`α × β` meeting every row and every column. -/
theorem sum_pow_card_filter_image_eq_univ (x : R) :
    ∑ s ∈ univ.filter (fun s : Finset (α × β) =>
        s.image Prod.fst = univ ∧ s.image Prod.snd = univ), x ^ s.card =
      (-1) ^ (Fintype.card α + Fintype.card β) *
        ∑ ℓ ∈ range (Fintype.card α + 1), ∑ k ∈ range (Fintype.card β + 1),
          ((Fintype.card α).choose ℓ : R) * ((Fintype.card β).choose k : R) *
            (-1) ^ (k + ℓ) * (1 + x) ^ (k * ℓ) := by
  have h := sum_pow_card_mul_sum_powerset_compl (α := α) (β := β) x
    (fun ℓ => (-1) ^ ℓ) (fun k => (-1) ^ k)
  have hind : ∀ s : Finset (α × β), x ^ s.card *
      ((if s.image Prod.fst = univ then 1 else 0) *
        (if s.image Prod.snd = univ then 1 else 0)) =
      if s.image Prod.fst = univ ∧ s.image Prod.snd = univ then x ^ s.card
        else 0 := by
    intro s
    rw [ite_zero_mul_ite_zero, mul_one, mul_ite, mul_one, mul_zero]
  simp only [sum_powerset_compl_neg_one_pow, hind] at h
  rw [sum_filter, h, mul_sum, sum_range_succ_reflect (Fintype.card α)]
  refine sum_congr rfl fun ℓ hℓ => ?_
  rw [mul_sum, sum_range_succ_reflect (Fintype.card β)]
  refine sum_congr rfl fun k hk => ?_
  have hℓ' := Nat.lt_succ_iff.1 (mem_range.1 hℓ)
  have hk' := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [Nat.choose_symm hℓ', Nat.choose_symm hk', neg_one_pow_sub hℓ',
    neg_one_pow_sub hk', Nat.sub_sub_self hℓ', Nat.sub_sub_self hk']
  ring

/-- Summing the inner binomial expansion in
`sum_pow_card_filter_image_eq_univ`. -/
private theorem neg_one_pow_mul_sum_sum_eq (A B : ℕ) (y : R) :
    (-1) ^ (A + B) *
        ∑ ℓ ∈ range (A + 1), ∑ k ∈ range (B + 1),
          (A.choose ℓ : R) * (B.choose k : R) * (-1) ^ (k + ℓ) *
            y ^ (k * ℓ) =
      (-1) ^ B * ∑ k ∈ range (B + 1),
        (-1) ^ k * (B.choose k : R) * (y ^ k - 1) ^ A := by
  have h : ∀ k, (y ^ k - 1) ^ A = (-1) ^ A *
      ∑ ℓ ∈ range (A + 1), (A.choose ℓ : R) * (-1) ^ ℓ * y ^ (k * ℓ) := by
    intro k
    rw [show y ^ k - 1 = -1 * (-y ^ k + 1) by ring, mul_pow, add_pow]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [one_pow, mul_one, neg_pow, pow_mul]
    ring
  rw [sum_comm]
  simp only [h, mul_sum]
  refine sum_congr rfl fun k _ => sum_congr rfl fun ℓ _ => ?_
  ring

end GeneratingPolynomial

/-! ### The rook domination polynomial -/

/-- The generating polynomial of `rookCoverCount`. -/
theorem sum_rookCoverCount_mul_X_pow (n m : ℕ) :
    ∑ k ∈ Finset.range (n * m + 1),
        Polynomial.C (rookCoverCount n m k : ℤ) * Polynomial.X ^ k =
      (-1 : Polynomial ℤ) ^ (n + m) *
        ∑ ℓ ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1),
          Polynomial.C ((n.choose ℓ : ℤ) * (m.choose k : ℤ)) *
            (-1 : Polynomial ℤ) ^ (k + ℓ) *
            (1 + Polynomial.X) ^ (k * ℓ) := by
  have h := sum_card_filter_powersetCard_mul_pow (α := Fin n × Fin m)
    (fun s => s.image Prod.fst = univ ∧ s.image Prod.snd = univ)
    (Polynomial.X : Polynomial ℤ)
  rw [sum_pow_card_filter_image_eq_univ] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [rookCoverCount_eq_card_filter, map_mul, map_natCast]
  exact h

/-- The rook domination polynomial is the sum of the generating
polynomials of the placements meeting every column and meeting every
row, minus that of the placements meeting both. -/
private theorem rookDominationPolynomial_eq_add_sub (n m : ℕ) :
    rookDominationPolynomial n m =
      ((1 + Polynomial.X) ^ n - 1) ^ m + ((1 + Polynomial.X) ^ m - 1) ^ n -
        ∑ s ∈ univ.filter (fun s : Finset (Fin n × Fin m) =>
          s.image Prod.fst = univ ∧ s.image Prod.snd = univ),
          Polynomial.X ^ s.card := by
  have h := sum_card_filter_powersetCard_mul_pow (α := Fin n × Fin m)
    (fun s => (SimpleGraph.rookGraph n m).IsDominating
      (s : Set (Fin n × Fin m)))
    (Polynomial.X : Polynomial ℤ)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have hsplit : univ.filter (fun s : Finset (Fin n × Fin m) =>
      (SimpleGraph.rookGraph n m).IsDominating (s : Set (Fin n × Fin m))) =
      univ.filter (fun s : Finset (Fin n × Fin m) =>
        s.image Prod.fst = univ) ∪
      univ.filter (fun s : Finset (Fin n × Fin m) =>
        s.image Prod.snd = univ) := by
    rw [← filter_or]
    exact filter_congr fun s _ => isDominating_iff_image_eq_univ
  have hu := sum_union_inter
    (s₁ := univ.filter (fun s : Finset (Fin n × Fin m) =>
      s.image Prod.fst = univ))
    (s₂ := univ.filter (fun s : Finset (Fin n × Fin m) =>
      s.image Prod.snd = univ))
    (f := fun s => (Polynomial.X : Polynomial ℤ) ^ s.card)
  rw [← filter_and, ← hsplit, ← h, sum_pow_card_filter_image_fst_eq_univ,
    sum_pow_card_filter_image_snd_eq_univ, Fintype.card_fin,
    Fintype.card_fin] at hu
  rw [eq_sub_iff_add_eq, add_comm (((1 + Polynomial.X) ^ n - 1) ^ m), ← hu]
  simp only [rookDominationPolynomial, rookDominatingCount, map_natCast]

-- The positivity hypotheses `hn` and `hm` are not needed.
set_option linter.unusedVariables false in
/-- Mertens' Theorem 4: the single-sum form of the rook domination
polynomial.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Theorem 4 (`thm:domination-polynomial`).

Proves `Wanted` entry `rookDominationPolynomial_eq`. -/
theorem rookDominationPolynomial_eq
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    rookDominationPolynomial n m =
      ((1 + Polynomial.X) ^ n - 1) ^ m -
        (-1 : Polynomial ℤ) ^ m *
          ∑ k ∈ Finset.range m,
            (-1 : Polynomial ℤ) ^ k * Polynomial.C (m.choose k : ℤ) *
              ((1 + Polynomial.X) ^ k - 1) ^ n := by
  have h2 : (-1 : Polynomial ℤ) ^ m * (-1) ^ m = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [rookDominationPolynomial_eq_add_sub, sum_pow_card_filter_image_eq_univ,
    Fintype.card_fin, Fintype.card_fin, neg_one_pow_mul_sum_sum_eq,
    sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
  simp only [map_natCast]
  linear_combination (-((1 + Polynomial.X) ^ m - 1) ^ n) * h2

-- The positivity hypotheses `hn` and `hm` are not needed.
set_option linter.unusedVariables false in
/-- Mertens' Corollary 5: the symmetric form of the rook
domination polynomial.

Source: Stephan Mertens, "Domination Polynomial of the Rook
Graph", Corollary 5 (`cor:domination-polynomial`).

Proves `Wanted` entry `rookDominationPolynomial_eq_symmetric`. -/
theorem rookDominationPolynomial_eq_symmetric
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    rookDominationPolynomial n m =
      ((1 + Polynomial.X) ^ n - 1) ^ m +
          ((1 + Polynomial.X) ^ m - 1) ^ n -
        (-1 : Polynomial ℤ) ^ (n + m) *
          ∑ ℓ ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1),
            Polynomial.C ((n.choose ℓ : ℤ) * (m.choose k : ℤ)) *
              (-1 : Polynomial ℤ) ^ (k + ℓ) *
              (1 + Polynomial.X) ^ (k * ℓ) := by
  rw [rookDominationPolynomial_eq_add_sub, sum_pow_card_filter_image_eq_univ,
    Fintype.card_fin, Fintype.card_fin]
  simp only [map_mul, map_natCast]

end MathlibExt.Combinatorics.SimpleGraph.RookDominationPolynomial
