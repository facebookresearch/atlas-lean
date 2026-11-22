/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Order.Group.Defs

/-!
# The sumset of sets of size `k`

Statements from Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26
(2026), Article A31.

The definitions of `R_G(h, k)` and of the trivial elements of `hA` are taken from the
arXiv version of the paper (arXiv:2505.07679v2, Section 1, Notation before
Definition 1.8 and Definition 1.8).  Throughout, `R_G(h, k)` is written out as the set
of cardinalities `(h • A).card` of `k`-element finsets `A`, and a `k`-element set
`a 0 < a 1 < ⋯ < a (k - 1)` is given by a function `a : ℕ → G` restricted to
`Finset.range k`.
-/

open scoped Pointwise

namespace MetaMathlibExt

@[expose] public section

/-- The trivial elements of the `h`-fold sumset of `{a 0, a 1, …, a (k - 1)}`: the
elements `h • a 0` and `(h - i) • a j + i • a (j + 1)` for `0 ≤ i ≤ h` and
`j + 1 < k`, the sums obtained by moving one summand at a time from each element to the
next.  When `a 0 < a 1 < ⋯ < a (k - 1)` in a linearly ordered additive group (the
paper's setting) these form an increasing list of `hk - h + 1` distinct sums; for an
arbitrary `a` they may coincide (e.g. `a = 0`, `h = k = 2` gives one element).  An
element of `h • A` outside this finset is called nontrivial.  `h • a 0` is listed
separately so that a one-element set has its single sum as a trivial element, as in the
paper's list; the empty set (`k = 0`) has no trivial elements.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial and nontrivial elements (arXiv:2505.07679v2,
Definition 1.8). -/
public def sumsetTrivialElements {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h k : ℕ) (a : ℕ → G) : Finset G :=
  if k = 0 then ∅
  else insert (h • a 0) ((Finset.range (k - 1) ×ˢ Finset.range (h + 1)).image
    fun p => (h - p.2) • a p.1 + p.2 • a (p.1 + 1))

/-- The empty set (`k = 0`) has no trivial elements.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_zero {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 0 a = ∅ := by
  simp [sumsetTrivialElements]

/-- A one-element set has its single `h`-fold sum as its only trivial element.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_one {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 1 a = {h • a 0} := by
  simp [sumsetTrivialElements]

/-- Each listed sum `(h - i) • a j + i • a (j + 1)` with `j + 1 < k` and `i ≤ h` is a
trivial element.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem adjacent_sum_mem_sumsetTrivialElements {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {h k i j : ℕ} (a : ℕ → G) (hj : j + 1 < k) (hi : i ≤ h) :
    (h - i) • a j + i • a (j + 1) ∈ sumsetTrivialElements h k a := by
  unfold sumsetTrivialElements
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, i), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_range]
  omega

/-- Membership in the trivial elements: `x` is trivial exactly when `k > 0` and
`x = h • a 0`, or `x = (h - i) • a j + i • a (j + 1)` for some `j + 1 < k` and `i ≤ h`.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem mem_sumsetTrivialElements_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {h k : ℕ} (a : ℕ → G) (x : G) :
    x ∈ sumsetTrivialElements h k a ↔
      (0 < k ∧ x = h • a 0) ∨
        ∃ j i : ℕ, j + 1 < k ∧ i ≤ h ∧ x = (h - i) • a j + i • a (j + 1) := by
  unfold sumsetTrivialElements
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro (hx | ⟨j, i, ⟨hj, hi⟩, rfl⟩)
    · exact Or.inl ⟨hk, hx⟩
    · exact Or.inr ⟨j, i, by omega, by omega, rfl⟩
  · rintro (⟨-, hx⟩ | ⟨j, i, hj, hi, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨j, i, ⟨by omega, by omega⟩, rfl⟩

/-- Dropping the largest element: for `a 0 < a 1 < ⋯ < a (k - 1)` in a linearly ordered
additive abelian group with `k > 1`, `A = {a 0, …, a (k - 1)}` and
`B = {a 0, …, a (k - 2)}`, we have `h • B ⊆ h • A`, and every nontrivial element of
`h • B` is a nontrivial element of `h • A`.  The paper takes `h > 1`; the statement
holds for every `h` (for `h = 0` there are no nontrivial elements).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Lemma 1 (`integers-2026-A31-lem-1`; arXiv:2505.07679v2, Lemma 3.2). -/
public theorem_wanted nsmul_sumset_erase_max_nontrivial
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 1 < k) (a : ℕ → G) (ha : ∀ i, i + 1 < k → a i < a (i + 1)) :
    h • (Finset.range (k - 1)).image a ⊆ h • (Finset.range k).image a ∧
      ∀ c ∈ h • (Finset.range (k - 1)).image a,
        c ∉ sumsetTrivialElements h (k - 1) a → c ∉ sumsetTrivialElements h k a

/-- Many nontrivial sums when the last gap is not a multiple of the one before: let
`k ≥ 4` and `0 = a 0 < a 1 < ⋯ < a (k - 3)` in a linearly ordered additive abelian
group, and let `a (k - 2) = a (k - 3) + b`, `a (k - 1) = a (k - 3) + b + c` with
`b, c > 0` and `c ≠ d • b` for every `d ≥ 1`.  Then `h • {a 0, …, a (k - 1)}` has at
least `h - 1` nontrivial elements.  The paper takes `h > 1`; the bound is vacuous for
`h ≤ 1`.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 1 (`integers-2026-A31-thm-1`; arXiv:2505.07679v2,
Theorem 3.3). -/
public theorem_wanted nontrivial_sumset_card_of_last_gap_ne_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b c : G) (hb : 0 < b) (hc : 0 < c)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + c)
    (hcb : ∀ d : ℕ, 1 ≤ d → c ≠ d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card

/-- Many nontrivial sums when the last gap is a proper multiple of the one before: let
`k ≥ 4` and `0 = a 0 < a 1 < ⋯ < a (k - 3)` in a linearly ordered additive abelian
group, and let `a (k - 2) = a (k - 3) + b`, `a (k - 1) = a (k - 3) + b + d • b` with
`b > 0` and `d > 1`.  Then `h • {a 0, …, a (k - 1)}` has at least `h - 1` nontrivial
elements.  The paper's `c` is written as `d • b` (its positivity follows).  The paper
takes `h > 1`; the bound is vacuous for `h ≤ 1`.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 2 (`integers-2026-A31-thm-2`; arXiv:2505.07679v2,
Theorem 3.4). -/
public theorem_wanted nontrivial_sumset_card_of_last_gap_eq_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b : G) (hb : 0 < b) (d : ℕ) (hd : 1 < d)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card

/-- Equal last two gaps: let `k ≥ 4` and `0 = a 0 < a 1 < ⋯ < a (k - 1)` in a linearly
ordered additive abelian group with `a (k - 1) - a (k - 2) = a (k - 2) - a (k - 3)`
(the paper's `b_{k-2} = b_{k-3}` for `A = {0, a, a + b₁, …, a + b₁ + ⋯ + b_{k-2}}`).
Then either `A = {a 0, …, a (k - 1)}` is the arithmetic progression
`a i = i • a 1`, or `h • B`, for `B = {a 0, …, a (k - 2)}`, has at least `h - 1`
nontrivial elements.  The paper takes `h > 1`; the second alternative is vacuous for
`h ≤ 1`.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 3 (`integers-2026-A31-thm-3`; arXiv:2505.07679v2,
Theorem 3.5). -/
public theorem_wanted arithProg_or_nontrivial_sumset_card_of_last_gaps_eq
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 < k → a i < a (i + 1))
    (hgap : a (k - 1) - a (k - 2) = a (k - 2) - a (k - 3)) :
    (∀ i < k, a i = i • a 1) ∨
      h - 1 ≤ (h • (Finset.range (k - 1)).image a \
        sumsetTrivialElements h (k - 1) a).card

/-- A missing interval of sumset sizes: in a torsion-free additive abelian group, for
`k ≥ 4` no `k`-element set `A` has `hk - h + 2 ≤ |h • A| ≤ hk - 1`, i.e.
`R_G(h, k) ∩ [hk - h + 2, hk - 1] = ∅`.  Stated for every `h : ℕ` (the interval is
empty for `h ≤ 1`).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 4 (`integers-2026-A31-thm-4`; arXiv:2505.07679v2,
Theorem 3.6). -/
public theorem_wanted card_nsmul_notMem_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉ Set.Icc (h * k - h + 2) (h * k - 1)

/-- The sumset sizes in `[hk - h + 1, hk]`: in a nontrivial torsion-free additive
abelian group, for `k ≥ 4` and `h ≥ 1`,
`R_G(h, k) ∩ [hk - h + 1, hk] = {hk - h + 1, hk}`.  Added hypotheses: `G` nontrivial
(otherwise there is no `k`-element set and `R_G(h, k) = ∅`) and `h ≥ 1` (for `h = 0`
the interval `[1, 0]` is empty while the right side is `{1, 0}`).  The arXiv version
states only the part `hk ∈ R_G(h, k)` (Corollary 3.8); the rest combines Theorem 4
with the arithmetic-progression size `hk - h + 1`.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Corollary 1 (`integers-2026-A31-cor-1`). -/
public theorem_wanted sumsetSizes_inter_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [Nontrivial G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (hh : 1 ≤ h) :
    {n : ℕ | ∃ A : Finset G, A.card = k ∧ (h • A).card = n} ∩
        Set.Icc (h * k - h + 1) (h * k) = {h * k - h + 1, h * k}

/-- An arithmetic progression with its second-to-last term moved: in a linearly
ordered additive abelian group, for `a > 0`, `k ≥ 3` and `h ≥ 1`, the set
`A = {0, a, 2a, …, (k - 2)a, ka}` has `|hA| = hk`, where `hA` is the `h`-fold sumset
`h • A`.  The paper leaves `h` unquantified; `h ≥ 1` is needed (`|0 • A| = 1`).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 5 (`integers-2026-A31-thm-5`). -/
public theorem_wanted card_nsmul_arithProg_skip_penultimate
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (a : G) (ha : 0 < a) (k h : ℕ) (hk : 3 ≤ k) (hh : 1 ≤ h) :
    (h • insert (k • a) ((Finset.range (k - 1)).image fun i => i • a)).card = h * k


/-- Rajagopal's family of missing intervals: in a torsion-free additive abelian group, for
`0 ≤ ℓ ≤ min(h, k) - 3` no `k`-element set `A` has
`hk - h + 1 + ℓh + 1 ≤ |h • A| ≤ hk - h + 1 + ℓh + (h - 2 - ℓ)`, i.e.
`R_G(h, k) ∩ ⋃_{ℓ=0}^{min(h,k)-3} [hk - h + 2 + ℓh, hk - h + 1 + ℓh + (h - 2 - ℓ)] = ∅`, stated
one `ℓ` at a time.  The journal statement does not repeat the group; torsion-freeness is the
setting of Theorem 4 and Corollary 1, of which this is the stated generalization (`ℓ = 0` is
Theorem 4, here also for `k = 3`).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 6 (`integers-2026-A31-thm-6`, journal version; credited to Rajagopal,
Theorem 1.3). -/
public theorem_wanted card_nsmul_notMem_Icc_add_mul_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k ℓ : ℕ) (hℓ : ℓ + 3 ≤ min h k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉
      Set.Icc (h * k - h + 1 + ℓ * h + 1) (h * k - h + 1 + ℓ * h + (h - 2 - ℓ))

end

end MetaMathlibExt
