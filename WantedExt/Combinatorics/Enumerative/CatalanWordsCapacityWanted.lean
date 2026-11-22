/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.TrinomialCoefficient

namespace MetaMathlibExt

@[expose] public section

/-- Mansour and Shattuck's Lemma 5, identity (21): for `n ≥ 1` and `2 ≤ i ≤ n + 1`,
`∑_{m=0}^{n-i+1} C(n-m-1, i-2) F_{2m-1} = C(n-1, i-2) + ∑_{j=i}^{n} ∑_{m=0}^{n-j} C(n-m-2, j-2) F_{2m-1}`,
with the convention `F_{-1} = 1`, written as `if m = 0 then 1 else Nat.fib (2 * m - 1)`.
All natural subtractions are untruncated in the summation ranges.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem_wanted sum_choose_mul_fib_odd_eq_choose_add_sum (n i : ℕ) (hn : 1 ≤ n)
    (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    ∑ m ∈ Finset.range (n + 2 - i),
        (n - m - 1).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) =
      (n - 1).choose (i - 2) +
        ∑ j ∈ Finset.Icc i n, ∑ m ∈ Finset.range (n - j + 1),
          (n - m - 2).choose (j - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))

/-- Mansour and Shattuck's Lemma 5, identity (22): for `n ≥ 1`,
`F_{2n} = ∑_{j=1}^{n} ∑_{m=0}^{n-j} C(n-m-1, j-1) F_{2m-1}`, with `F_{-1} = 1` as in
`sum_choose_mul_fib_odd_eq_choose_add_sum`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 5 (`integers-2025-A5-lem-5`). -/
public theorem_wanted fib_two_mul_eq_sum_sum_choose_mul_fib_odd (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (2 * n) =
      ∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.range (n - j + 1),
        (n - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1))


open Polynomial LaurentPolynomial

/-- The capacity of a word `w = w₁ ⋯ wₙ` of positive integers viewed as a bargraph: the sum over
columns `i` of `min (max_{j<i} w_j) (max_{j>i} w_j) - w_i` (truncated at `0`), the number of water
cells above column `i`. Empty maxima are `0`, so the first and last columns hold no water.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of capacity. -/
public def wordCapacity {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n,
    (min ((Finset.univ.filter (· < i)).sup w) ((Finset.univ.filter (i < ·)).sup w) - w i)

/-- The area of a word, the sum of its letters (the area of its bargraph).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of the area statistic. -/
public def wordArea {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, w i

/-- The paper's Figure 1 example: `cap(122341123212323) = 10`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, Figure 1. -/
public theorem wordCapacity_figure_one :
    wordCapacity ![1, 2, 2, 3, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3] = 10 := by
  decide

/-- The set `𝒜ₙ` of Catalan words of length `n`: positive letters, first letter `1`, and
`w_{i+1} ≤ w_i + 1`. Letters of such words are at most `n`, so the ambient box `[1, n]ⁿ` loses
nothing (see `mem_catalanWords_iff`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of Catalan words. -/
public def catalanWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧ ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1

/-- The set `ℛₙ` of smooth words of length `n`: positive letters, first letter `1`, and
`|w_{i+1} - w_i| ≤ 1`. Letters of such words are at most `n`, so the ambient box
`[1, n]ⁿ` loses nothing (see `mem_smoothWords_iff`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public def smoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 n).filter fun w =>
    (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1

/-- Membership in `𝒜ₙ` is the definition of a Catalan word of length `n`: the box bound `n` on
the letters is automatic.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of Catalan words. -/
public theorem mem_catalanWords_iff {n : ℕ} (w : Fin n → ℕ) :
    w ∈ catalanWords n ↔ (∀ i, 1 ≤ w i) ∧ (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 := by
  simp only [catalanWords, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, h0, hg⟩
    exact ⟨fun i => (hb i).1, h0, hg⟩
  · rintro ⟨h1, h0, hg⟩
    have key : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k + 1 := by
      intro k
      induction k with
      | zero => intro hk; rw [h0 ⟨0, hk⟩ rfl]
      | succ k ih =>
        intro hk
        have h₁ := hg ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
        have h₂ := ih (by omega)
        omega
    refine ⟨fun i => ⟨h1 i, ?_⟩, h0, hg⟩
    have := key i.val i.isLt
    rw [Fin.eta] at this
    omega

/-- Membership in `ℛₙ` is the definition of a smooth word of length `n`: the box bound `n` on the
letters is automatic.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of smooth words. -/
public theorem mem_smoothWords_iff {n : ℕ} (w : Fin n → ℕ) :
    w ∈ smoothWords n ↔ (∀ i, 1 ≤ w i) ∧ (∀ i : Fin n, i.val = 0 → w i = 1) ∧
      ∀ i j : Fin n, j.val = i.val + 1 → w j ≤ w i + 1 ∧ w i ≤ w j + 1 := by
  simp only [smoothWords, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, h0, hg⟩
    exact ⟨fun i => (hb i).1, h0, hg⟩
  · rintro ⟨h1, h0, hg⟩
    have key : ∀ k (hk : k < n), w ⟨k, hk⟩ ≤ k + 1 := by
      intro k
      induction k with
      | zero => intro hk; rw [h0 ⟨0, hk⟩ rfl]
      | succ k ih =>
        intro hk
        have h₁ := (hg ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).1
        have h₂ := ih (by omega)
        omega
    refine ⟨fun i => ⟨h1 i, ?_⟩, h0, hg⟩
    have := key i.val i.isLt
    rw [Fin.eta] at this
    omega

/-- The set `ℛ*ₙ` of smooth words of length `n` with no two adjacent `1`s.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of restricted smooth words. -/
public def restrictedSmoothWords (n : ℕ) : Finset (Fin n → ℕ) :=
  (smoothWords n).filter fun w => ∀ i j : Fin n, j.val = i.val + 1 → ¬(w i = 1 ∧ w j = 1)

/-- The members of a set of words of length `n` whose last letter is `k` (empty when `n = 0`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒜_{n,i}`. -/
public def wordsEndingIn {n : ℕ} (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.filter fun w => ∃ i : Fin n, i.val + 1 = n ∧ w i = k

/-- The members of a set of words all of whose letters are at most `k`; applied to words ending in
`k` this gives those whose largest letter is `k` (the sets `ℬ_{n,i}` and `𝒮_{n,i}`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `ℬ_{n,i}`. -/
public def wordsBoundedBy {n : ℕ} (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.filter fun w => ∀ i : Fin n, w i ≤ k

/-- The capacity distribution `∑_{w ∈ S} q^{cap w}` of a finite set of words.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def capacityDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordCapacity w

/-- The area distribution `∑_{w ∈ S} q^{area w}` of a finite set of words.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def areaDist {n : ℕ} (S : Finset (Fin n → ℕ)) : ℤ[X] :=
  ∑ w ∈ S, X ^ wordArea w

/-- `a(n, i; q)`, the capacity distribution on Catalan words of length `n` ending in `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public noncomputable def catalanCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (catalanWords n) i)

/-- `b(n, i; q)`, the capacity distribution on Catalan words of length `n` ending in `i` whose
largest letter is `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `b(n, i; q)`. -/
public noncomputable def catalanMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (catalanWords n) i) i)

/-- `r(n, i; q)`, the capacity distribution on smooth words of length `n` ending in `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `r(n, i; q)`. -/
public noncomputable def smoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (smoothWords n) i)

/-- `s(n, i; q)`, the capacity distribution on smooth words of length `n` ending in `i` whose
largest letter is `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `s(n, i; q)`. -/
public noncomputable def smoothMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (smoothWords n) i) i)

/-- `r*(n, i; q)`, the capacity distribution on restricted smooth words of length `n` ending
in `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `r*(n, i; q)`. -/
public noncomputable def restrictedSmoothCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsEndingIn (restrictedSmoothWords n) i)

/-- `s*(n, i; q)`, the capacity distribution on restricted smooth words of length `n` ending in
`i` whose largest letter is `i`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `s*(n, i; q)`. -/
public noncomputable def restrictedSmoothMaxEndCapacityDist (n i : ℕ) : ℤ[X] :=
  capacityDist (wordsBoundedBy (wordsEndingIn (restrictedSmoothWords n) i) i)

/-- The set `𝒞_{m,j}` of words of length `m` over `[1, j]` ending in `j` (so with largest letter
`j`) with `w_{i+1} ≤ w_i + 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `𝒞_{m,j}`. -/
public def catalanGrowthWords (m j : ℕ) : Finset (Fin m → ℕ) :=
  wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    ∀ i k : Fin m, k.val = i.val + 1 → w k ≤ w i + 1) j

/-- `c(m, j, ℓ; q)`, the area distribution on the members of `𝒞_{m,j}` starting with `ℓ`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public noncomputable def catalanGrowthAreaDist (m j ℓ : ℕ) : ℤ[X] :=
  areaDist ((catalanGrowthWords m j).filter fun w => ∀ i : Fin m, i.val = 0 → w i = ℓ)

/-- `t(m, j; q)`, the area distribution on the set `𝒯_{m,j}` of words of length `m` over `[1, j]`
that begin and end with `j` and satisfy `|w_{i+1} - w_i| ≤ 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 3, definition of `𝒯_{m,j}` and
`t(m, j; q)`. -/
public noncomputable def smoothPlateauAreaDist (m j : ℕ) : ℤ[X] :=
  areaDist (wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    (∀ i : Fin m, i.val = 0 → w i = j) ∧
      ∀ i k : Fin m, k.val = i.val + 1 → w k ≤ w i + 1 ∧ w i ≤ w k + 1) j)

/-- A capacity distribution evaluated at `q = 1` counts its words.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `a(n, i; q)`. -/
public theorem capacityDist_eval_one {n : ℕ} (S : Finset (Fin n → ℕ)) :
    (capacityDist S).eval 1 = S.card := by
  simp [capacityDist, eval_finsetSum]

/-- An area distribution evaluated at `q = 1` counts its words.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 2, definition of `c(m, j, ℓ; q)`. -/
public theorem areaDist_eval_one {n : ℕ} (S : Finset (Fin n → ℕ)) :
    (areaDist S).eval 1 = S.card := by
  simp [areaDist, eval_finsetSum]

/-- Small cardinalities from the paper's examples: `|𝒜₄| = C₄ = 14`, `|ℛ₄| = |𝒜₄| - 1 = 13`, and
`|ℛ*₄| = G₃ = 7`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, examples. -/
public theorem card_catalanWords_four_smoothWords_four :
    (catalanWords 4).card = 14 ∧ (smoothWords 4).card = 13 ∧
      (restrictedSmoothWords 4).card = 7 := by
  decide

/-- Mansour and Shattuck's Lemma 1: for `m ≥ 2`, `j ≥ 1` and `ℓ ∈ [j]`,
`c(m, j, ℓ) = q^ℓ ∑_{i=1}^{ℓ+1} c(m-1, j, i)`, with `c(1, j, ℓ) = q^ℓ δ_{j,ℓ}`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 1 (`integers-2025-A5-lem-1`). -/
public theorem_wanted catalanGrowthAreaDist_succ (m j ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 1 ≤ ℓ)
    (hℓj : ℓ ≤ j) :
    catalanGrowthAreaDist m j ℓ =
        X ^ ℓ * ∑ i ∈ Finset.Icc 1 (ℓ + 1), catalanGrowthAreaDist (m - 1) j i ∧
      catalanGrowthAreaDist 1 j ℓ = X ^ ℓ * if j = ℓ then 1 else 0

/-- The polynomials `d_j(x; q)` of Lemma 3, as power series in `x` over `ℤ[q]`: `d₀ = 1`,
`d₁ = 1 - xq`, `d₂ = 1 - xq - xq²` and `d_j = (1 - xq^j) d_{j-1} - x² q^{2j-1} d_{j-3}` for `j ≥ 3`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3, recurrence (4). -/
public noncomputable def catalanGrowthDen : ℕ → PowerSeries ℤ[X]
  | 0 => 1
  | 1 => 1 - PowerSeries.C X * PowerSeries.X
  | 2 => 1 - PowerSeries.C X * PowerSeries.X - PowerSeries.C (X ^ 2) * PowerSeries.X
  | j + 3 => (1 - PowerSeries.C (X ^ (j + 3)) * PowerSeries.X) * catalanGrowthDen (j + 2) -
      PowerSeries.C (X ^ (2 * j + 5)) * PowerSeries.X ^ 2 * catalanGrowthDen j

/-- Every `d_j(x; q)` has constant term `1`, so `PowerSeries.invOfUnit (catalanGrowthDen j) 1`
is its inverse.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3, recurrence (4). -/
public theorem constantCoeff_catalanGrowthDen :
    ∀ j, PowerSeries.constantCoeff (catalanGrowthDen j) = 1
  | 0 => by simp [catalanGrowthDen]
  | 1 => by simp [catalanGrowthDen]
  | 2 => by simp [catalanGrowthDen]
  | j + 3 => by
    simp [catalanGrowthDen, constantCoeff_catalanGrowthDen (j + 2)]

/-- Mansour and Shattuck's Lemma 3, formula (5): for `1 ≤ i ≤ j`,
`C_{j,i}(x; q) = ∑_{n ≥ 1} c(n, j, i; q) xⁿ
  = x^{j-i+1} q^{C(j+1,2) - C(i,2)} d_{i-1}(x; q) / d_j(x; q)`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3 (`integers-2025-A5-lem-3`). -/
public theorem_wanted catalanGrowthAreaDist_genFun (j i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    PowerSeries.mk (fun n => catalanGrowthAreaDist n j i) =
      PowerSeries.C (X ^ ((j + 1).choose 2 - i.choose 2)) * PowerSeries.X ^ (j - i + 1) *
        catalanGrowthDen (i - 1) * PowerSeries.invOfUnit (catalanGrowthDen j) 1

/-- Mansour and Shattuck's Lemma 3, formula (6): for `j ≥ 1`,
`C_j(x; q) = ∑_{n ≥ 1} c(n, j; q) xⁿ
  = (1 / d_j(x; q)) ∑_{i=1}^{j} x^{j-i+1} q^{C(j+1,2) - C(i,2)} d_{i-1}(x; q)`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 3 (`integers-2025-A5-lem-3`). -/
public theorem_wanted catalanGrowthWords_areaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun n => areaDist (catalanGrowthWords n j)) =
      PowerSeries.invOfUnit (catalanGrowthDen j) 1 *
        ∑ i ∈ Finset.Icc 1 j,
          PowerSeries.C (X ^ ((j + 1).choose 2 - i.choose 2)) * PowerSeries.X ^ (j - i + 1) *
            catalanGrowthDen (i - 1)

/-- The substitution `f(x; q) ↦ f(q^j x; 1/q)` of Lemma 4, taking a power series in `x` over
`ℤ[q]` to one over `ℤ[q, q⁻¹]`: the coefficient of `xⁿ` becomes `q^{jn}` times the image of the old
coefficient under `q ↦ q⁻¹`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4. -/
public noncomputable def dilateInvertSeries (j : ℕ) (f : PowerSeries ℤ[X]) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n => T ((j * n : ℕ) : ℤ) * invert (toLaurent (PowerSeries.coeff n f))

/-- The substitution `f(x; q) ↦ f(q^j x; 1/q)` keeps a constant term `1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4. -/
public theorem constantCoeff_dilateInvertSeries (j : ℕ) (f : PowerSeries ℤ[X])
    (h : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (dilateInvertSeries j f) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, dilateInvertSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp

/-- Mansour and Shattuck's Lemma 4, formula (9): for `i ≥ 1`, `B_i(x; q) = ∑_{n ≥ i} b(n, i; q) xⁿ`
equals
`xⁱ / ∏_{j=1}^{i} (1 - x - (x / d_{j-1}(q^j x; 1/q))
  ∑_{m=1}^{j-1} x^{j-m} q^{j(j-m) + C(m,2) - C(j,2)} d_{m-1}(q^j x; 1/q))`, in power series over
`ℤ[q, q⁻¹]`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4 (`integers-2025-A5-lem-4`). -/
public theorem_wanted catalanMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (catalanMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.Icc 1 i,
        PowerSeries.invOfUnit (1 - PowerSeries.X -
          PowerSeries.X *
            PowerSeries.invOfUnit (dilateInvertSeries j (catalanGrowthDen (j - 1))) 1 *
            ∑ m ∈ Finset.Icc 1 (j - 1),
              PowerSeries.C (T (((j * (j - m) + m.choose 2 : ℕ) : ℤ) - (j.choose 2 : ℕ))) *
                PowerSeries.X ^ (j - m) * dilateInvertSeries j (catalanGrowthDen (m - 1))) 1

/-- Mansour and Shattuck's Lemma 2, recurrence (2): for `1 < i < n`,
`a(n,i) = b(n-1,i-1) + ∑_{j=i}^{n-1} a(n-1,j)
  + ∑_{m=1}^{n-i-1} ∑_{j=i}^{n-m-1} q^{mi} a(n-m-1,j) c(m,i-1;1/q)`, stated in `ℤ[q, q⁻¹]`
with `c(m, i-1; 1/q)` the image of `c(m, i-1)` under `q ↦ q⁻¹`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (catalanCapacityDist n i) =
      toLaurent (catalanMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ j ∈ Finset.Icc i (n - 1), toLaurent (catalanCapacityDist (n - 1) j) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1), ∑ j ∈ Finset.Icc i (n - m - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (catalanCapacityDist (n - m - 1) j) *
            invert (toLaurent (areaDist (catalanGrowthWords m (i - 1))))

/-- Mansour and Shattuck's Lemma 2, recurrence (3): for `1 < i < n`,
`b(n,i) = b(n-1,i) + b(n-1,i-1) + ∑_{m=1}^{n-i-1} q^{mi} b(n-m-1,i) c(m,i-1;1/q)`, in
`ℤ[q, q⁻¹]`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanMaxEndCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (catalanMaxEndCapacityDist n i) =
      toLaurent (catalanMaxEndCapacityDist (n - 1) i) +
        toLaurent (catalanMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (catalanMaxEndCapacityDist (n - m - 1) i) *
            invert (toLaurent (areaDist (catalanGrowthWords m (i - 1))))

/-- Mansour and Shattuck's Lemma 2, boundary values: `a(n, 1) = a(n - 1)` for `n ≥ 2`, and
`a(n, n) = b(n, 1) = b(n, n) = 1` for `n ≥ 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 2 (`integers-2025-A5-lem-2`). -/
public theorem_wanted catalanCapacityDist_boundary (n : ℕ) (hn : 1 ≤ n) :
    (2 ≤ n → catalanCapacityDist n 1 = capacityDist (catalanWords (n - 1))) ∧
      catalanCapacityDist n n = 1 ∧ catalanMaxEndCapacityDist n 1 = 1 ∧
        catalanMaxEndCapacityDist n n = 1

/-- Mansour and Shattuck's Corollary 3: with `C(x) = ∑ Cₙ xⁿ` the Catalan generating function,
`A_i(x; 1) = ∑_{n ≥ i} |𝒜_{n,i}| xⁿ = xⁱ C(x)ⁱ` for `i ≥ 1`, using `a(n, i; 1) = |𝒜_{n,i}|`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 3 (`integers-2025-A5-cor-3`). -/
public theorem_wanted catalanWordsEndingIn_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => ((wordsEndingIn (catalanWords n) i).card : ℤ)) =
      PowerSeries.X ^ i * PowerSeries.mk (fun n => (catalan n : ℤ)) ^ i

/-- Mansour and Shattuck's Theorem 2: the maximum capacity `deg a(n; q)` over `𝒜ₙ` is
`3 C(m, 2)` for `n = 3m`, `m(3m-1)/2` for `n = 3m + 1` and `m(3m+1)/2` for `n = 3m + 2`.
The case `n = 0` of the first formula is included (both sides are `0`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 2 (`integers-2025-A5-thm-2`). -/
public theorem_wanted catalanWords_capacity_natDegree (m : ℕ) :
    (capacityDist (catalanWords (3 * m))).natDegree = 3 * m.choose 2 ∧
      (capacityDist (catalanWords (3 * m + 1))).natDegree = m * (3 * m - 1) / 2 ∧
        (capacityDist (catalanWords (3 * m + 2))).natDegree = m * (3 * m + 1) / 2

/-- Mansour and Shattuck's Corollary 4, leading coefficient: for `n ≥ 4`, the number `cₙ` of
Catalan words of length `n` with maximum capacity is `2` if `3 ∣ n` and `1` otherwise.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 4 (`integers-2025-A5-cor-4`). -/
public theorem_wanted catalanWords_capacity_leadingCoeff (n : ℕ) (hn : 4 ≤ n) :
    (capacityDist (catalanWords n)).leadingCoeff = if 3 ∣ n then 2 else 1

/-- Mansour and Shattuck's Corollary 4, subleading coefficient: with
`α = deg a(n; q)`, the coefficient `dₙ` of `q^{α-1}` is `2m`, `m + 1`, `m + 2` for
`n = 3m, 3m + 1, 3m + 2 ≥ 7`, and `d₄ = 13`, `d₅ = 7`, `d₆ = 8`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Corollary 4 (`integers-2025-A5-cor-4`). -/
public theorem_wanted catalanWords_capacity_subleading_coeff (n : ℕ) (hn : 4 ≤ n) :
    (capacityDist (catalanWords n)).coeff ((capacityDist (catalanWords n)).natDegree - 1) =
      if n = 4 then 13 else if n = 5 then 7 else if n = 6 then 8
      else if n % 3 = 0 then 2 * (n / 3 : ℕ) else if n % 3 = 1 then (n / 3 : ℕ) + 1
      else (n / 3 : ℕ) + 2

/-- Mansour and Shattuck's Theorem 3, formula (24): for `2 ≤ i ≤ n`, the number of
zero-capacity Catalan words of length `n` ending in `i` is
`a(n, i; 0) = ∑_{m=0}^{n-i} C(n-m-2, i-2) F_{2m-1}`, with `F_{-1} = 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`). -/
public theorem_wanted catalanCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (catalanCapacityDist n i).eval 0 =
      ∑ m ∈ Finset.range (n - i + 1),
        (((n - m - 2).choose (i - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1)) : ℕ) : ℤ)

/-- Mansour and Shattuck's Theorem 3, totals: for `n ≥ 1`, `a(n, 1; 0) = F_{2n-3}` (with
`F_{-1} = 1`) and `a(n; 0) = F_{2n-1}`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`). -/
public theorem_wanted catalanWords_zero_capacity_count (n : ℕ) (hn : 1 ≤ n) :
    (catalanCapacityDist n 1).eval 0 = ((if n = 1 then 1 else Nat.fib (2 * n - 3) : ℕ) : ℤ) ∧
      (capacityDist (catalanWords n)).eval 0 = (Nat.fib (2 * n - 1) : ℤ)

/-- Mansour and Shattuck's Lemma 6: for `m, j ≥ 2`,
`t(m, j) = q^j t(m-1, j) + q^j ∑_{ℓ=1}^{m-2} t(ℓ, j-1) t(m-ℓ-1, j)`, with
`t(m, 1) = t(1, m) = q^m` for `m ≥ 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 6 (`integers-2025-A5-lem-6`). -/
public theorem_wanted smoothPlateauAreaDist_recurrence (m j : ℕ) (hm : 2 ≤ m) (hj : 2 ≤ j) :
    smoothPlateauAreaDist m j =
        X ^ j * smoothPlateauAreaDist (m - 1) j +
          X ^ j * ∑ ℓ ∈ Finset.Icc 1 (m - 2),
            smoothPlateauAreaDist ℓ (j - 1) * smoothPlateauAreaDist (m - ℓ - 1) j ∧
      ∀ k : ℕ, 1 ≤ k → smoothPlateauAreaDist k 1 = X ^ k ∧ smoothPlateauAreaDist 1 k = X ^ k

/-- `t*(m, j; q)`, the area distribution on the set `𝒯*_{m,j}` of members of `𝒯_{m,j}` with no
two adjacent `1`s.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Section 4, definition of `t*(m, j; q)`. -/
public noncomputable def restrictedSmoothPlateauAreaDist (m j : ℕ) : ℤ[X] :=
  areaDist (wordsEndingIn ((Fintype.piFinset fun _ : Fin m => Finset.Icc 1 j).filter fun w =>
    (∀ i : Fin m, i.val = 0 → w i = j) ∧
      ∀ i k : Fin m, k.val = i.val + 1 →
        w k ≤ w i + 1 ∧ w i ≤ w k + 1 ∧ ¬(w i = 1 ∧ w k = 1)) j)

/-- The denominators of the finite continued fractions in Lemmas 8 and 10, as power series in `x`
over `ℤ[q]`: `K₁ = base` and `K_k = 1 - q^k x - q^{2k-1} x² / K_{k-1}` for `k ≥ 2` (`K₀ = 1` is
unused). Lemma 8 takes `base = 1 - qx` and Lemma 10 takes `base = 1`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemmas 8 and 10. -/
public noncomputable def capacityContinuedFractionDen (base : PowerSeries ℤ[X]) :
    ℕ → PowerSeries ℤ[X]
  | 0 => 1
  | 1 => base
  | k + 2 => 1 - PowerSeries.C (X ^ (k + 2)) * PowerSeries.X -
      PowerSeries.C (X ^ (2 * k + 3)) * PowerSeries.X ^ 2 *
        PowerSeries.invOfUnit (capacityContinuedFractionDen base (k + 1)) 1

/-- Every continued-fraction denominator has constant term `1` when `base` does, so the
inverses `PowerSeries.invOfUnit _ 1` in its definition are true inverses.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemmas 8 and 10. -/
public theorem constantCoeff_capacityContinuedFractionDen (base : PowerSeries ℤ[X])
    (h : PowerSeries.constantCoeff base = 1) :
    ∀ k, PowerSeries.constantCoeff (capacityContinuedFractionDen base k) = 1
  | 0 => by simp [capacityContinuedFractionDen]
  | 1 => by simpa [capacityContinuedFractionDen] using h
  | k + 2 => by simp [capacityContinuedFractionDen]

/-- Mansour and Shattuck's Lemma 8: for `j ≥ 1`, the generating function
`T_j(x; q) = ∑_{m ≥ 1} t(m, j; q) xᵐ` is the finite continued fraction
`q^j x / (1 - q^j x - q^{2j-1} x² / (1 - q^{j-1} x - ⋯ q⁵x² / (1 - q²x - q³x² / (1 - qx))))`,
with `T₁ = qx / (1 - qx)` (the case `j = 1`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 8 (`integers-2025-A5-lem-8`). -/
public theorem_wanted smoothPlateauAreaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun m => smoothPlateauAreaDist m j) =
      PowerSeries.C (X ^ j) * PowerSeries.X *
        PowerSeries.invOfUnit
          (capacityContinuedFractionDen (1 - PowerSeries.C X * PowerSeries.X) j) 1

/-- Mansour and Shattuck's Lemma 10: for `j ≥ 1`, the generating function
`T*_j(x; q) = ∑_{m ≥ 1} t*(m, j; q) xᵐ` is the finite continued fraction
`q^j x / (1 - q^j x - q^{2j-1} x² / (1 - q^{j-1} x - ⋯ q⁵x² / (1 - q²x - q³x²)))`,
with `T*₁ = qx` (the case `j = 1`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 10 (`integers-2025-A5-lem-10`). -/
public theorem_wanted restrictedSmoothPlateauAreaDist_genFun (j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.mk (fun m => restrictedSmoothPlateauAreaDist m j) =
      PowerSeries.C (X ^ j) * PowerSeries.X *
        PowerSeries.invOfUnit (capacityContinuedFractionDen 1 j) 1

/-- Mansour and Shattuck's Lemma 7, recurrence (26): for `1 < i < n`,
`r(n,i) = r(n-1,i) + r(n-1,i+1) + s(n-1,i-1) + ∑_{m=1}^{n-i-1} q^{mi} r(n-m-1,i) t(m,i-1;1/q)`,
in `ℤ[q, q⁻¹]`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (smoothCapacityDist n i) =
      toLaurent (smoothCapacityDist (n - 1) i) + toLaurent (smoothCapacityDist (n - 1) (i + 1)) +
        toLaurent (smoothMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (smoothCapacityDist (n - m - 1) i) *
            invert (toLaurent (smoothPlateauAreaDist m (i - 1)))

/-- Mansour and Shattuck's Lemma 7, recurrence (27): for `1 < i < n`,
`s(n,i) = s(n-1,i) + s(n-1,i-1) + ∑_{m=1}^{n-i-1} q^{mi} s(n-m-1,i) t(m,i-1;1/q)`, in
`ℤ[q, q⁻¹]`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothMaxEndCapacityDist_recurrence (n i : ℕ) (hi : 1 < i) (hin : i < n) :
    toLaurent (smoothMaxEndCapacityDist n i) =
      toLaurent (smoothMaxEndCapacityDist (n - 1) i) +
        toLaurent (smoothMaxEndCapacityDist (n - 1) (i - 1)) +
        ∑ m ∈ Finset.Icc 1 (n - i - 1),
          T ((m * i : ℕ) : ℤ) * toLaurent (smoothMaxEndCapacityDist (n - m - 1) i) *
            invert (toLaurent (smoothPlateauAreaDist m (i - 1)))

/-- Mansour and Shattuck's Lemma 7, boundary values: `r(n, n) = s(n, n) = s(n, 1) = 1` for
`n ≥ 1`, and `r(n, 1) = r(n-1, 1) + r(n-1, 2)` for `n ≥ 2`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 7 (`integers-2025-A5-lem-7`). -/
public theorem_wanted smoothCapacityDist_boundary (n : ℕ) (hn : 1 ≤ n) :
    smoothCapacityDist n n = 1 ∧ smoothMaxEndCapacityDist n n = 1 ∧
      smoothMaxEndCapacityDist n 1 = 1 ∧
        (2 ≤ n → smoothCapacityDist n 1 =
          smoothCapacityDist (n - 1) 1 + smoothCapacityDist (n - 1) 2)

/-- Mansour and Shattuck's Lemma 9: for `i ≥ 1`,
`S_i(x; q) = ∑_{n ≥ i} s(n, i; q) xⁿ = xⁱ / ∏_{j=0}^{i-1} (1 - x - x T_j(q^{j+1} x; 1/q))`, in
power series over `ℤ[q, q⁻¹]`, where `T_j(q^{j+1} x; 1/q) = ∑_m q^{(j+1)m} t(m, j; 1/q) xᵐ`
(and `T₀ = 0`, since `t(m, 0) = 0`).

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 9 (`integers-2025-A5-lem-9`). -/
public theorem_wanted smoothMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (smoothMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.range i,
        PowerSeries.invOfUnit (1 - PowerSeries.X - PowerSeries.X * PowerSeries.mk fun m =>
          T (((j + 1) * m : ℕ) : ℤ) * invert (toLaurent (smoothPlateauAreaDist m j))) 1

/-- Mansour and Shattuck's Lemma 11: for `i ≥ 1`,
`S*_i(x; q) = ∑_{n ≥ i} s*(n, i; q) xⁿ = xⁱ / ∏_{j=1}^{i-1} (1 - x - x T*_j(q^{j+1} x; 1/q))`, in
power series over `ℤ[q, q⁻¹]`, where `T*_j(q^{j+1} x; 1/q) = ∑_m q^{(j+1)m} t*(m, j; 1/q) xᵐ`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 11 (`integers-2025-A5-lem-11`). -/
public theorem_wanted restrictedSmoothMaxEndCapacityDist_genFun (i : ℕ) (hi : 1 ≤ i) :
    PowerSeries.mk (fun n => toLaurent (restrictedSmoothMaxEndCapacityDist n i)) =
      PowerSeries.X ^ i * ∏ j ∈ Finset.Icc 1 (i - 1),
        PowerSeries.invOfUnit (1 - PowerSeries.X - PowerSeries.X * PowerSeries.mk fun m =>
          T (((j + 1) * m : ℕ) : ℤ) * invert (toLaurent (restrictedSmoothPlateauAreaDist m j))) 1

/-- Mansour and Shattuck's Theorem 5: the maximum capacity over smooth words of length
`4m + p` is `deg r(4m + p; q) = m(2m + p - 1)` for `m ≥ 1`, `0 ≤ p ≤ 3`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 5 (`integers-2025-A5-thm-5`). -/
public theorem_wanted smoothWords_capacity_natDegree (m p : ℕ) (hm : 1 ≤ m) (hp : p ≤ 3) :
    (capacityDist (smoothWords (4 * m + p))).natDegree = m * (2 * m + p - 1)

/-- Mansour and Shattuck's Theorem 6, formula (34): for `2 ≤ i ≤ n`, the number of
zero-capacity smooth words of length `n` ending in `i` is `∑_{j=i-2}^{n-2} C(n-2, j)`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 6 (`integers-2025-A5-thm-6`). -/
public theorem_wanted smoothCapacityDist_eval_zero (n i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n) :
    (smoothCapacityDist n i).eval 0 = ∑ j ∈ Finset.Icc (i - 2) (n - 2), ((n - 2).choose j : ℤ)

/-- Mansour and Shattuck's Theorem 6, totals: `r(n, 1; 0) = 2^{n-2}` for `n ≥ 2`,
`r(1, 1; 0) = 1`, `r(n; 0) = (n + 2) 2^{n-3}` for `n ≥ 3` and `r(1; 0) = 1`. The paper states
the total for `n ≥ 2`; at `n = 2` the exponent `n - 3 = -1` gives `r(2; 0) = 2`, so that case is
stated separately as `r(2; 0) = 2`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 6 (`integers-2025-A5-thm-6`). -/
public theorem_wanted smoothWords_zero_capacity_count (n : ℕ) (hn : 2 ≤ n) :
    (smoothCapacityDist n 1).eval 0 = 2 ^ (n - 2) ∧ (smoothCapacityDist 1 1).eval 0 = 1 ∧
      (3 ≤ n → (capacityDist (smoothWords n)).eval 0 = (n + 2) * 2 ^ (n - 3)) ∧
        (capacityDist (smoothWords 2)).eval 0 = 2 ∧ (capacityDist (smoothWords 1)).eval 0 = 1

/-- Mansour and Shattuck's Theorem 9, degree formula (41): for `n = 8m + p ≥ 1` with
`0 ≤ p ≤ 7`, the maximum capacity over restricted smooth words is
`deg r*(8m + p; q) = 8m² + (2p - 3)m + e_p` with `e_p = 0` for `p ≤ 3`, `e_4 = 1` and
`e_p = 2^{p-5}` for `5 ≤ p ≤ 7`; computed in `ℤ`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 9 (`integers-2025-A5-thm-9`). -/
public theorem_wanted restrictedSmoothWords_capacity_natDegree (m p : ℕ) (hp : p ≤ 7)
    (hn : 1 ≤ 8 * m + p) :
    ((capacityDist (restrictedSmoothWords (8 * m + p))).natDegree : ℤ) =
      8 * (m : ℤ) ^ 2 + (2 * (p : ℤ) - 3) * m +
        if p ≤ 3 then 0 else if p = 4 then 1 else 2 ^ (p - 5)

/-- Mansour and Shattuck's Theorem 9, leading coefficient (42): the number `cₙ` of restricted
smooth words of length `n = 8m + p` with maximum capacity is `m + 1` for `p ∈ {0, 3}`, `1` for
`p ∈ {1, 2, 4, 7}`, `m + 3` for `p = 5` and `m + 2` for `p = 6` when `m ≥ 1`, and
`1, 1, 3, 1, 5, 2, 1` for `n = 1, …, 7`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 9 (`integers-2025-A5-thm-9`). -/
public theorem_wanted restrictedSmoothWords_capacity_leadingCoeff (m p : ℕ) (hp : p ≤ 7)
    (hn : 1 ≤ 8 * m + p) :
    (capacityDist (restrictedSmoothWords (8 * m + p))).leadingCoeff =
      if m = 0 then ([0, 1, 1, 3, 1, 5, 2, 1].getD p 0 : ℤ)
      else if p = 0 ∨ p = 3 then (m : ℤ) + 1 else if p = 5 then (m : ℤ) + 3
      else if p = 6 then (m : ℤ) + 2 else 1

/-- Mansour and Shattuck's Theorem 10, formula (43): for `3 ≤ i ≤ n`, the number of
zero-capacity restricted smooth words of length `n` ending in `i` is
`∑_{j=i-3}^{n-3} C(n-3, j)`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 10 (`integers-2025-A5-thm-10`). -/
public theorem_wanted restrictedSmoothCapacityDist_eval_zero (n i : ℕ) (hi : 3 ≤ i)
    (hin : i ≤ n) :
    (restrictedSmoothCapacityDist n i).eval 0 =
      ∑ j ∈ Finset.Icc (i - 3) (n - 3), ((n - 3).choose j : ℤ)

/-- Mansour and Shattuck's Theorem 10, remaining values: `r*(n, 1; 0)` is `1` for `n = 1, 3`,
`0` for `n = 2` and `2^{n-4}` for `n ≥ 4`; `r*(n, 2; 0)` is `1` for `n = 2` and `2^{n-3}` for
`n ≥ 3`; and `r*(n; 0) = (n + 2) 2^{n-4}` for `n ≥ 4`, with `r*(1; 0) = r*(2; 0) = 1` and
`r*(3; 0) = 3`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 10 (`integers-2025-A5-thm-10`). -/
public theorem_wanted restrictedSmoothWords_zero_capacity_count (n : ℕ) (hn : 1 ≤ n) :
    (restrictedSmoothCapacityDist n 1).eval 0 =
        (if n = 1 ∨ n = 3 then 1 else if n = 2 then 0 else 2 ^ (n - 4)) ∧
      (2 ≤ n → (restrictedSmoothCapacityDist n 2).eval 0 = if n = 2 then 1 else 2 ^ (n - 3)) ∧
        (capacityDist (restrictedSmoothWords n)).eval 0 =
          if n ≤ 2 then 1 else if n = 3 then 3 else (n + 2) * 2 ^ (n - 4)

/-- Mansour and Shattuck's Theorem 11: `|ℛ*ₙ|` is the grand Motzkin number `G_{n-1}` for
`n ≥ 1`; `G_k` (OEIS A002426) is the central trinomial coefficient
`MetaMathlibExt.trinomialCoefficient k k`.

Source: Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According
to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 11 (`integers-2025-A5-thm-11`). -/
public theorem_wanted card_restrictedSmoothWords (n : ℕ) (hn : 1 ≤ n) :
    (restrictedSmoothWords n).card = trinomialCoefficient (n - 1) (n - 1)

end

end MetaMathlibExt
