/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# `k`-box paths: a subfamily of skew Dyck paths related to `k`-ary trees

Statements from Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to
`k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4
(arXiv:2306.15778). Skew Dyck paths are words over `{U, D, L}` that avoid the
factors `UL` and `LU`, have as many `U`s as `D`s and `L`s together, and have no
prefix with more `D`s and `L`s than `U`s; the semilength is the number of `U`s.
A `k`-box path of size `n` (`k ≥ 1`) is a skew Dyck path of semilength
`(k+2)n - 1` with exactly `n` factors `U D^k L`. A `k`-Dyck path is a word over
`Bool` (`true` for `U = (1,1)`, `false` for `D^{(k)} = (k,-k)`), and an
augmented `k`-Dyck path replaces each `D^{(k)}` by `U D^{k-1} L D`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The steps `U = (1,1)`, `D = (1,-1)`, `L = (-1,-1)` of a skew Dyck path.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public inductive SkewDyckStep
  | U
  | D
  | L
  deriving DecidableEq

open SkewDyckStep

/-- The three steps form a finite type.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public instance : Fintype SkewDyckStep where
  elems := {U, D, L}
  complete := by intro x; cases x <;> simp

/-- A skew Dyck path as a word: it avoids `UL` and `LU`, has as many `U`s as `D`s
and `L`s together, and no prefix has more `D`s and `L`s than `U`s.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def IsSkewDyckWord (w : List SkewDyckStep) : Prop :=
  ¬ [U, L] <:+: w ∧ ¬ [L, U] <:+: w ∧ w.count U = w.count D + w.count L ∧
    ∀ i ≤ w.length, (w.take i).count D + (w.take i).count L ≤ (w.take i).count U

/-- Being a skew Dyck word is decidable.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public instance : DecidablePred IsSkewDyckWord := fun w => by
  unfold IsSkewDyckWord
  infer_instance

/-- The skew Dyck paths of semilength `m` (they have length `2m`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def skewDyckWords (m : ℕ) : Finset (List SkewDyckStep) :=
  ((Finset.univ : Finset (Fin (2 * m) → SkewDyckStep)).image List.ofFn).filter IsSkewDyckWord

/-- There are three skew Dyck paths of semilength `2`: `UUDD`, `UDUD`, `UUDL`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public theorem card_skewDyckWords_two : (skewDyckWords 2).card = 3 := by
  decide +kernel

/-- The number of occurrences of the factor `f` in `w` (contiguous, overlaps
counted).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 1. -/
public def skewFactorCount (f w : List SkewDyckStep) : ℕ :=
  w.tails.countP fun t => f.isPrefixOf t

/-- The factor `U D^k L`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def boxFactor (k : ℕ) : List SkewDyckStep :=
  U :: List.replicate k D ++ [L]

/-- `B_n^{(k)}`: the `k`-box paths of size `n`, i.e. skew Dyck paths of semilength
`(k+2)n - 1` with exactly `n` factors `U D^k L`. (For `n = 0` the truncated
semilength is `0` and the set is `{ε}`; the statements below take `n ≥ 1`.)

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def kBoxPaths (k n : ℕ) : Finset (List SkewDyckStep) :=
  (skewDyckWords ((k + 2) * n - 1)).filter fun w => skewFactorCount (boxFactor k) w = n

/-- The only box path (`k = 1`) of size `1` is `UUDL`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public theorem kBoxPaths_one_one : kBoxPaths 1 1 = {[U, U, D, L]} := by
  decide +kernel

/-- The word `U^{a₁} D^k L D ⋯ U^{a_{n-1}} D^k L D U^{a_n} D^k L` for
`a = [a₁, …, a_n]`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2. -/
public def boxWord (k : ℕ) (a : List ℕ) : List SkewDyckStep :=
  (a.dropLast.flatMap fun x => List.replicate x U ++ List.replicate k D ++ [L, D]) ++
    List.replicate (a.getLastD 0) U ++ List.replicate k D ++ [L]

/-- `boxWord 1 [3, 2] = UUUDLDUUDL`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2. -/
public theorem boxWord_one_three_two :
    boxWord 1 [3, 2] = [U, U, U, D, L, D, U, U, D, L] := by
  decide

/-- A `k`-Dyck path as a word over `Bool` (`true` for `U = (1,1)`, `false` for
`D^{(k)} = (k,-k)`): it ends on the `x`-axis and never goes below it.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def IsKDyckWord (k : ℕ) (w : List Bool) : Prop :=
  w.count true = k * w.count false ∧
    ∀ i ≤ w.length, k * (w.take i).count false ≤ (w.take i).count true

/-- Being a `k`-Dyck word is decidable.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public instance (k : ℕ) : DecidablePred (IsKDyckWord k) := fun w => by
  unfold IsKDyckWord
  infer_instance

/-- The `k`-Dyck paths of size `n` (`n` steps `D^{(k)}`, hence length `(k+1)n`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def kDyckWords (k n : ℕ) : Finset (List Bool) :=
  ((Finset.univ : Finset (Fin ((k + 1) * n) → Bool)).image List.ofFn).filter fun w =>
    IsKDyckWord k w ∧ w.count false = n

/-- There are three `2`-Dyck paths of size `2`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public theorem card_kDyckWords_two_two : (kDyckWords 2 2).card = 3 := by
  decide +kernel

/-- The augmented path of a `k`-Dyck word: each `D^{(k)}` becomes `U D^{k-1} L D`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def augmentKDyckWord (k : ℕ) (w : List Bool) : List SkewDyckStep :=
  w.flatMap fun b => if b then [U] else U :: List.replicate (k - 1) D ++ [L, D]

/-- `D̂_n^{(k)}`: the augmented `k`-Dyck paths of size `n` (used for `k ≥ 2`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 2. -/
public def augmentedKDyckPaths (k n : ℕ) : Finset (List SkewDyckStep) :=
  (kDyckWords k n).image (augmentKDyckWord k)

/-- The number of returns of a path: steps that end on the `x`-axis.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 3. -/
public def skewReturns (w : List SkewDyckStep) : ℕ :=
  ((List.range w.length).filter fun i =>
    decide ((w.take (i + 1)).count U = (w.take (i + 1)).count D + (w.take (i + 1)).count L)).length

/-- The number of long ascents of a path: maximal runs of at least two `U`s.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public def skewLongAscents (w : List SkewDyckStep) : ℕ :=
  ((List.range w.length).filter fun i =>
    decide (w[i]? = some U ∧ w[i + 1]? = some U ∧ (i = 0 ∨ w[i - 1]? ≠ some U))).length

/-- The source's example `U D U^5 D L^2 D U D L` has two returns and one long
ascent.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Figure 1. -/
public theorem skewReturns_skewLongAscents_example :
    skewReturns [U, D, U, U, U, U, U, D, L, L, D, U, D, L] = 2 ∧
      skewLongAscents [U, D, U, U, U, U, U, D, L, L, D, U, D, L] = 1 := by
  decide

/-- `G_k(x) = ∑_n |D̂_n^{(k)}| x^n`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 6. -/
public noncomputable def augmentedKDyckGF (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((augmentedKDyckPaths k n).card : ℤ)

/-- `F̀_k(t, x) = ∑_{n ≥ 1} ∑_{μ ∈ B_n^{(k)}} t^{returns(μ)} x^n` in `ℤ[t]⟦x⟧`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 6. -/
public noncomputable def kBoxReturnGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else ∑ w ∈ kBoxPaths k n, Polynomial.X ^ skewReturns w

/-- `F́_k(t, x) = ∑_{n ≥ 1} ∑_{μ ∈ B_n^{(k)}} t^{longAscents(μ)} x^n` in `ℤ[t]⟦x⟧`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public noncomputable def kBoxLongAscentGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else ∑ w ∈ kBoxPaths k n, Polynomial.X ^ skewLongAscents w

/-- `Ǵ_k(t, x) = ∑_{n ≥ 0} ∑_{μ ∈ D̂_n^{(k)}} t^{longAscents(μ)} x^n` in
`ℤ[t]⟦x⟧`, including the empty path (constant term `1`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Section 7. -/
public noncomputable def augmentedKDyckLongAscentGF (k : ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => ∑ w ∈ augmentedKDyckPaths k n, Polynomial.X ^ skewLongAscents w

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `t` of the bivariate generating functions, a constant in `ℤ[t]`. -/
local notation "𝒕" => PowerSeries.C (Polynomial.X : Polynomial ℤ)

/-- Among skew Dyck paths with exactly `n ≥ 1` factors `U D^k L` (`k ≥ 1`), the
smallest semilength is `(k+2)n - 1`: it is attained, and no such path is shorter.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 1
(`jis-2024-24.2.4-prop-1`). -/
public theorem_wanted min_semilength_boxFactor {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∃ w, IsSkewDyckWord w ∧ skewFactorCount (boxFactor k) w = n ∧
      w.count U = (k + 2) * n - 1) ∧
    ∀ w, IsSkewDyckWord w → skewFactorCount (boxFactor k) w = n → (k + 2) * n - 1 ≤ w.count U

/-- Structure of `k`-box paths: every `k`-box path of size `n` is
`U^{a₁} D^k L D ⋯ U^{a_{n-1}} D^k L D U^{a_n} D^k L` with positive `aᵢ`; conversely,
such a word with `a₁ + ⋯ + a_n = (k+2)n - 1` and no prefix with fewer `U`s than
`D`s and `L`s together is a `k`-box path of size `n`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 2
(`jis-2024-24.2.4-lem-2`). -/
public theorem_wanted kBoxPaths_structure {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ w ∈ kBoxPaths k n, ∃ a : List ℕ, a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ w = boxWord k a) ∧
    ∀ a : List ℕ, a.length = n → (∀ x ∈ a, 0 < x) → a.sum = (k + 2) * n - 1 →
      (∀ i ≤ (boxWord k a).length, ((boxWord k a).take i).count D +
        ((boxWord k a).take i).count L ≤ ((boxWord k a).take i).count U) →
      boxWord k a ∈ kBoxPaths k n

/-- Decomposition: the `k`-box paths (of all sizes `n ≥ 1`) are exactly the words
`μ₁ U μ₂ U ⋯ μ_{k+1} U D^k L` with `μ₁, …, μ_{k+1}` augmented `(k+1)`-Dyck paths.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 4
(`jis-2024-24.2.4-lem-4`). -/
public theorem_wanted kBoxPaths_decomposition {k : ℕ} (hk : 1 ≤ k) (w : List SkewDyckStep) :
    (∃ n, 1 ≤ n ∧ w ∈ kBoxPaths k n) ↔
      ∃ μ : Fin (k + 1) → List SkewDyckStep, (∀ i, ∃ m, μ i ∈ augmentedKDyckPaths (k + 1) m) ∧
        w = (List.ofFn fun i => μ i ++ [U]).flatten ++ List.replicate k D ++ [L]

/-- The number of `k`-box paths of size `n` is
`f_{k,n} = (k+1)/(n-1) · binom((k+2)n-2, n-2) = 1/((k+2)n-1) · binom((k+2)n-1, n)`,
stated with denominators cleared (the first form for `n ≥ 2`). The identification
with `(k+1)`-tuples of `(k+2)`-ary trees with `n - 1` nodes is not stated.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 5
(`jis-2024-24.2.4-thm-5`). -/
public theorem_wanted card_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * n - 1) * (kBoxPaths k n).card = ((k + 2) * n - 1).choose n ∧
      (2 ≤ n → (n - 1) * (kBoxPaths k n).card = (k + 1) * ((k + 2) * n - 2).choose (n - 2))

/-- Tailed `k`-box paths (those ending with `U^{k+1} D^k L`) of size `n` number
`1/(n-1) · binom((k+2)(n-1), n-2) = 1/((k+2)(n-1)+1) · binom((k+2)(n-1)+1, n-1)`,
stated with denominators cleared (the first form for `n ≥ 2`). The identification
with `(k+2)`-ary trees with `n - 1` nodes is not stated.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 7
(`jis-2024-24.2.4-prop-7`). -/
public theorem_wanted card_tailed_kBoxPaths {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k + 2) * (n - 1) + 1) *
        ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1) + 1).choose (n - 1) ∧
    (2 ≤ n → (n - 1) * ((kBoxPaths k n).filter fun w =>
          List.replicate (k + 1) U ++ List.replicate k D ++ [L] <:+ w).card =
      ((k + 2) * (n - 1)).choose (n - 2))

/-- The returns generating function: `F̀_k = t x G_{k+1}^k / (1 - t x G_{k+1}^{k+1})`,
with the denominator cleared and `G_{k+1}` mapped into `ℤ[t]⟦x⟧`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 8
(`jis-2024-24.2.4-lem-8`). -/
public theorem_wanted kBoxReturnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    (1 - 𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ (k + 1)) *
        kBoxReturnGF k =
      𝒕 * 𝒙 * PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1)) ^ k

/-- The number of `k`-box paths of size `n` with exactly `j` returns
(`1 ≤ j ≤ n`) is `(j(k+1)-1)/((k+2)n-j-1) · binom((k+2)n-j-1, n-j)`, and also
`(j(k+1)-1)/(n-j) · binom((k+2)n-j-2, n-j-1)` for `j < n`; denominators cleared.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 9
(`jis-2024-24.2.4-thm-9`). -/
public theorem_wanted card_kBoxPaths_returns {k n j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j)
    (hjn : j ≤ n) :
    ((k + 2) * n - j - 1) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 1).choose (n - j) ∧
      (j < n → (n - j) * ((kBoxPaths k n).filter fun w => skewReturns w = j).card =
        (j * (k + 1) - 1) * ((k + 2) * n - j - 2).choose (n - j - 1))

/-- Among `k`-box paths of size `n`, the mean number of returns is
`(k+2)((k+2)n-1) / ((k+1)((k+1)n+1))` and the variance is
`(k+2)((k+2)n-1)((2k+1)(k+1)n-2)(n-1) / ((k+1)²((k+1)n+1)²((k+1)n+2))`.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Corollary 11
(`jis-2024-24.2.4-cor-11`). -/
public theorem_wanted kBoxPaths_returns_mean_variance {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card =
        ((k + 2) * ((k + 2) * n - 1) : ℚ) / ((k + 1) * ((k + 1) * n + 1)) ∧
      (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        ((k + 2) * ((k + 2) * n - 1) * ((2 * k + 1) * (k + 1) * n - 2) * (n - 1) : ℚ) /
          ((k + 1) ^ 2 * ((k + 1) * n + 1) ^ 2 * ((k + 1) * n + 2))

/-- The long-ascent functional equations: `F́_k = x Ǵ_{k+1}^k (Ǵ_{k+1} - 1 + t)` for
`k ≥ 1` and `Ǵ_k = 1 + x Ǵ_k^k (Ǵ_k - 1 + t)` for `k ≥ 2`. The source's displayed
sum for `Ǵ_k` starts at `j = 1`, omitting the empty path; `Ǵ_k` here includes it
(constant term `1`), as both equations require.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 12
(`jis-2024-24.2.4-lem-12`). -/
public theorem_wanted kBoxLongAscentGF_functional_equations :
    (∀ k : ℕ, 1 ≤ k → kBoxLongAscentGF k =
      𝒙 * augmentedKDyckLongAscentGF (k + 1) ^ k *
        (augmentedKDyckLongAscentGF (k + 1) - 1 + 𝒕)) ∧
    ∀ k : ℕ, 2 ≤ k → augmentedKDyckLongAscentGF k =
      1 + 𝒙 * augmentedKDyckLongAscentGF k ^ k * (augmentedKDyckLongAscentGF k - 1 + 𝒕)

/-- The number of `k`-box paths of size `n` with exactly `j ≥ 1` long ascents is
`1/j · binom((k+1)n-2, j-1) · binom(n-1, j-1)`; denominator cleared. (For
`j > n` both sides vanish.)

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 13
(`jis-2024-24.2.4-thm-13`). -/
public theorem_wanted card_kBoxPaths_longAscents {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hj : 1 ≤ j) :
    j * ((kBoxPaths k n).filter fun w => skewLongAscents w = j).card =
      ((k + 1) * n - 2).choose (j - 1) * (n - 1).choose (j - 1)

/-- For `K ≥ 4` and `n ≥ 1`, the `n`th second `K`-gonal number
`n((K-2)n + (K-4))/2` (the `K`-gonal formula `n((K-2)n - (K-4))/2` at `-n`) equals
the number of `(K-3)`-box paths of size `n + 1` with exactly two long ascents;
the factor `2` is cleared. The source states `K ≥ 3`; `K = 3` needs its `0`-box
convention (Remark 6), which is not formalized.

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Theorem 15
(`jis-2024-24.2.4-thm-15`). -/
public theorem_wanted second_polygonal_eq_card_kBoxPaths_two_longAscents {K n : ℕ}
    (hK : 4 ≤ K) (hn : 1 ≤ n) :
    n * ((K - 2) * n + (K - 4)) =
      2 * ((kBoxPaths (K - 3) (n + 1)).filter fun w => skewLongAscents w = 2).card

/-- `∑_j j f́_{k,n,j} = binom((k+2)n-3, n-1)` and
`∑_j j² f́_{k,n,j} = ((k+1)n² - n - 1)/((k+2)n-3) · binom((k+2)n-3, n-1)`, written as
sums over `k`-box paths of size `n` with the second denominator cleared (at
`k = n = 1` the cleared form reads `0 = 0`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 17
(`jis-2024-24.2.4-lem-17`). -/
public theorem_wanted sum_kBoxPaths_longAscents {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∑ w ∈ kBoxPaths k n, skewLongAscents w = ((k + 2) * n - 3).choose (n - 1) ∧
      ((k + 2) * n - 3) * ∑ w ∈ kBoxPaths k n, skewLongAscents w ^ 2 =
        ((k + 1) * n ^ 2 - n - 1) * ((k + 2) * n - 3).choose (n - 1)

/-- Among `k`-box paths of size `n`, the mean number of long ascents is
`n((k+1)n-1)/((k+2)n-2)` and the variance is
`((k+1)n-1)((k+1)n-2)n(n-1)/(((k+2)n-2)²((k+2)n-3))` (at `k = n = 1` both the
variance and, with Lean's `x / 0 = 0`, the right side are `0`).

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Proposition 18
(`jis-2024-24.2.4-prop-18`). -/
public theorem_wanted kBoxPaths_longAscents_mean_variance {k n : ℕ} (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card =
        (n * ((k + 1) * n - 1) : ℚ) / ((k + 2) * n - 2) ∧
      (∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewLongAscents w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        (((k + 1) * n - 1) * ((k + 1) * n - 2) * n * (n - 1) : ℚ) /
          (((k + 2) * n - 2) ^ 2 * ((k + 2) * n - 3))

end

end MetaMathlibExt
