/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Fundamental sequences and the duality formula for Zeckendorf binary expansions

Statement-only targets from Sungkon Chang, *Distribution of Zeckendorf Expressions*,
INTEGERS 25 (2025), Article A25 (texts checked against arXiv:2308.12872v1, Lemmas 1.2 and 1.5).
Indices are shifted to start at `0`: the paper's `2^(k-1)` and Fibonacci terms `F_k`
(`F_1 = 1`, `F_2 = 2`) become `2 ^ k` and `Nat.fib (k + 2)`. A coefficient function with entries
at most `1` is a finite index set `s : Finset ℕ`.

Section 2 of the paper (generalized Zeckendorf expansions for positive integers) works with
general coefficient functions, taken here as `ℕ →₀ ℕ` with the same shift: the paper's
`ε_k` (`k ≥ 1`) is `ε (k - 1)`, its basis coefficient function `β^k` is `Finsupp.single (k - 1) 1`,
`res_m(ε)` (indices `≤ m`) is `ε.filter (· < m)` and `res^m(ε)` (indices `≥ m`) is
`ε.filter (m - 1 ≤ ·)`.

Sections 3.3-4 (the function `δ*` on `(0, 1)`, its continuity, differentiability and extrema) are
checked against the journal text (INTEGERS 25 (2025), Article A25, pp. 18-42); see the section
note before `IsPeriodicZeckendorfPair`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Powers of two are the only fundamental sequence of the binary collection: a strictly
increasing sequence `H` of positive integers has every natural number represented uniquely as
`∑_{k ∈ s} H k` with `s` finite iff `H k = 2 ^ k` for all `k`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem_wanted bijective_finset_sum_iff_eq_two_pow {H : ℕ → ℕ} (hpos : ∀ k, 0 < H k)
    (hmono : StrictMono H) :
    Function.Bijective (fun s : Finset ℕ => ∑ k ∈ s, H k) ↔ ∀ k, H k = 2 ^ k

/-- The Fibonacci sequence is the only fundamental sequence of the Zeckendorf collection: a
strictly increasing sequence `H` of positive integers has every natural number represented
uniquely as `∑_{k ∈ s} H k` with `s` finite and containing no two adjacent indices iff
`H k = F_{k+2}` for all `k`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem_wanted bijective_nonadjacent_finset_sum_iff_eq_fib {H : ℕ → ℕ}
    (hpos : ∀ k, 0 < H k) (hmono : StrictMono H) :
    Function.Bijective (fun s : {s : Finset ℕ // ∀ k ∈ s, k + 1 ∉ s} => ∑ k ∈ s.1, H k) ↔
      ∀ k, H k = Nat.fib (k + 2)

/-- Duality formula: let `z(x)` count the `n < x` whose binary expansion has no two adjacent
`1`s (`n &&& (n >>> 1) = 0`). For a finite index set `A`, put `Ā = A` if `A` has no adjacent
indices, and otherwise `Ā = {k ∈ A | k ≥ j}` with `j` the largest index such that
`j, j + 1 ∈ A`. Then `z(∑_{k ∈ A} 2^k) = ∑_{k ∈ Ā} F_{k+2}`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 2 (`integers-2025-A25-lem-2`). -/
public theorem_wanted card_zeckendorfBinary_lt_sum_two_pow (A : Finset ℕ) :
    let J := A.filter (fun j => j + 1 ∈ A)
    let Abar := if h : J.Nonempty then A.filter (fun k => J.max' h ≤ k) else A
    ((Finset.range (∑ k ∈ A, 2 ^ k)).filter (fun n => n &&& (n >>> 1) = 0)).card =
      ∑ k ∈ Abar, Nat.fib (k + 2)

/-- The ascending lexicographic order `μ <_a ν` on coefficient functions with finite support:
at the largest index where they differ, `μ` is smaller (some `k` has `μ_k < ν_k` and
`μ_j = ν_j` for all `j > k`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def AscLexLT (μ ν : ℕ →₀ ℕ) : Prop :=
  ∃ k, μ k < ν k ∧ ∀ j, k < j → μ j = ν j

/-- The paper's example: `(1, 2, 10, 3, 7) <_a (1, 3, 1, 4, 7)` (they differ last at the
fourth entry, `3 < 4`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2, example). -/
public theorem ascLexLT_example :
    AscLexLT (Finsupp.single 0 1 + Finsupp.single 1 2 + Finsupp.single 2 10 +
        Finsupp.single 3 3 + Finsupp.single 4 7)
      (Finsupp.single 0 1 + Finsupp.single 1 3 + Finsupp.single 2 1 + Finsupp.single 3 4 +
        Finsupp.single 4 7) := by
  refine ⟨3, by simp, fun j hj => ?_⟩
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- `μ` is the immediate predecessor of `ν` in the collection `E`: the largest element of `E`
that is `<_a ν`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediatePredecessor (E : Set (ℕ →₀ ℕ)) (ν μ : ℕ →₀ ℕ) : Prop :=
  μ ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT ξ ν → ξ = μ ∨ AscLexLT ξ μ

/-- `ν` is the immediate successor of `μ` in the collection `E`: the smallest element of `E`
that is `>_a μ`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsImmediateSuccessor (E : Set (ℕ →₀ ℕ)) (μ ν : ℕ →₀ ℕ) : Prop :=
  ν ∈ E ∧ AscLexLT μ ν ∧ ∀ ξ ∈ E, AscLexLT μ ξ → ξ = ν ∨ AscLexLT ν ξ

/-- A Zeckendorf collection for positive integers: a collection `E` of coefficient functions
with finite support, containing `0` and every basis coefficient function, such that (1) each
`μ ∈ E` has only finitely many elements of `E` below it, and (2) if the immediate successor
`μ̃` of `μ ∈ E` is not `β^1 + μ`, then there is an index `n ≥ 2` with
`res_{n-1}(μ) = β̂^n` (the immediate predecessor of `β^n`) and `μ̃ = β^n + res^n(μ)`.
Zero-based: `n` is `m + 1` with `m ≥ 1`, `β^n = single m 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public def IsZeckendorfCollection (E : Set (ℕ →₀ ℕ)) : Prop :=
  0 ∈ E ∧ (∀ i, Finsupp.single i 1 ∈ E) ∧ (∀ μ ∈ E, {ν | ν ∈ E ∧ AscLexLT ν μ}.Finite) ∧
    ∀ μ ∈ E, ∀ ν, IsImmediateSuccessor E μ ν → ν ≠ Finsupp.single 0 1 + μ →
      ∃ m, 1 ≤ m ∧ IsImmediatePredecessor E (Finsupp.single m 1) (μ.filter (· < m)) ∧
        ν = Finsupp.single m 1 + μ.filter (m ≤ ·)

/-- A Zeckendorf collection contains the zero coefficient function.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.2). -/
public theorem IsZeckendorfCollection.zero_mem {E : Set (ℕ →₀ ℕ)} (h : IsZeckendorfCollection E) :
    0 ∈ E :=
  h.1

/-- The maximal `L`-block `θ^n = rev_{n-1}(β^*)` for a list `L = (e_1, …, e_N)`, where
`β^*_k = e_j` for `k ≡ j (mod N)`: zero-based, `θ^{m+1}` has entry `e_{((m-1-i) mod N) + 1}` at
index `i < m` and `0` from index `m` on.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public noncomputable def periodicTheta (L : List ℕ) (m : ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ Finset.range m, Finsupp.single i (L.getD ((m - 1 - i) % L.length) 0)

/-- For `L = (1, 0)` (the Fibonacci case), `θ^4 = (1, 0, 1)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public theorem periodicTheta_one_zero_three :
    periodicTheta [1, 0] 3 = Finsupp.single 0 1 + Finsupp.single 2 1 := by
  simp [periodicTheta, Finset.sum_range_succ]

/-- `ζ` is an `L`-block with (zero-based) support interval `[lo, m - 1]` at index `m` (the paper's
index `n - 1` with `n = m + 1 ≥ 2`): either the maximal block `θ^{m+1}` (`lo = 0`), or a proper
block, agreeing with `θ^{m+1}` above `lo`, smaller at `lo`, and `0` below `lo`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public def IsLBlock (L : List ℕ) (ζ : ℕ →₀ ℕ) (lo m : ℕ) : Prop :=
  1 ≤ m ∧ lo < m ∧
    ((lo = 0 ∧ ζ = periodicTheta L m) ∨
      (ζ.filter (lo < ·) = (periodicTheta L m).filter (lo < ·) ∧ ζ lo < periodicTheta L m lo ∧
        ζ.filter (· < lo) = 0))

/-- The periodic Zeckendorf collection determined by `L`: sums of finitely many `L`-blocks with
pairwise disjoint support intervals (blocks listed as `(ζ, lo, m)` with support `[lo, m - 1]`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 4 and the definition following it (arXiv:2308.12872v1, Section 2.2). -/
public def periodicZeckendorfCollection (L : List ℕ) : Set (ℕ →₀ ℕ) :=
  {μ | ∃ blocks : List ((ℕ →₀ ℕ) × ℕ × ℕ), (∀ b ∈ blocks, IsLBlock L b.1 b.2.1 b.2.2) ∧
    blocks.Pairwise (fun a b => a.2.2 ≤ b.2.1 ∨ b.2.2 ≤ a.2.1) ∧ μ = (blocks.map Prod.fst).sum}

/-- Evaluation `eval_H(ε) = ∑_k ε_k H_k` of a coefficient function at a sequence `H`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 1 (arXiv:2308.12872v1, Section 1). -/
public def zeckendorfEval (H : ℕ → ℕ) (ε : ℕ →₀ ℕ) : ℕ :=
  ε.sum fun k a => a * H k

/-- Zeckendorf collections are determined by their immediate predecessors: given coefficient
functions `θ^n` of order `n - 1` for `n ≥ 2`, there is a unique Zeckendorf collection with
`β̂^n = θ^n` for each `n ≥ 2`. Zero-based: `θ m` (`m ≥ 1`) has last nonzero entry at index
`m - 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 3 (`integers-2025-A25-thm-3`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted existsUnique_zeckendorfCollection (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → θ m (m - 1) ≠ 0 ∧ ∀ j, m ≤ j → θ m j = 0) :
    ∃! E : Set (ℕ →₀ ℕ), IsZeckendorfCollection E ∧
      ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)

/-- Periodic collections: for a list `L = (e_1, …, e_N)` with `N ≥ 2` and `e_1 ≠ 0`, the sums of
finitely many disjoint `L`-blocks form a Zeckendorf collection with `β̂^n = θ^n` for `n ≥ 2`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 4 (`integers-2025-A25-thm-4`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted isZeckendorfCollection_periodic (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    IsZeckendorfCollection (periodicZeckendorfCollection L) ∧
      ∀ m, 1 ≤ m → IsImmediatePredecessor (periodicZeckendorfCollection L)
        (Finsupp.single m 1) (periodicTheta L m)

/-- Fundamental sequences: for a Zeckendorf collection `E` with immediate predecessors `β̂^n`,
there is a unique strictly increasing sequence `H` of positive integers with
`eval_H : E → ℕ` bijective; moreover `H_n = H_1 + ∑ β̂^n H` for `n ≥ 2`, and `eval_H` is
increasing (`ε <_a δ ↔ eval_H ε < eval_H δ`). Zero-based indices.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 5 (`integers-2025-A25-thm-5`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021). -/
public theorem_wanted existsUnique_zeckendorf_fundamentalSequence {E : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)) :
    (∃! H : ℕ → ℕ, StrictMono H ∧ (∀ k, 0 < H k) ∧ Set.BijOn (zeckendorfEval H) E Set.univ) ∧
      ∀ H : ℕ → ℕ, StrictMono H → (∀ k, 0 < H k) → Set.BijOn (zeckendorfEval H) E Set.univ →
        (∀ m, 1 ≤ m → H m = H 0 + zeckendorfEval H (θ m)) ∧
          ∀ μ ∈ E, ∀ ν ∈ E, (AscLexLT μ ν ↔ zeckendorfEval H μ < zeckendorfEval H ν)

/-- Subcollections: if `Ẽ` and `E` are Zeckendorf collections and `β̂^n` are the immediate
predecessors in `E`, then `E ⊆ Ẽ` if and only if `β̂^n ∈ Ẽ` for all `n ≥ 2`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 1 (`integers-2025-A25-prop-1`; arXiv:2308.12872v1, Section 2.2). -/
public theorem_wanted zeckendorfCollection_subset_iff {E E' : Set (ℕ →₀ ℕ)}
    (hE' : IsZeckendorfCollection E') (hE : IsZeckendorfCollection E) (θ : ℕ → ℕ →₀ ℕ)
    (hθ : ∀ m, 1 ≤ m → IsImmediatePredecessor E (Finsupp.single m 1) (θ m)) :
    E ⊆ E' ↔ ∀ m, 1 ≤ m → θ m ∈ E'

/-- The counting function `z(x)` of Section 3: the number of natural numbers `n < x` of the form
`n = ∑ μ H̃` with `μ ∈ E` (the elements of `R(x)`), for a real bound `x`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1 and Section 3 (arXiv:2308.12872v1, Sections 1 and 3.2). -/
public noncomputable def subcollectionCount (E : Set (ℕ →₀ ℕ)) (H : ℕ → ℕ) (x : ℝ) : ℕ :=
  {n : ℕ | (n : ℝ) < x ∧ ∃ μ ∈ E, zeckendorfEval H μ = n}.ncard

/-- `z(x) = 0` for `x ≤ 0`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3 (arXiv:2308.12872v1, Section 3.2). -/
public theorem subcollectionCount_of_nonpos (E : Set (ℕ →₀ ℕ)) (H : ℕ → ℕ) {x : ℝ}
    (hx : x ≤ 0) : subcollectionCount E H x = 0 := by
  have h : {n : ℕ | (n : ℝ) < x ∧ ∃ μ ∈ E, zeckendorfEval H μ = n} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hn
    exact absurd hn (not_lt.mpr (le_trans hx (Nat.cast_nonneg n)))
  simp [subcollectionCount, h]

/-- Main theorem, part (1): let `Ẽ` and `E` be the periodic Zeckendorf collections determined by
lists `L̃` and `L` (length `≥ 2`, first entry nonzero) with `E` a proper subcollection of `Ẽ`, and
let `H̃` be the fundamental sequence of `Ẽ`. Then there are positive reals `γ < 1`, `a`, `b` with
`a < z(x) / x^γ < b` for all sufficiently large `x`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1 (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1, with the standing
assumption of Section 3 that `E` is a proper subcollection). -/
public theorem_wanted exists_rpow_bounds_subcollectionCount (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H' : ℕ → ℕ}
    (hmono : StrictMono H') (hpos : ∀ k, 0 < H' k)
    (hbij : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ γ a b : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < a ∧ 0 < b ∧ ∀ᶠ x in Filter.atTop,
      a < (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) / x ^ γ ∧
        (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) / x ^ γ < b

/-- Zeckendorf binary expansions: with `z(x)` the number of `n < x` whose binary expansion has no
two adjacent `1`s (`n &&& (n >>> 1) = 0`), `φ` the golden ratio and `γ = log₂ φ`,
`limsup z(x) / x^γ = 3^γ (φ + 2) / 5`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1, Equation (1) (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted limsup_zeckendorfBinaryCount_div_rpow :
    Filter.limsup (fun x : ℝ =>
      ({n : ℕ | (n : ℝ) < x ∧ n &&& (n >>> 1) = 0}.ncard : ℝ) /
        x ^ Real.logb 2 Real.goldenRatio) Filter.atTop =
      3 ^ Real.logb 2 Real.goldenRatio * (Real.goldenRatio + 2) / 5

/-- Zeckendorf binary expansions: with `z(x)` the number of `n < x` whose binary expansion has no
two adjacent `1`s, `φ` the golden ratio and `γ = log₂ φ`, `liminf z(x) / x^γ = (3φ + 1) / 5`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 1, Equation (1) (`integers-2025-A25-thm-1`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted liminf_zeckendorfBinaryCount_div_rpow :
    Filter.liminf (fun x : ℝ =>
      ({n : ℕ | (n : ℝ) < x ∧ n &&& (n >>> 1) = 0}.ncard : ℝ) /
        x ^ Real.logb 2 Real.goldenRatio) Filter.atTop =
      (3 * Real.goldenRatio + 1) / 5

/-- Main theorem, asymptotic form: in the setting of Theorem 1 there are reals `0 < γ < 1`,
`φ̃ > 1` and a continuous function `Φ` with `z(x) ∼ x^γ Φ({log_φ̃ x})`, and `Φ` is differentiable
at almost every point of `(0, 1)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 2 (`integers-2025-A25-thm-2`; arXiv:2308.12872v1, Section 1). -/
public theorem_wanted exists_isEquivalent_subcollectionCount (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H' : ℕ → ℕ}
    (hmono : StrictMono H') (hpos : ∀ k, 0 < H' k)
    (hbij : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ γ φ' : ℝ, 0 < γ ∧ γ < 1 ∧ 1 < φ' ∧ ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun x : ℝ => (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ))
        (fun x : ℝ => x ^ γ * Φ (Int.fract (Real.logb φ' x))) ∧
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 → DifferentiableAt ℝ Φ t

/-- Growth of fundamental sequences: if `E ⊊ Ẽ` are periodic Zeckendorf collections with
fundamental sequences `H` and `H̃`, there are positive reals `α, α̃, φ, φ̃` and `r < 1` with
`H_n = α φ^(n-1) + O(φ^(nr))`, `H̃_n = α̃ φ̃^(n-1) + O(φ̃^(nr))`, `1 < φ < φ̃`, and
`H_n / H̃_n^γ → α / α̃^γ` for `γ = log_φ̃ φ`. Zero-based indices (`H n` is the paper's `H_{n+1}`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 7 (`integers-2025-A25-thm-7`; arXiv:2308.12872v1, Section 3.1). -/
public theorem_wanted fundamentalSequence_div_rpow_tendsto (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {H H' : ℕ → ℕ}
    (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) (periodicZeckendorfCollection L) Set.univ)
    (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) :
    ∃ α α' φ φ' r : ℝ, 0 < α ∧ 0 < α' ∧ 1 < φ ∧ φ < φ' ∧ 0 < r ∧ r < 1 ∧
      (fun n : ℕ => (H n : ℝ) - α * φ ^ n) =O[Filter.atTop] (fun n : ℕ => φ ^ ((n : ℝ) * r)) ∧
      (fun n : ℕ => (H' n : ℝ) - α' * φ' ^ n) =O[Filter.atTop]
        (fun n : ℕ => φ' ^ ((n : ℝ) * r)) ∧
      Filter.Tendsto (fun n : ℕ => (H n : ℝ) / (H' n : ℝ) ^ Real.logb φ' φ) Filter.atTop
        (nhds (α / α' ^ Real.logb φ' φ))

/-- Reduction lemma: for Zeckendorf collections `E ⊆ Ẽ` with fundamental sequence `H̃` of `Ẽ`,
and nonzero `μ ∈ Ẽ`, let `μ̌` be the largest element of `E` below `μ` (`<_a`) and `μ̄` its
immediate successor in `E`. Then `R(∑ μ H̃) = R(∑ μ̄ H̃)`, where `R(x)` is the set of `n < x`
of the form `∑ ε H̃` with `ε ∈ E`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 7 (`integers-2025-A25-lem-7`; arXiv:2308.12872v1, Section 3.2, with the paper's
definition of `μ̌` and `μ̄` there). -/
public theorem_wanted subcollectionLT_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H' : ℕ → ℕ} (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ) {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E')
    (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc) (hb : IsImmediateSuccessor E μc μb) :
    {n : ℕ | n < zeckendorfEval H' μ ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n} =
      {n : ℕ | n < zeckendorfEval H' μb ∧ ∃ ε ∈ E, zeckendorfEval H' ε = n}

/-- Duality formula: for Zeckendorf collections `E ⊆ Ẽ` with fundamental sequences `H` and `H̃`,
and nonzero `μ ∈ Ẽ` with `μ̌` the largest element of `E` below `μ` and `μ̄` its immediate
successor in `E`, `z(∑ μ H̃) = ∑ μ̄ H`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 8 (`integers-2025-A25-thm-8`; arXiv:2308.12872v1, Section 3.2). -/
public theorem_wanted subcollectionCount_eval_eq_eval_bar {E E' : Set (ℕ →₀ ℕ)}
    (hE : IsZeckendorfCollection E) (hE' : IsZeckendorfCollection E') (hsub : E ⊆ E')
    {H H' : ℕ → ℕ} (hmono : StrictMono H) (hpos : ∀ k, 0 < H k)
    (hbij : Set.BijOn (zeckendorfEval H) E Set.univ) (hmono' : StrictMono H')
    (hpos' : ∀ k, 0 < H' k) (hbij' : Set.BijOn (zeckendorfEval H') E' Set.univ)
    {μ μc μb : ℕ →₀ ℕ} (hμ : μ ∈ E') (hμ0 : μ ≠ 0) (hc : IsImmediatePredecessor E μ μc)
    (hb : IsImmediateSuccessor E μc μb) :
    subcollectionCount E H' (zeckendorfEval H' μ) = zeckendorfEval H μb

/-- The descending lexicographic order `ε <_d ε'` on infinite coefficient functions: at the
smallest index where they differ, `ε` is smaller.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def DescLexLT (ε ε' : ℕ → ℕ) : Prop :=
  ∃ k, ε k < ε' k ∧ ∀ j, j < k → ε j = ε' j

/-- The maximal `L*`-block `β̄` starting at (zero-based) index `s`: `0` below `s`, and
`e_j` at index `i ≥ s` with `j - 1 = (i - s) mod N` (the paper's `β̄^{s+1}`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def maxLStarBlock (L : List ℕ) (s i : ℕ) : ℕ :=
  if i < s then 0 else L.getD ((i - s) % L.length) 0

/-- For `L = (2, 3, 0)`, `β̄^2 = (0, 2, 3, 0, 2, …)` (the paper's example): entries `0, 2, 3, 0, 2`
at indices `0, …, 4`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3, example). -/
public theorem maxLStarBlock_example :
    (List.range 5).map (maxLStarBlock [2, 3, 0] 1) = [0, 2, 3, 0, 2] := by
  decide

/-- `ζ` is a proper `L*`-block with (zero-based) support interval `[s, k]`: it agrees with the
maximal block `β̄` starting at `s` below `k`, is smaller at `k`, and vanishes after `k`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsProperLStarBlock (L : List ℕ) (ζ : ℕ → ℕ) (s k : ℕ) : Prop :=
  s ≤ k ∧ (∀ i, i < k → ζ i = maxLStarBlock L s i) ∧ ζ k < maxLStarBlock L s k ∧
    ∀ i, k < i → ζ i = 0

/-- `ε` is the sum of the disjoint proper `L*`-blocks with support intervals `[p.1, p.2]`,
`p ∈ I` (finitely or infinitely many): on each interval `ε` is a proper block, and `ε` vanishes
off the intervals.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsLStarBlockSum (L : List ℕ) (I : Set (ℕ × ℕ)) (ε : ℕ → ℕ) : Prop :=
  (∀ p ∈ I, p.1 ≤ p.2) ∧ I.PairwiseDisjoint (fun p => Set.Icc p.1 p.2) ∧
    (∀ p ∈ I, (∀ i, p.1 ≤ i → i < p.2 → ε i = maxLStarBlock L p.1 i) ∧
      ε p.2 < maxLStarBlock L p.1 p.2) ∧
    ∀ i, (∀ p ∈ I, i ∉ Set.Icc p.1 p.2) → ε i = 0

/-- The periodic Zeckendorf collection `E*` for the interval `(0, 1)` determined by `L`: the
nonzero sums of finitely or infinitely many disjoint proper `L*`-blocks.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def lStarCollection (L : List ℕ) : Set (ℕ → ℕ) :=
  {ε | ε ≠ 0 ∧ ∃ I, IsLStarBlockSum L I ε}

/-- The zero coefficient function is not in `E*`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public theorem zero_notMem_lStarCollection (L : List ℕ) : (0 : ℕ → ℕ) ∉ lStarCollection L :=
  fun h => h.1 rfl

/-- Real Zeckendorf expansions: for `L = (e_1, …, e_N)` with `N ≥ 2` and `e_1 ≠ 0` there is a
unique strictly decreasing sequence `Q` in `(0, 1)` with `ε ↦ ∑ ε Q` a bijection
`E* → (0, 1)`; for it, `ε <_d δ ↔ ∑ ε Q < ∑ δ Q`, `Q_n = ∑ β̄^{n+1} Q`, and `Q_n = ω^n`
for the positive zero `ω` of `-1 + ∑_{k<N} e_k x^k + (1 + e_N) x^N`. Zero-based (`Q m` is the
paper's `Q_{m+1}`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6 (`integers-2025-A25-thm-6`; arXiv:2308.12872v1, Section 2.3, quoting Chang 2021). -/
public theorem_wanted existsUnique_lStar_fundamentalSequence (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    (∃! Q : ℕ → ℝ, StrictAnti Q ∧ (∀ n, 0 < Q n ∧ Q n < 1) ∧
      Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L) (Set.Ioo 0 1)) ∧
    ∀ Q : ℕ → ℝ, StrictAnti Q → (∀ n, 0 < Q n ∧ Q n < 1) →
      Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L) (Set.Ioo 0 1) →
      (∀ ε ∈ lStarCollection L, ∀ δ ∈ lStarCollection L,
        DescLexLT ε δ ↔ ∑' k, (ε k : ℝ) * Q k < ∑' k, (δ k : ℝ) * Q k) ∧
      (∀ m, Q m = ∑' k, (maxLStarBlock L (m + 1) k : ℝ) * Q k) ∧
      ∀ ω : ℝ, 0 < ω →
        -1 + ∑ k ∈ Finset.Ico 1 L.length, (L.getD (k - 1) 0 : ℝ) * ω ^ k +
          (1 + (L.getD (L.length - 1) 0 : ℝ)) * ω ^ L.length = 0 →
        ∀ m, Q m = ω ^ (m + 1)

/-- `inf(ε)` for `ε ∈ E*`: `ε` itself if `ε` has infinite support; otherwise, with `c` the largest
index where `ε_c ≥ 1`, the coefficient function `res_c(ε) - β^c + β̄^{c+1}` (keep `ε` below `c`,
lower `ε_c` by one, then continue with the maximal `L*`-block from `c + 1`). Zero-based.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public noncomputable def lStarInf (L : List ℕ) (ε : ℕ → ℕ) : ℕ → ℕ := by
  classical
  exact if h : ∃ c, ε c ≠ 0 ∧ ∀ i, c < i → ε i = 0 then
    fun i => if i < h.choose then ε i else if i = h.choose then ε i - 1
      else maxLStarBlock L (h.choose + 1) i
  else ε

/-- `inf(ε) = ε` when `ε` has infinite support.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public theorem lStarInf_of_infinite_support (L : List ℕ) {ε : ℕ → ℕ}
    (hε : ∀ c, ∃ i, c < i ∧ ε i ≠ 0) : lStarInf L ε = ε := by
  have h : ¬ ∃ c, ε c ≠ 0 ∧ ∀ i, c < i → ε i = 0 := by
    rintro ⟨c, -, hc⟩
    obtain ⟨i, hi, hne⟩ := hε c
    exact hne (hc i hi)
  simp [lStarInf, h]

/-- `∑ ε Q = ∑ inf(ε) Q` for `ε ∈ E*` and `Q` the fundamental sequence of `E*`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 4 (`integers-2025-A25-lem-4`; arXiv:2308.12872v1, Section 2.3). -/
public theorem_wanted tsum_lStarInf_mul_eq (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {Q : ℕ → ℝ} (hQ : StrictAnti Q) (hQ01 : ∀ n, 0 < Q n ∧ Q n < 1)
    (hbij : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L)
      (Set.Ioo 0 1)) {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L) :
    ∑' k, (ε k : ℝ) * Q k = ∑' k, (lStarInf L ε k : ℝ) * Q k

/-- Nearby expansions share long prefixes: for `ε ∈ E*` and `x = ∑ ε Q`, the expansions
`ε^± ∈ E*` of real numbers `x ± Δx` agree with `ε` (for `+`) and with `inf(ε)` (for `-`) on
indices `≤ n` once `Δx` is small enough, for every `n`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 5 (`integers-2025-A25-lem-5`; arXiv:2308.12872v1, Section 2.3). -/
public theorem_wanted exists_prefix_eq_of_lStar_near (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {Q : ℕ → ℝ} (hQ : StrictAnti Q) (hQ01 : ∀ n, 0 < Q n ∧ Q n < 1)
    (hbij : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q k) (lStarCollection L)
      (Set.Ioo 0 1)) {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L) (n : ℕ) :
    ∃ δ > 0,
      (∀ ε' ∈ lStarCollection L, ∑' k, (ε k : ℝ) * Q k < ∑' k, (ε' k : ℝ) * Q k →
        ∑' k, (ε' k : ℝ) * Q k < ∑' k, (ε k : ℝ) * Q k + δ → ∀ i ≤ n, ε' i = ε i) ∧
      (∀ ε' ∈ lStarCollection L, ∑' k, (ε k : ℝ) * Q k - δ < ∑' k, (ε' k : ℝ) * Q k →
        ∑' k, (ε' k : ℝ) * Q k < ∑' k, (ε k : ℝ) * Q k → ∀ i ≤ n, ε' i = lStarInf L ε i)

/-- Proper blocks below a maximal block: if `ε` vanishes below index `b` (zero-based), then
`ε <_d β̄^{b+1}` iff for some `k ≥ b` the restriction of `ε` to indices `≤ k` is a proper
`L*`-block with support interval `[b, k]`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 8 (`integers-2025-A25-lem-8`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted descLexLT_maxLStarBlock_iff (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} {b : ℕ} (hε : ∀ i, i < b → ε i = 0) :
    DescLexLT ε (maxLStarBlock L b) ↔
      ∃ k, b ≤ k ∧ IsProperLStarBlock L (fun i => if i ≤ k then ε i else 0) b k

/-- `L̃*`-decompositions of `L*`-blocks: if `E ⊊ Ẽ` are the periodic Zeckendorf collections
determined by `L` and `L̃`, every nonzero proper `L*`-block `ζ` with support interval `[i, b]`
is a sum of disjoint proper `L̃*`-blocks with support intervals inside `[0, b]`, one of them
ending at `b`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 9 (`integers-2025-A25-lem-9`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted exists_lStarBlockSum_of_properLStarBlock (L L' : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {ζ : ℕ → ℕ}
    {i b : ℕ} (hζ : IsProperLStarBlock L ζ i b) (hζ0 : ζ ≠ 0) :
    ∃ I, IsLStarBlockSum L' I ζ ∧ (∀ p ∈ I, p.2 ≤ b) ∧ ∃ a, (a, b) ∈ I

/-- The tail of an `L̄*`-block decomposition stays in `Ẽ*`: if `E ⊊ Ẽ` are determined by `L` and
`L̃`, `ε ∈ Ẽ*`, the part of `ε` below `b` is a sum of disjoint proper `L*`-blocks with support
intervals inside `[0, b)`, and the rest `μ` (zero below `b`) satisfies `β̄^{b+1} ≤_d μ`, then
`μ ∈ Ẽ*`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 2 (`integers-2025-A25-cor-2`; arXiv:2308.12872v1, Section 3.3). -/
public theorem_wanted mem_lStarCollection_of_lStarBar_decomposition (L L' : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {ε : ℕ → ℕ}
    (hε : ε ∈ lStarCollection L') {b : ℕ} {I : Set (ℕ × ℕ)}
    (hI : IsLStarBlockSum L I (fun i => if i < b then ε i else 0)) (hIb : ∀ p ∈ I, p.2 < b)
    (hμ : maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
      DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)) :
    (fun i => if i < b then 0 else ε i) ∈ lStarCollection L'

/-- Shifted maximal blocks: with `Q̃` the fundamental sequence of `Ẽ*` and
`ρ = ∑ β̄^1 Q̃`, `∑ β̄^ℓ Q̃ = ω̃^{ℓ-1} ρ` where `ω̃ = Q̃_1`. Zero-based (`maxLStarBlock L s` is the
paper's `β̄^{s+1}`, `Q' 0` is `Q̃_1`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 16 (`integers-2025-A25-lem-16`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted tsum_maxLStarBlock_mul_eq (L L' : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0) {Q' : ℕ → ℝ}
    (hQ' : StrictAnti Q') (hQ'01 : ∀ n, 0 < Q' n ∧ Q' n < 1)
    (hbij' : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q' k) (lStarCollection L')
      (Set.Ioo 0 1)) (s : ℕ) :
    ∑' k, (maxLStarBlock L s k : ℝ) * Q' k = Q' 0 ^ s * ∑' k, (maxLStarBlock L 0 k : ℝ) * Q' k

/-- Counting proper blocks: for `s ≤ k` with `k - s + 1 ≡ j (mod N)`, `1 ≤ j ≤ N`, there are
exactly `e_j` proper `L*`-blocks with support interval `[s, k]`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 15 (`integers-2025-A25-lem-15`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted ncard_properLStarBlock (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {s k : ℕ} (hsk : s ≤ k) :
    {ζ : ℕ → ℕ | IsProperLStarBlock L ζ s k}.ncard = L.getD ((k - s) % L.length) 0

/-- `C_n`: the number of coefficient functions that are sums of disjoint proper `L*`-blocks with
support intervals inside `[1, n]` (zero-based `[0, n)`), the zero function included; `C_0 = 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (arXiv:2308.12872v1, Section 4.1). -/
public noncomputable def lStarBlockSumCount (L : List ℕ) (n : ℕ) : ℕ :=
  {ε : ℕ → ℕ | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < n}.ncard

/-- `C_0 = 1`: only the zero function is a block sum with no support.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (arXiv:2308.12872v1, Section 4.1, `S_0 = {0}`). -/
public theorem lStarBlockSumCount_zero (L : List ℕ) : lStarBlockSumCount L 0 = 1 := by
  have h : {ε : ℕ → ℕ | ∃ I, IsLStarBlockSum L I ε ∧ ∀ p ∈ I, p.2 < 0} = {0} := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.not_lt_zero]
    constructor
    · rintro ⟨I, h, hI⟩
      funext i
      exact h.2.2.2 i (fun p hp _ => hI p hp)
    · rintro rfl
      exact ⟨∅, ⟨by simp, by simp, by simp, fun _ _ => rfl⟩, by simp⟩
  rw [lStarBlockSumCount, h, Set.ncard_singleton]

/-- Recurrence for `C_n`: `C_k = e_1 C_{k-1} + ⋯ + e_k C_0` for `1 ≤ k ≤ N`, and
`C_n = ∑_{k=1}^{N-1} e_k C_{n-k} + (1 + e_N) C_{n-N}` for `n ≥ N + 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 4 (`integers-2025-A25-prop-4`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted lStarBlockSumCount_recurrence (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    (∀ k, 1 ≤ k → k ≤ L.length → lStarBlockSumCount L k =
      ∑ j ∈ Finset.Icc 1 k, L.getD (j - 1) 0 * lStarBlockSumCount L (k - j)) ∧
    ∀ n, L.length + 1 ≤ n → lStarBlockSumCount L n =
      ∑ k ∈ Finset.Ico 1 L.length, L.getD (k - 1) 0 * lStarBlockSumCount L (n - k) +
        (1 + L.getD (L.length - 1) 0) * lStarBlockSumCount L (n - L.length)

/-- Generating function: with `f(x) = 1 - ∑_{k=1}^{N-1} e_k x^k - (1 + e_N) x^N`,
`∑ C_k x^k = (1 - x^N) / f(x)` on an open interval around `0`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 5 (`integers-2025-A25-prop-5`; arXiv:2308.12872v1, Section 4.1). -/
public theorem_wanted hasSum_lStarBlockSumCount (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Ioo (-r) r,
      HasSum (fun k => (lStarBlockSumCount L k : ℝ) * x ^ k)
        ((1 - x ^ L.length) / (1 - ∑ k ∈ Finset.Ico 1 L.length, (L.getD (k - 1) 0 : ℝ) * x ^ k -
          (1 + (L.getD (L.length - 1) 0 : ℝ)) * x ^ L.length))

/-! ### Sections 3.3-4: the function `δ*` on `(0, 1)`

Definitions and statements below follow the journal version (INTEGERS 25 (2025), Article A25,
pp. 7, 18-38). Zero-based conventions as above: the paper's `β̄^{b+1}` is `maxLStarBlock L b`, its
`β^b` is `Finsupp.single (b - 1) 1`, `res_n(ε)` keeps the indices `< n`, `Q_n` is `Q (n - 1)`,
`ω = Q 0` and `ω̃ = Q' 0` (Theorem 6 gives `Q m = ω ^ (m + 1)`), and `γ = log_φ̃ φ`
is `Real.logb (Q' 0) (Q 0)`. -/

/-- `L` and `L̃` determine periodic Zeckendorf collections `E ⊊ Ẽ` (lists of length `≥ 2` with
nonzero first entry): the standing assumption of Sections 3 and 4.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3.1. -/
public structure IsPeriodicZeckendorfPair (L L' : List ℕ) : Prop where
  two_le_length : 2 ≤ L.length
  head_ne_zero : L.getD 0 0 ≠ 0
  two_le_length' : 2 ≤ L'.length
  head_ne_zero' : L'.getD 0 0 ≠ 0
  ssubset : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L'

/-- The smaller collection of a pair is contained in the larger one.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 3.1. -/
public theorem IsPeriodicZeckendorfPair.subset {L L' : List ℕ} (h : IsPeriodicZeckendorfPair L L') :
    periodicZeckendorfCollection L ⊆ periodicZeckendorfCollection L' :=
  h.ssubset.subset

/-- Evaluation `∑ ε Q = ∑_k ε_k Q_k` of a coefficient function at a real sequence.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2.1. -/
public noncomputable def zeckendorfRealEval (Q : ℕ → ℝ) (ε : ℕ → ℕ) : ℝ :=
  ∑' k, (ε k : ℝ) * Q k

/-- `∑ 0 Q = 0`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2.1. -/
public theorem zeckendorfRealEval_zero (Q : ℕ → ℝ) : zeckendorfRealEval Q 0 = 0 := by
  simp [zeckendorfRealEval]

/-- `Q` is the fundamental sequence of `E*` (Theorem 6): strictly decreasing in `(0, 1)` with
`ε ↦ ∑ ε Q` a bijection `E* → (0, 1)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6 and Definition 18. -/
public structure IsLStarFundamentalSequence (L : List ℕ) (Q : ℕ → ℝ) : Prop where
  strictAnti : StrictAnti Q
  mem_Ioo : ∀ n, Q n ∈ Set.Ioo (0 : ℝ) 1
  bijOn : Set.BijOn (zeckendorfRealEval Q) (lStarCollection L) (Set.Ioo 0 1)

/-- The terms of a fundamental sequence are positive.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 6. -/
public theorem IsLStarFundamentalSequence.pos {L : List ℕ} {Q : ℕ → ℝ}
    (h : IsLStarFundamentalSequence L Q) (n : ℕ) : 0 < Q n :=
  (h.mem_Ioo n).1

/-- `rev_n(ε) = (ε_n, …, ε_1)`: the first `n` entries of `ε` in reverse order, a coefficient
function with finite support (zero-based: entry `j < n` is `ε (n - 1 - j)`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 5. -/
public noncomputable def zeckendorfRev (n : ℕ) (ε : ℕ → ℕ) : ℕ →₀ ℕ :=
  ∑ j ∈ Finset.range n, Finsupp.single j (ε (n - 1 - j))

/-- `rev_3(ε) = (ε_3, ε_2, ε_1)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 5. -/
public theorem zeckendorfRev_three (ε : ℕ → ℕ) :
    zeckendorfRev 3 ε =
      Finsupp.single 0 (ε 2) + Finsupp.single 1 (ε 1) + Finsupp.single 2 (ε 0) := by
  simp [zeckendorfRev, Finset.sum_range_succ]

/-- `μ̄` for a nonzero finitely supported `μ` (Definition 20): with `μ̌` the largest element of
`E` below `μ` (`<_a`), `μ̄` is the immediate successor of `μ̌` in `E` (`0` when these do not
exist).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 20. -/
public noncomputable def zeckendorfBar (E : Set (ℕ →₀ ℕ)) (μ : ℕ →₀ ℕ) : ℕ →₀ ℕ := by
  classical
  exact if h : ∃ μb μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc μb then
    h.choose else 0

/-- When `μ̌` and its successor exist, `μ̄` is that successor.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 20. -/
public theorem zeckendorfBar_spec {E : Set (ℕ →₀ ℕ)} {μ : ℕ →₀ ℕ}
    (h : ∃ μb μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc μb) :
    ∃ μc, IsImmediatePredecessor E μ μc ∧ IsImmediateSuccessor E μc (zeckendorfBar E μ) := by
  rw [zeckendorfBar, dite_eq_left h]
  exact h.choose_spec

/-- The collection `Ē*` (Definition 22): `E*` together with the coefficient functions
`∑ ζ^m + β̄^{b+1}`, a sum of disjoint proper `L*`-blocks with support intervals inside `[1, b]`
followed by the maximal block from index `b + 1` (`b = 0` gives `β̄^1`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 22. -/
public def lStarClosure (L : List ℕ) : Set (ℕ → ℕ) :=
  lStarCollection L ∪ {ε | ∃ b I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
    (∀ p ∈ I, p.2 < b) ∧ ∀ i, b ≤ i → ε i = maxLStarBlock L b i}

/-- `β̄^1 ∈ Ē*` (the case `b = 0`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 22. -/
public theorem maxLStarBlock_zero_mem_lStarClosure (L : List ℕ) :
    maxLStarBlock L 0 ∈ lStarClosure L :=
  Set.mem_union_right _ ⟨0, ∅, ⟨by simp, by simp, by simp, fun i _ => by simp⟩, by simp,
    fun _ _ => rfl⟩

/-- `rev̄(ε)` (Definition 23): `β̄^1` if `β̄^1 ≤_d ε`, and otherwise the coordinatewise limit of
`rev_n(\overline{rev_n(ε)})` as `n → ∞` (each coordinate is eventually constant by Lemma 10; `0`
for a coordinate that is not).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfRevBar (L : List ℕ) (ε : ℕ → ℕ) : ℕ → ℕ := by
  classical
  exact if DescLexLT ε (maxLStarBlock L 0) then
    fun i => if h : ∃ v, ∀ᶠ n in Filter.atTop,
        zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε)) i = v
      then h.choose else 0
  else maxLStarBlock L 0

/-- `rev̄(ε) = β̄^1` when `ε <_d β̄^1` fails.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public theorem zeckendorfRevBar_of_not_descLexLT (L : List ℕ) {ε : ℕ → ℕ}
    (h : ¬ DescLexLT ε (maxLStarBlock L 0)) : zeckendorfRevBar L ε = maxLStarBlock L 0 := by
  rw [zeckendorfRevBar, ite_eq_right h]

/-- `δ1*(y) = ∑ rev̄(ε) Q / y^γ` where `ε ∈ Ẽ*` is the expansion `y = ∑ ε Q̃` (Definition 23;
used on `[ω̃, 1)`; `0` if `y` has no expansion).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfDeltaStarOne (L L' : List ℕ) (Q Q' : ℕ → ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : ∃ ε ∈ lStarCollection L', zeckendorfRealEval Q' ε = y then
    zeckendorfRealEval Q (zeckendorfRevBar L h.choose) / y ^ Real.logb (Q' 0) (Q 0) else 0

/-- `δ*(y) = δ1*(y / ω̃^m)` for `y ∈ [ω̃^{m+1}, ω̃^m)` (Definition 23; `0` outside `(0, 1)`).
The printed definition reduces `y` by powers of `ω`; since `δ1*` lives on `[ω̃, 1)`, Proposition 2
and Equation (12) evaluate `δ*` on `[ω̃, 1)` as `δ1*`, and the proof of Theorem 9 glues
`δ1*(ω̃) = lim_{x → 1⁻} δ1*(x)`, the reduction is by powers of `ω̃` (Notation 1).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public noncomputable def zeckendorfDeltaStar (L L' : List ℕ) (Q Q' : ℕ → ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : ∃ m : ℕ, Q' 0 ^ (m + 1) ≤ y ∧ y < Q' 0 ^ m then
    zeckendorfDeltaStarOne L L' Q Q' (y / Q' 0 ^ h.choose) else 0

/-- `δ* = δ1*` on `[ω̃, 1)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 23. -/
public theorem zeckendorfDeltaStar_of_mem_Ico {L L' : List ℕ} {Q Q' : ℕ → ℝ} (h0 : 0 < Q' 0)
    (h1 : Q' 0 < 1) {y : ℝ} (hy : Q' 0 ≤ y) (hy1 : y < 1) :
    zeckendorfDeltaStar L L' Q Q' y = zeckendorfDeltaStarOne L L' Q Q' y := by
  have h : ∃ m : ℕ, Q' 0 ^ (m + 1) ≤ y ∧ y < Q' 0 ^ m := ⟨0, by simpa using hy, by simpa using hy1⟩
  have hm : h.choose = 0 := by
    by_contra hne
    have h2 := h.choose_spec.2
    have h3 := pow_le_of_le_one h0.le h1.le hne
    linarith
  rw [zeckendorfDeltaStar, dite_eq_left h, hm, pow_zero, div_one]

/-- The exponent `p` of the generic upper bound of `δ*` (Definition 25): the smallest positive
integer with `γ ω̃^{p-1} < ω^p`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 25. -/
public noncomputable def zeckendorfGenericExponent (Q Q' : ℕ → ℝ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ Real.logb (Q' 0) (Q 0) * Q' 0 ^ (p - 1) < Q 0 ^ p}

/-- When some positive integer satisfies the defining inequality, `p` does.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 25. -/
public theorem zeckendorfGenericExponent_spec {Q Q' : ℕ → ℝ}
    (h : ∃ p : ℕ, 0 < p ∧ Real.logb (Q' 0) (Q 0) * Q' 0 ^ (p - 1) < Q 0 ^ p) :
    0 < zeckendorfGenericExponent Q Q' ∧
      Real.logb (Q' 0) (Q 0) * Q' 0 ^ (zeckendorfGenericExponent Q Q' - 1) <
        Q 0 ^ zeckendorfGenericExponent Q Q' :=
  Nat.sInf_mem h

/-- The set `U = eval_Q̃(Ẽ* − Ē*)` (Notation 2).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Notation 2. -/
public noncomputable def zeckendorfSmoothSet (L L' : List ℕ) (Q' : ℕ → ℝ) : Set ℝ :=
  zeckendorfRealEval Q' '' (lStarCollection L' \ lStarClosure L)

/-- Membership in `U`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Notation 2. -/
public theorem mem_zeckendorfSmoothSet_iff {L L' : List ℕ} {Q' : ℕ → ℝ} {x : ℝ} :
    x ∈ zeckendorfSmoothSet L L' Q' ↔
      ∃ ε ∈ lStarCollection L', ε ∉ lStarClosure L ∧ zeckendorfRealEval Q' ε = x := by
  simp [zeckendorfSmoothSet, and_assoc]

/-- Lemma 3, read for nonzero `ε` with the case `b = 0` (`ε = β̄^1`) included: `rev_n(ε) ∈ E` for
all `n` iff `ε ∈ Ē*`. As printed (no `ε ≠ 0`, decompositions with `n ≥ 1` blocks) it fails at
`ε = 0` (`rev_n(0) = 0 ∈ E`) and at `ε = β̄^1` (`rev_n(β̄^1) = θ^{n+1} ∈ E`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 3 (`integers-2025-A25-lem-3`). -/
public theorem_wanted forall_zeckendorfRev_mem_iff_mem_lStarClosure (L : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} (hε : ε ≠ 0) :
    (∀ n, zeckendorfRev n ε ∈ periodicZeckendorfCollection L) ↔ ε ∈ lStarClosure L

/-- `L̄*`-block decompositions (Corollary 1): for `ε ∈ Ẽ*`, either `ε ∈ E*` (the case `ℓ = ∞`) and
no index `b` as below exists, or there is a unique `b` (the largest `L̄*`-support index) such that
the part of `ε` below `b` is a sum of disjoint proper `L*`-blocks inside `[1, b]` and the rest `μ`
satisfies `β̄^{b+1} ≤_d μ` (`b = 0` is the case `ℓ = 0`, `ε = μ`). The decomposition is recorded
by its index `b`, which determines the blocks.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 1 (`integers-2025-A25-cor-1`). -/
public theorem_wanted lStarBar_decomposition {L L' : List ℕ} (hp : IsPeriodicZeckendorfPair L L')
    {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    (ε ∈ lStarCollection L ↔ ¬ ∃ b I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
        (∀ p ∈ I, p.2 < b) ∧ (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
          DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i))) ∧
    (ε ∉ lStarCollection L → ∃! b, ∃ I, IsLStarBlockSum L I (fun i => if i < b then ε i else 0) ∧
        (∀ p ∈ I, p.2 < b) ∧ (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
          DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)))

open Classical in
/-- Lemma 10: let `ε ∈ Ẽ*` with `ε <_d β̄^1`. If `ε ∈ E*`, then
`rev_n(\overline{rev_n(ε)}) = res_n(ε)` for all `n ≥ 1`. If `ε` has an `L̄*`-block decomposition
with largest support index `b ≥ 1` (part below `b` a sum of disjoint proper `L*`-blocks inside
`[1, b]`, rest `μ` with `β̄^{b+1} ≤_d μ`), then for all large `n` the left side is
`∑ ζ^m + β^b` if `β̄^{b+1} <_d μ` and `res_n(ε)` if `μ = β̄^{b+1}`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 10 (`integers-2025-A25-lem-10`). -/
public theorem_wanted zeckendorfRev_bar_zeckendorfRev_eq {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hlt : DescLexLT ε (maxLStarBlock L 0)) :
    (ε ∈ lStarCollection L → ∀ n, 1 ≤ n →
      ⇑(zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε))) =
        fun i => if i < n then ε i else 0) ∧
    ∀ b I, 1 ≤ b → IsLStarBlockSum L I (fun i => if i < b then ε i else 0) →
      (∀ p ∈ I, p.2 < b) →
      (maxLStarBlock L b = (fun i => if i < b then 0 else ε i) ∨
        DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i)) →
      ∀ᶠ n in Filter.atTop,
        ⇑(zeckendorfRev n (zeckendorfBar (periodicZeckendorfCollection L) (zeckendorfRev n ε))) =
          if DescLexLT (maxLStarBlock L b) (fun i => if i < b then 0 else ε i) then
            (fun i => if i < b then ε i else 0) + ⇑(Finsupp.single (b - 1) 1)
          else fun i => if i < n then ε i else 0

/-- Lemma 11: for `ε ∈ Ẽ*`, `ε ∈ Ē*` iff `rev̄(ε) = ε`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 11 (`integers-2025-A25-lem-11`). -/
public theorem_wanted mem_lStarClosure_iff_zeckendorfRevBar_eq {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    ε ∈ lStarClosure L ↔ zeckendorfRevBar L ε = ε

/-- Lemma 12: let `μ ∈ Ẽ` have order `t ≥ 1` (last nonzero entry at zero-based index `t - 1`),
and let `β̂^{t+1} = θ^{t+1}` be the immediate predecessor of `β^{t+1}` in `E`. If
`μ ≤_a β̂^{t+1}`, then `rev̄(rev_t(μ)) = rev_t(μ̄)`; if `β̂^{t+1} <_a μ`, then
`rev̄(rev_t(μ)) = β̄^1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 12 (`integers-2025-A25-lem-12`). -/
public theorem_wanted zeckendorfRevBar_zeckendorfRev_of_order {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {μ : ℕ →₀ ℕ} (hμ : μ ∈ periodicZeckendorfCollection L')
    {t : ℕ} (ht : 1 ≤ t) (hord : μ (t - 1) ≠ 0 ∧ ∀ j, t ≤ j → μ j = 0) :
    ((μ = periodicTheta L t ∨ AscLexLT μ (periodicTheta L t)) →
      zeckendorfRevBar L (zeckendorfRev t μ) =
        ⇑(zeckendorfRev t (zeckendorfBar (periodicZeckendorfCollection L) μ))) ∧
    (AscLexLT (periodicTheta L t) μ → zeckendorfRevBar L (zeckendorfRev t μ) = maxLStarBlock L 0)

/-- Transition to `δ*` (Proposition 2): with `H`, `H̃` the fundamental sequences of `E ⊊ Ẽ`,
`α = lim H_n / φ^{n-1}`, `α̃ = lim H̃_n / φ̃^{n-1}` (`φ = 1/ω`, `φ̃ = 1/ω̃`), and `x = ∑ μ_x H̃`
with `μ_x ∈ Ẽ` of order `n`, `δ(x) = z(x)/x^γ ∼ δ*(∑ rev_n(μ_x) Q̃) α / α̃^γ` as `x → ∞`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 2 (`integers-2025-A25-prop-2`). -/
public theorem_wanted isEquivalent_subcollectionCount_div_rpow_deltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {H H' : ℕ → ℕ} (hmono : StrictMono H)
    (hpos : ∀ k, 0 < H k) (hbij : Set.BijOn (zeckendorfEval H) (periodicZeckendorfCollection L) Set.univ)
    (hmono' : StrictMono H') (hpos' : ∀ k, 0 < H' k)
    (hbij' : Set.BijOn (zeckendorfEval H') (periodicZeckendorfCollection L') Set.univ) {α α' : ℝ}
    (hα : Filter.Tendsto (fun n => (H n : ℝ) * Q 0 ^ n) Filter.atTop (nhds α))
    (hα' : Filter.Tendsto (fun n => (H' n : ℝ) * Q' 0 ^ n) Filter.atTop (nhds α'))
    {μ : ℕ → ℕ →₀ ℕ}
    (hμ : ∀ x, μ x ∈ periodicZeckendorfCollection L' ∧ zeckendorfEval H' (μ x) = x) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℕ => (subcollectionCount (periodicZeckendorfCollection L) H' x : ℝ) /
        (x : ℝ) ^ Real.logb (Q' 0) (Q 0))
      (fun x : ℕ => zeckendorfDeltaStar L L' Q Q'
          (zeckendorfRealEval Q' (zeckendorfRev ((μ x).support.sup (· + 1)) (μ x))) *
        (α / α' ^ Real.logb (Q' 0) (Q 0)))

/-- Behaviour of `rev̄` near `ε ∈ Ẽ*` (Lemma 13), with `x = ∑ ε Q̃` and `ε^±` the expansions of
nearby points: if `ε ∉ Ē*`, `rev̄` is constant near `x`; if `ε ∈ Ē* − E*`, then
`inf_{E*}(rev̄(ε^+)) = rev̄(ε)` just to the right, and `rev̄(ε^-)` agrees with `rev̄(ε)` on any
prefix just to the left; if `ε ∈ E*`, `rev̄(ε^±)` agree with `rev̄(ε)` on any prefix near `x`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 13 (`integers-2025-A25-lem-13`). -/
public theorem_wanted zeckendorfRevBar_eventually_near {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q')
    {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L') :
    (ε ∉ lStarClosure L → ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
      |zeckendorfRealEval Q' ε' - zeckendorfRealEval Q' ε| < δ →
        zeckendorfRevBar L ε' = zeckendorfRevBar L ε) ∧
    (ε ∈ lStarClosure L → ε ∉ lStarCollection L →
      (∃ δ > 0, ∀ ε' ∈ lStarCollection L', zeckendorfRealEval Q' ε < zeckendorfRealEval Q' ε' →
        zeckendorfRealEval Q' ε' < zeckendorfRealEval Q' ε + δ →
          lStarInf L (zeckendorfRevBar L ε') = zeckendorfRevBar L ε) ∧
      ∀ n, ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
        zeckendorfRealEval Q' ε - δ < zeckendorfRealEval Q' ε' →
          zeckendorfRealEval Q' ε' < zeckendorfRealEval Q' ε →
            ∀ i < n, zeckendorfRevBar L ε' i = zeckendorfRevBar L ε i) ∧
    (ε ∈ lStarCollection L → ∀ n, ∃ δ > 0, ∀ ε' ∈ lStarCollection L',
      |zeckendorfRealEval Q' ε' - zeckendorfRealEval Q' ε| < δ →
        ∀ i < n, zeckendorfRevBar L ε' i = zeckendorfRevBar L ε i)

/-- Lemma 14: if `ε ∈ Ē*` is not a finitely supported member of `E*`, then `ε - β^r ∈ Ē*` for
infinitely many indices `r` (with `ε_r ≥ 1`).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 14 (`integers-2025-A25-lem-14`). -/
public theorem_wanted infinite_setOf_sub_single_mem_lStarClosure (L : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L)
    (hfin : ¬ (ε ∈ lStarCollection L ∧ ∃ M, ∀ i, M < i → ε i = 0)) :
    {r | 1 ≤ ε r ∧ Function.update ε r (ε r - 1) ∈ lStarClosure L}.Infinite

/-- Proposition 3: `U` is the disjoint union of the open intervals `(x_ε, x'_ε)` over
`ε = ∑ ζ^m + β̄^{b+1} ∈ Ē* − E*`, where `x_ε = ∑ ε Q̃` and `x'_ε = ∑ (∑ ζ^m + β^b) Q̃`
(`= ∑ (∑ ζ^m) Q̃ + ω̃^b`, read as `1` for `b = 0`); in particular `U` is open and measurable.
Members of `Ē* − E*` are indexed by `(b, ∑ ζ^m)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 3 (`integers-2025-A25-prop-3`). -/
public theorem_wanted zeckendorfSmoothSet_eq_iUnion {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q') :
    zeckendorfSmoothSet L L' Q' =
      (⋃ (b : ℕ) (η : ℕ → ℕ) (_ : (∃ I, IsLStarBlockSum L I η ∧ ∀ p ∈ I, p.2 < b) ∧
          η + maxLStarBlock L b ∉ lStarCollection L),
        Set.Ioo (zeckendorfRealEval Q' (η + maxLStarBlock L b))
          (zeckendorfRealEval Q' η + Q' 0 ^ b)) ∧
    (∀ b η b' η', (∃ I, IsLStarBlockSum L I η ∧ ∀ p ∈ I, p.2 < b) →
      η + maxLStarBlock L b ∉ lStarCollection L →
      (∃ I, IsLStarBlockSum L I η' ∧ ∀ p ∈ I, p.2 < b') →
      η' + maxLStarBlock L b' ∉ lStarCollection L → (b, η) ≠ (b', η') →
      Disjoint (Set.Ioo (zeckendorfRealEval Q' (η + maxLStarBlock L b))
          (zeckendorfRealEval Q' η + Q' 0 ^ b))
        (Set.Ioo (zeckendorfRealEval Q' (η' + maxLStarBlock L b'))
          (zeckendorfRealEval Q' η' + Q' 0 ^ b'))) ∧
    IsOpen (zeckendorfSmoothSet L L' Q') ∧ MeasurableSet (zeckendorfSmoothSet L L' Q')

/-- Theorem 9: `δ*` is continuous on `(0, 1)`, and at each point of `U` it is differentiable and
strictly decreasing on a neighbourhood.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 9 (`integers-2025-A25-thm-9`). -/
public theorem_wanted continuousOn_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    ContinuousOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) ∧
      ∀ x ∈ zeckendorfSmoothSet L L' Q', DifferentiableAt ℝ (zeckendorfDeltaStar L L' Q Q') x ∧
        ∃ s ∈ nhds x, StrictAntiOn (zeckendorfDeltaStar L L' Q Q') s

/-- Theorem 10: `δ*` is not differentiable at any point of `eval_Q̃(Ē*)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 10 (`integers-2025-A25-thm-10`). -/
public theorem_wanted not_differentiableAt_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L) :
    ¬ DifferentiableAt ℝ (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- Theorem 11: `U` has Lebesgue measure `1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 11 (`integers-2025-A25-thm-11`). -/
public theorem_wanted volume_zeckendorfSmoothSet {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q' : ℕ → ℝ} (hQ' : IsLStarFundamentalSequence L' Q') :
    MeasureTheory.volume (zeckendorfSmoothSet L L' Q') = 1

/-- Proposition 6: `δ*` has a local minimum at each point `∑ ε Q̃` with `ε ∈ E*_∘` (finite support).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 6 (`integers-2025-A25-prop-6`). -/
public theorem_wanted isLocalMin_zeckendorfDeltaStar_of_finite {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L)
    (hfin : ∃ M, ∀ i, M < i → ε i = 0) :
    IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- Proposition 7: `δ*` has no local extremum at the points `∑ ε Q̃` with `ε ∈ E* − E*_∘`
(infinite support).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 7 (`integers-2025-A25-prop-7`). -/
public theorem_wanted not_isLocalExtr_zeckendorfDeltaStar_of_infinite {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L)
    (hinf : ∀ M, ∃ i, M < i ∧ ε i ≠ 0) :
    ¬ IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε) ∧
      ¬ IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- Proposition 8: at each point `x = ∑ ε Q̃` with `ε ∈ Ē* − E*`, `δ*` has a strict local maximum
(a local maximum attained only at `x` nearby).

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Proposition 8 (`integers-2025-A25-prop-8`). -/
public theorem_wanted eventually_zeckendorfDeltaStar_lt_of_mem_lStarClosure {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarClosure L)
    (hε' : ε ∉ lStarCollection L) :
    ∀ᶠ y in nhdsWithin (zeckendorfRealEval Q' ε) {zeckendorfRealEval Q' ε}ᶜ,
      zeckendorfDeltaStar L L' Q Q' y < zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε)

/-- Theorem 12: `δ*` has no local extremum at the points of `eval_Q̃((Ẽ* − Ē*) ∪ (E* − E*_∘))`, a
local minimum at the points of `eval_Q̃(E*_∘)`, and a local maximum at the points of
`eval_Q̃(Ē* − E*)`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 12 (`integers-2025-A25-thm-12`). -/
public theorem_wanted isLocalExtr_zeckendorfDeltaStar_classification {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ ε ∈ lStarCollection L', (ε ∉ lStarClosure L ∨
        (ε ∈ lStarCollection L ∧ ∀ M, ∃ i, M < i ∧ ε i ≠ 0)) →
      ¬ IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε) ∧
        ¬ IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)) ∧
    (∀ ε ∈ lStarCollection L, (∃ M, ∀ i, M < i → ε i = 0) →
      IsLocalMin (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)) ∧
    ∀ ε ∈ lStarClosure L, ε ∉ lStarCollection L →
      IsLocalMax (zeckendorfDeltaStar L L' Q Q') (zeckendorfRealEval Q' ε)

/-- Lemma 17, with the middle bound read for `∑ ε Q̃ ≥ ω̃` (the normalization `ε_1 ≥ 1` its proof
assumes): `δ*[ε] < γ⁻¹ (ω/ω̃)^p` for every `ε ∈ Ẽ*`, and if `∑ ε Q̃ ≥ ω̃`, then
`δ*[ε] < ∑ rev̄(ε) Q / ∑ ε Q̃ < γ⁻¹ (ω/ω̃)^p`. As printed (for all `ε ∈ Ẽ*`) the middle bound fails:
for `L = (1, 0)`, `L̃ = (1, 1)` (`p = 2`) and `ε = β^4`, `rev̄(ε) = ε` and
`∑ rev̄(ε) Q / ∑ ε Q̃ = 16 ω^4 = 2.33436… > γ⁻¹ (ω/ω̃)^2 = 2.20076…`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 17 (`integers-2025-A25-lem-17`). -/
public theorem_wanted zeckendorfDeltaStar_lt_genericBound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ ε ∈ lStarCollection L', zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) <
      (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' / Real.logb (Q' 0) (Q 0)) ∧
    ∀ ε ∈ lStarCollection L', Q' 0 ≤ zeckendorfRealEval Q' ε →
      zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) <
          zeckendorfRealEval Q (zeckendorfRevBar L ε) / zeckendorfRealEval Q' ε ∧
        zeckendorfRealEval Q (zeckendorfRevBar L ε) / zeckendorfRealEval Q' ε <
          (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' / Real.logb (Q' 0) (Q 0)

/-- Lemma 18, read for `x = ∑ ε Q̃ ≥ ω̃` (as Lemma 17): with `y = ∑ rev̄(ε) Q`, positive `Δx`, `Δy`
with `(ω/ω̃)^p ≤ Δy/Δx` give `y/x^γ < (y + Δy)/(x + Δx)^γ`. As printed (all `ε ∈ Ẽ*`) it fails for
`L = (1, 0)`, `L̃ = (1, 1)`, `ε = β^4` (`x = 1/16`, `y = ω^4`, `y/x^γ = 1`),
`Δx = 10⁻⁸`, `Δy = (ω/ω̃)^2 Δx`: the right side is `0.99999999364…`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 18 (`integers-2025-A25-lem-18`). -/
public theorem_wanted div_rpow_lt_add_div_add_rpow_of_genericBound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hx : Q' 0 ≤ zeckendorfRealEval Q' ε) {Δx Δy : ℝ} (hΔx : 0 < Δx) (hΔy : 0 < Δy)
    (hΔ : (Q 0 / Q' 0) ^ zeckendorfGenericExponent Q Q' ≤ Δy / Δx) :
    zeckendorfRealEval Q (zeckendorfRevBar L ε) /
        zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) <
      (zeckendorfRealEval Q (zeckendorfRevBar L ε) + Δy) /
        (zeckendorfRealEval Q' ε + Δx) ^ Real.logb (Q' 0) (Q 0)

/-- Corollary 3, read for `x = ∑ ε Q̃ ≥ ω̃` (as Lemma 17): for `n ≥ p`,
`δ*[ε] = ∑ rev̄(ε) Q / x^γ < (∑ rev̄(ε) Q + Q_n)/(x + Q̃_n)^γ` (zero-based `Q_n = Q m`,
`n = m + 1`). As printed (all `ε ∈ Ẽ*`) it fails for `L = (1, 0)`, `L̃ = (1, 1)`, `n = p = 2`,
`ε = β^{11} + β^{13} ∈ E*` (`rev̄(ε) = ε`): `1.18363… > 1.01645…`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Corollary 3 (`integers-2025-A25-cor-3`). -/
public theorem_wanted zeckendorfDeltaStar_lt_add_fundamental {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') {ε : ℕ → ℕ} (hε : ε ∈ lStarCollection L')
    (hx : Q' 0 ≤ zeckendorfRealEval Q' ε) {m : ℕ} (hm : zeckendorfGenericExponent Q Q' ≤ m + 1) :
    zeckendorfDeltaStar L L' Q Q' (zeckendorfRealEval Q' ε) =
        zeckendorfRealEval Q (zeckendorfRevBar L ε) /
          zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) ∧
      zeckendorfRealEval Q (zeckendorfRevBar L ε) /
          zeckendorfRealEval Q' ε ^ Real.logb (Q' 0) (Q 0) <
        (zeckendorfRealEval Q (zeckendorfRevBar L ε) + Q m) /
          (zeckendorfRealEval Q' ε + Q' m) ^ Real.logb (Q' 0) (Q 0)

/-- Theorem 13: a maximum of `δ*` on `(0, 1)` is attained only at points of `eval_Q̃(Ē* − E*)`; if
`ε = ∑ ζ^m + β̄^ℓ` (proper `L*`-blocks inside `[1, ℓ - 1]`, `ℓ ≥ 1`) and `δ*[ε]` is the maximum,
then `ℓ < max{2, p*}` with `p* = p + 1 + (N ln φ + ln(1 - ρ + ω̃^N)) / (ln φ̃ - ln φ)`,
`ρ = ∑ β̄^1 Q̃`, `N` the length of `L`, `φ = 1/ω`, `φ̃ = 1/ω̃`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 13 (`integers-2025-A25-thm-13`). -/
public theorem_wanted isMaxOn_zeckendorfDeltaStar_bound {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∀ y ∈ Set.Ioo (0 : ℝ) 1, IsMaxOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) y →
      ∃ ε ∈ lStarClosure L, ε ∉ lStarCollection L ∧ zeckendorfRealEval Q' ε = y) ∧
    ∀ (ℓ : ℕ) (η : ℕ → ℕ) (I : Set (ℕ × ℕ)), 1 ≤ ℓ → IsLStarBlockSum L I η →
      (∀ p ∈ I, p.2 < ℓ - 1) →
      IsMaxOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1)
        (zeckendorfRealEval Q' (η + maxLStarBlock L (ℓ - 1))) →
      (ℓ : ℝ) < max 2 (zeckendorfGenericExponent Q Q' + 1 +
        (L.length * Real.log (Q 0)⁻¹ +
          Real.log (1 - zeckendorfRealEval Q' (maxLStarBlock L 0) + Q' 0 ^ L.length)) /
        (Real.log (Q' 0)⁻¹ - Real.log (Q 0)⁻¹))

/-- Theorem 14: with `p† = max{2, p}`, the minimum of `δ*` on `(0, 1)` is attained at `∑ ε Q̃` for
some `ε ∈ E*` with `res^{p†}(ε) = 0` (entries at indices `≥ p†` vanish); if `p ≤ 2`, the minimum
value is `δ*[β^1] = δ*(ω̃) = 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 14 (`integers-2025-A25-thm-14`). -/
public theorem_wanted exists_isMinOn_zeckendorfDeltaStar {L L' : List ℕ}
    (hp : IsPeriodicZeckendorfPair L L') {Q Q' : ℕ → ℝ} (hQ : IsLStarFundamentalSequence L Q)
    (hQ' : IsLStarFundamentalSequence L' Q') :
    (∃ ε ∈ lStarCollection L, (∀ i, max 2 (zeckendorfGenericExponent Q Q') - 1 ≤ i → ε i = 0) ∧
      IsMinOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) (zeckendorfRealEval Q' ε)) ∧
    (zeckendorfGenericExponent Q Q' ≤ 2 →
      IsMinOn (zeckendorfDeltaStar L L' Q Q') (Set.Ioo 0 1) (Q' 0) ∧
        zeckendorfDeltaStar L L' Q Q' (Q' 0) = 1)

/-- Lemma 19 for the `N`th order Zeckendorf collection `L = (1, …, 1, 0)` (`N - 1` ones) inside
the base-`N` collection `L̃ = (N - 1, …, N - 1)`: `p = 1` for `N ≥ 4`; and for `N ≥ 3`, if
`ε ∈ E*` has `ε_1 ≥ 1`, `ε_n = 1` (`n ≥ 3`) and a proper block with support interval
`[i, n - 1]`, then `ε' = ε + β^{n-1} - β^n ∈ E*` and `δ*[ε] < δ*[ε']`. As printed, `p = 1` fails
for `N = 3` (`γ = 0.55467… > ω = 0.54368…`, so `p = 2`), and `δ*[ε] < δ*[ε']` fails without
`ε_1 ≥ 1` (the normalization used where the paper applies it): `ε = β^4`, `ε' = β^3` give
`δ*[ε] = δ*[ε'] = 1`.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 19 (`integers-2025-A25-lem-19`). -/
public theorem_wanted zeckendorfDeltaStar_lt_shift_baseN {N : ℕ} (hN : 3 ≤ N) {Q Q' : ℕ → ℝ}
    (hQ : IsLStarFundamentalSequence (List.replicate (N - 1) 1 ++ [0]) Q)
    (hQ' : IsLStarFundamentalSequence (List.replicate N (N - 1)) Q') :
    (4 ≤ N → zeckendorfGenericExponent Q Q' = 1) ∧
    ∀ ε ∈ lStarCollection (List.replicate (N - 1) 1 ++ [0]), 1 ≤ ε 0 →
      ∀ (n i : ℕ) (I : Set (ℕ × ℕ)), 3 ≤ n → ε (n - 1) = 1 →
        IsLStarBlockSum (List.replicate (N - 1) 1 ++ [0]) I ε → (i, n - 2) ∈ I →
        ε + Pi.single (n - 2) 1 - Pi.single (n - 1) 1 ∈
            lStarCollection (List.replicate (N - 1) 1 ++ [0]) ∧
          zeckendorfDeltaStar (List.replicate (N - 1) 1 ++ [0]) (List.replicate N (N - 1)) Q Q'
              (zeckendorfRealEval Q' ε) <
            zeckendorfDeltaStar (List.replicate (N - 1) 1 ++ [0]) (List.replicate N (N - 1)) Q Q'
              (zeckendorfRealEval Q' (ε + Pi.single (n - 2) 1 - Pi.single (n - 1) 1))

end

end MetaMathlibExt
