/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Two-sequence alignment

**E-value bound, explicit cross-diagonal dependence at finite size, and a Gumbel limit
conditional on asymptotic independence** (given a one-sequence tail input, intended for the
classical nonlattice regime with `K > 0`).

Two independent iid sequences `u` (length `m`, letter law `p`) and `v` (length `n`, letter law
`q`) over a finite alphabet are compared with a scoring matrix `s`. An **ungapped alignment** pairs
the window `u[i, i+ℓ)` with `v[j, j+ℓ)` and scores `∑_{k<ℓ} s(u_{i+k}, v_{j+k})`; the **maximal
segment score** `M_{m,n}` (`maxAlignScore`) is the best such score, the empty alignment scoring
`0`. (`alignScore s u v i j ℓ` takes `ℓ` as a length bound: windows running past the end of a
sequence are truncated, so it is the score of the alignment of length
`min ℓ (min (|u| - i) (|v| - j))` (`alignScore_eq_min`), and the maximum over all triples is
still the best score of a genuine alignment.) Karlin and Altschul (1990) and Dembo, Karlin and
Zeitouni (1994) showed that for negative expected score,
`P(M_{m,n} ≤ log (m n) / λ + x) → exp (-K e^{-λ x})`, where `λ` solves
`E e^{λ s(A, B)} = 1` and `K` is the constant of the single-sequence theory.

## Structure, and where the dependence between diagonals enters

Every ungapped alignment lies on one diagonal `j - i = d` of the `m × n` grid, so
`M_{m,n} = max_d M_d`, where `M_d` is the one-sequence maximal segment score
(`SingleSequence.maxSegScore`) of the score sequence along diagonal `d`. Each diagonal on its own is
an iid score sequence with the law of `s(A, B)`; but two diagonals that share a letter of `u` or `v`
are **not independent**, so `M_{m,n}` is not the maximum of independent one-sequence maxima. The
dependence is isolated in `Δ_k` at every finite size; the limit takes `Δ_k → 0` as a hypothesis (it
is the Poisson-approximation step of Dembo–Karlin–Zeitouni, not proved here; it can fail when
their entropy condition fails).

1. *Diagonal decomposition* (pathwise, proved): `maxSegScore_diag_le`,
   `exists_maxSegScore_diag_eq`, `maxAlignScore_le_iff`; the diagonal lengths add up to `m n`
   (`sum_diagLen`).
2. *Single-diagonal slice* (proved): `twoExpect_diag` / `twoProb_diag`: the scores along a diagonal
   of length `L` have the law of `L` iid pair scores, i.e. the one-sequence model of
   `SingleSequence` over the pair alphabet `β × β` with law `pairLaw p q` and score `pairScore s`.
3. *Dependence structure* (proved): diagonals reading disjoint sets of letters are independent
   (`twoProb_diag_and_diag_of_disjoint`); diagonals sharing letters are in general dependent
   (counterexample in the test file).
4. *Dependence isolation* (proved): with `W` the number of diagonals with a segment scoring more
   than `t` and `p_d = P(M_d > t)`, the Bonferroni inequalities of every order sandwich
   `P(M_{m,n} ≤ t) = P(W = 0)` between alternating partial sums of the factorial moments
   `S_k = E[C(W, k)]` (`twoProb_maxAlignScore_le_le`, `le_twoProb_maxAlignScore_le`). Writing
   `S_k = e_k(p) + Δ_k`, where `e_k(p)` is the value for independent diagonals with the same
   marginals, the cross-diagonal dependence enters *only* through the coefficients
   `Δ_k = crossDep … k` (`crossDep_eq_sum`: `Δ_k = ∑_{|T| = k} (P(⋂_T {M_d > t}) - ∏_T p_d)`),
   with `Δ_0 = Δ_1 = 0`. `twoProb_maxAlignScore_le_second_order` is the explicit second-order
   case `1 - ∑ p_d ≤ P(M ≤ t) ≤ 1 - ∑ p_d + e_2(p) + Δ_2`.
5. *Marginals* (proved from the one-sequence input): at `t = log (m n) / θ + x`, with
   `log n / m → 0` and `log m / n → 0`, `∑_d p_d → K e^{-θ x}` (`tendsto_sum_exceedProb`;
   diagonals of length at least `ℓ = max L₀ ⌈t / η⌉ = o(min m n)` use the one-sequence tail, the
   at most `2 ℓ` shorter ones the Cramér bound of `SingleSequence`) and `max_d p_d → 0`, so
   `e_k(p) → (K e^{-θ x})^k / k!` (`tendsto_elemSymm`).
6. *Poisson limit* (proved, given `Δ_k → 0`): `tendsto_of_bonferroni`.

## Main results

* `twoProb_le_maxAlignScore_le`: **unconditional Karlin–Altschul bound**
  `P(M_{m,n} ≥ t) ≤ m n e^{-θ t}` at a Cramér root `θ` of the pair score, for every `t > 0`;
  a union bound over diagonals, so no independence is needed.
* `existsUnique_karlinAltschul_root`: the Karlin–Altschul `λ` exists and is unique (common letter
  law, negative mean, a positive score), from `Cslib.Bioinformatics.Motifs.PWM`.
* `twoProb_maxAlignScore_le_second_order`: the explicit finite-size bounds with the pairwise
  dependence coefficient `Δ_2`.
* `tendsto_twoProb_maxAlignScore_le`: **Gumbel limit, conditional on a one-sequence tail and
  asymptotic independence**: `P(M_{m,n} ≤ log (m n) / θ + x) → exp (-K e^{-θ x})` as `m, n → ∞`
  with `log n / m → 0` and `log m / n → 0`, given the one-sequence tail
  `OneSequenceTail (pairLaw p q) (pairScore s) θ K` and `Δ_k → 0` for every `k`. No lattice
  hypothesis is imposed; the intended regime is the classical nonlattice one with `K > 0`.

## What is assumed

Two inputs are hypotheses of `tendsto_twoProb_maxAlignScore_le`, not derived here:

* `OneSequenceTail`: `P(M_L > t) = (K + o(1)) L e^{-θ t}` uniformly as `L → ∞`,
  `L e^{-θ t} → 0`, over thresholds `t ≤ η L`, for the pair-score walk. This is the one-sequence
  (Iglehart; Karlin–Dembo) tail in the uniform form the two-sequence problem needs; `GumbelTail`
  (T50) proves the fixed-`x` Gumbel limit of one sequence from a ladder input, which does not
  give this uniformity. The cap `t ≤ η L` is needed: bounded scores make `P(M_L > t) = 0` for
  `t` beyond `L` times the largest score. The definition has no nonlattice hypothesis: it is
  meant for the nondegenerate classical regime `K > 0` of nonlattice scores, but it also holds in
  degenerate cases, e.g. for the lattice-valued zero score with `K = 0` (test file).
* `Δ_k → 0` for every `k`: asymptotic independence of the exceedances of distinct diagonals.
  Given the marginal limit this is equivalent to `S_k → (K e^{-θ x})^k / k!`, i.e. Poisson
  convergence in factorial-moment form, so in the limit the dependence is assumed, not derived.
  Dembo, Karlin and Zeitouni (1994) obtain it through a Poisson approximation under a
  relative-entropy condition on the letter laws; that analysis is not formalized.

Non-vacuity: the test file checks that a zero score matrix with `K = 0` satisfies every
hypothesis. No instance with `K ≠ 0` is constructed; that needs the renewal theory behind
`OneSequenceTail`.

## Scope

Not covered: the classical lattice theory (integer scoring matrices with a nondegenerate tail),
where `P(M_{m,n} ≤ log (m n)/θ + x)` in general has no limit and only liminf/limsup bounds hold
(compare `LatticeRenewalInput` in `GumbelTail`); `tendsto_twoProb_maxAlignScore_le` imposes no
lattice condition and applies whenever its hypotheses hold, as for the degenerate zero score.
Also not covered: the regime `E s(A, B) ≥ 0` with `s(A, B)` not almost surely `0`, where
`E e^{θ s(A, B)} > 1` for every `θ > 0` (convexity), so there is no Cramér root `θ > 0`, and for
`E s(A, B) > 0` the maximum grows linearly; gapped alignment; edge-effect corrections to `m n`.

## Implementation notes

The probability space is the finite product: `twoExpect p q m n F` sums `F u v` against
`bgLik p u · bgLik q v` over all words (`wordExpect`), so independence of disjoint blocks is
Fubini (`wordExpect_take_drop`). Scores along a diagonal are `List.zipWith s (u.drop i) (v.drop j)`.
The one-sequence layer of `SingleSequence` (T49) is reused through `scoreExpect_eq_wordExpect`,
`twoProb_diag` and `scoreProb_le_maxSegScore_le`. `elemSymm` is the elementary symmetric sum
over a `Finset`, written out as a sum over `powersetCard`.

Reuse search (base `4c8f3eb367`): `CSLibExt`, `MathlibExt` (the `ScoreSignificance` files
`SingleSequence`, `GumbelTail`, `LadderDerivation`, `RenewalDerivation`, `Calibration`, and
`Motifs.PWM`), the `cslib` package and Mathlib were searched for two-sequence alignment maxima,
Bonferroni inequalities, Poisson approximation by factorial moments, and elementary symmetric
sums of reals. Reused: `maxSegScore`, `scoreExpect`, `scoreProb`, `scoreMGF`,
`scoreProb_le_maxSegScore_le`, `bgLik`, `pairMGF`, `existsUnique_pairMGF_eq_one`,
`powersetCard_succ_insert`, `NormedSpace.expSeries_div_hasSum_exp`. Mathlib's
`Combinatorics.Enumerative.InclusionExclusion` gives the full alternating sum, not the
partial-sum (Bonferroni) inequalities; `Multiset.esymm` has no asymptotic lemmas; the
`MathlibExt` inclusion–exclusion lemmas (`BK`, `RookDominationPolynomial`) are exact identities
for other objects. No two-sequence alignment development was found.

## References

* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular
  sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
* A. Dembo, S. Karlin and O. Zeitouni, *Critical phenomena for sequence matching with scoring*,
  Ann. Probab. 22 (1994), 1993–2021.
* A. Dembo, S. Karlin and O. Zeitouni, *Limit distribution of maximal non-aligned two-sequence
  segmental score*, Ann. Probab. 22 (1994), 2022–2039.
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
* D. L. Iglehart, *Extreme values in the GI/G/1 queue*, Ann. Math. Statist. 43 (1972), 627–635.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley
  (1968), Chapter IV (combination of events, Bonferroni inequalities).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

open Real Finset Filter Topology
open Cslib.Bioinformatics.Motifs.PWM Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

/-! ## Pathwise layer: diagonals and ungapped alignments -/

section Pathwise

variable {β : Type*} (s : β → β → ℝ)

/-- The scores `s(u_i, v_j), s(u_{i+1}, v_{j+1}), …` along the diagonal of the alignment grid that
starts at position `i` of `u` and position `j` of `v`, up to the end of the shorter sequence. -/
def diagFrom (u v : List β) (i j : ℕ) : List ℝ := List.zipWith s (u.drop i) (v.drop j)

/-- The scores along the diagonal with **offset** `d` (the cells `(i, j)` with `j - i = d`). It
starts at `((-d)⁺, d⁺)`. -/
def diag (u v : List β) (d : ℤ) : List ℝ := diagFrom s u v (-d).toNat d.toNat

/-- The offsets `-(m - 1), …, n - 1` of the `m + n - 1` nonempty diagonals of an `m × n` grid
(`m, n ≥ 1`). -/
def offsets (m n : ℕ) : Finset ℤ := Ioo (-(m : ℤ)) n

/-- The length `min (m - (-d)⁺) (n - d⁺)` of the diagonal with offset `d` in an `m × n` grid. -/
def diagLen (m n : ℕ) (d : ℤ) : ℕ := min (m - (-d).toNat) (n - d.toNat)

/-- The score of the **ungapped alignment** of `u` from position `i` with `v` from position `j`,
with **length bound** `ℓ`: `∑_{k < ℓ'} s(u_{i+k}, v_{j+k})` over the
`ℓ' = min ℓ (min (|u| - i) (|v| - j))` pairs that exist. Windows running past the end of a
sequence are truncated (`take`, `zipWith`), so `ℓ` bounds the alignment length rather than
fixing it (`alignScore_eq_min`); for `i + ℓ ≤ |u|` and `j + ℓ ≤ |v|` it is the score of the two
windows of length `ℓ`. -/
def alignScore (u v : List β) (i j ℓ : ℕ) : ℝ :=
  (List.zipWith s ((u.drop i).take ℓ) ((v.drop j).take ℓ)).sum

/-- The **maximal ungapped alignment score** of `u` and `v`: the largest `alignScore` over all
start positions `i ≤ |u|`, `j ≤ |v|` and length bounds `ℓ ≤ |u|` (the empty alignment scores
`0`). Every alignment of a window of `u` with a window of `v` of the same length occurs, and every
triple scores such an alignment (`alignScore_eq_min`), so this is the best ungapped alignment
score. -/
noncomputable def maxAlignScore (u v : List β) : ℝ :=
  (range (u.length + 1) ×ˢ range (v.length + 1) ×ˢ range (u.length + 1)).sup'
    ⟨(0, 0, 0), by simp⟩ fun c => alignScore s u v c.1 c.2.1 c.2.2

theorem alignScore_eq (u v : List β) (i j ℓ : ℕ) :
    alignScore s u v i j ℓ = ((diagFrom s u v i j).take ℓ).sum := by
  rw [alignScore, diagFrom, List.take_zipWith]

theorem length_diagFrom (u v : List β) (i j : ℕ) :
    (diagFrom s u v i j).length = min (u.length - i) (v.length - j) := by
  simp [diagFrom]

theorem length_diag (u v : List β) (d : ℤ) :
    (diag s u v d).length = diagLen u.length v.length d :=
  length_diagFrom s u v _ _

/-- **Truncation.** `alignScore` only scores the `min ℓ (min (|u| - i) (|v| - j))` pairs that
exist: with length bound `ℓ` it is the score of the alignment of that length. -/
theorem alignScore_eq_min (u v : List β) (i j ℓ : ℕ) :
    alignScore s u v i j ℓ = alignScore s u v i j (min ℓ (min (u.length - i) (v.length - j))) := by
  rw [alignScore_eq, alignScore_eq, ← length_diagFrom s u v i j]
  rcases le_total ℓ (diagFrom s u v i j).length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le h, List.take_of_length_le le_rfl]

/-- Every ungapped alignment scores at most the maximum. -/
theorem alignScore_le_maxAlignScore (u v : List β) {i j ℓ : ℕ} (hi : i ≤ u.length)
    (hj : j ≤ v.length) (hℓ : ℓ ≤ u.length) : alignScore s u v i j ℓ ≤ maxAlignScore s u v :=
  le_sup' (fun c : ℕ × ℕ × ℕ => alignScore s u v c.1 c.2.1 c.2.2) (b := (i, j, ℓ))
    (by simp only [mem_product, mem_range]; omega)

theorem maxAlignScore_nonneg (u v : List β) : 0 ≤ maxAlignScore s u v := by
  simpa [alignScore] using
    alignScore_le_maxAlignScore s u v (i := 0) (j := 0) (ℓ := 0) (Nat.zero_le _) (Nat.zero_le _)
      (Nat.zero_le _)

/-- Dropping `k` scores from the diagonal starting at `(i, j)` gives the diagonal starting at
`(i + k, j + k)`. -/
theorem drop_diagFrom (u v : List β) (i j k : ℕ) :
    (diagFrom s u v i j).drop k = diagFrom s u v (i + k) (j + k) := by
  simp [diagFrom, List.drop_zipWith, List.drop_drop]

/-- The diagonal through `(i, j)`, started at its first cell, contains the diagonal starting at
`(i, j)` as a suffix. -/
theorem diagFrom_eq_drop_diag (u v : List β) (i j : ℕ) :
    diagFrom s u v i j = (diag s u v ((j : ℤ) - i)).drop (min i j) := by
  rw [diag, drop_diagFrom]
  congr 1 <;> omega

/-- **Every diagonal's maximal segment score is an ungapped alignment score**, so it is at most
the maximal alignment score. -/
theorem maxSegScore_diag_le (u v : List β) (d : ℤ) :
    maxSegScore (diag s u v d) ≤ maxAlignScore s u v := by
  obtain ⟨w, hw, hsum⟩ := exists_infix_sum_eq_maxSegScore (diag s u v d)
  obtain ⟨a, b, hab⟩ := hw
  have hlen := congrArg List.length hab
  simp only [List.length_append, length_diag, diagLen] at hlen
  have hw' : w = ((diag s u v d).drop a.length).take w.length := by
    rw [← hab, List.append_assoc, List.drop_left, List.take_left]
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · rw [← hsum, List.length_eq_zero_iff.1 h0, List.sum_nil]; exact maxAlignScore_nonneg s u v
  rw [← hsum, hw', diag, drop_diagFrom, ← alignScore_eq]
  exact alignScore_le_maxAlignScore s u v (by omega) (by omega) (by omega)

/-- **The maximal ungapped alignment score is attained on a diagonal**: it is the maximal segment
score of the score sequence along some diagonal. -/
theorem exists_maxSegScore_diag_eq (u v : List β) :
    ∃ d : ℤ, maxSegScore (diag s u v d) = maxAlignScore s u v := by
  obtain ⟨⟨i, j, ℓ⟩, -, h⟩ := exists_mem_eq_sup'
    (⟨(0, 0, 0), by simp⟩ : (range (u.length + 1) ×ˢ range (v.length + 1) ×ˢ
      range (u.length + 1)).Nonempty) fun c => alignScore s u v c.1 c.2.1 c.2.2
  refine ⟨(j : ℤ) - i, le_antisymm (maxSegScore_diag_le s u v _) ?_⟩
  rw [maxAlignScore, h, alignScore_eq, diagFrom_eq_drop_diag]
  exact sum_le_maxSegScore_of_infix ((List.take_prefix _ _).isInfix.trans
    (List.drop_suffix _ _).isInfix)

/-- Diagonals with offset outside `offsets |u| |v|` are empty. -/
theorem diag_eq_nil (u v : List β) {d : ℤ} (hd : d ∉ offsets u.length v.length) :
    diag s u v d = [] := by
  simp only [offsets, mem_Ioo, not_and_or, not_lt] at hd
  rcases hd with hd | hd
  · simp [diag, diagFrom, List.drop_eq_nil_of_le (show u.length ≤ (-d).toNat by omega)]
  · simp [diag, diagFrom, List.drop_eq_nil_of_le (show v.length ≤ d.toNat by omega)]

/-- **Diagonal decomposition**: for `t ≥ 0`, the maximal ungapped alignment score is at most `t`
iff no diagonal contains a segment scoring more than `t`. -/
theorem maxAlignScore_le_iff (u v : List β) {t : ℝ} (ht : 0 ≤ t) :
    maxAlignScore s u v ≤ t ↔
      ∀ d ∈ offsets u.length v.length, ¬ t < maxSegScore (diag s u v d) := by
  refine ⟨fun h d _ => not_lt.2 ((maxSegScore_diag_le s u v d).trans h), fun h => ?_⟩
  obtain ⟨d, hd⟩ := exists_maxSegScore_diag_eq s u v
  rw [← hd]
  by_cases hmem : d ∈ offsets u.length v.length
  · exact not_lt.1 (h d hmem)
  · rw [diag_eq_nil s u v hmem, maxSegScore_nil]; exact ht

/-- For `t > 0` some diagonal reaches `t` iff the maximal alignment score does. -/
theorem le_maxAlignScore_iff (u v : List β) {t : ℝ} (ht : 0 < t) :
    t ≤ maxAlignScore s u v ↔ ∃ d ∈ offsets u.length v.length, t ≤ maxSegScore (diag s u v d) := by
  refine ⟨fun h => ?_, fun ⟨d, _, hd⟩ => hd.trans (maxSegScore_diag_le s u v d)⟩
  obtain ⟨d, hd⟩ := exists_maxSegScore_diag_eq s u v
  by_cases hmem : d ∈ offsets u.length v.length
  · exact ⟨d, hmem, hd ▸ h⟩
  · rw [diag_eq_nil s u v hmem, maxSegScore_nil] at hd; linarith

/-- **Cell count**: the diagonal lengths of an `m × n` grid add up to `m n`. -/
theorem sum_diagLen (m n : ℕ) : ∑ d ∈ offsets m n, (diagLen m n d : ℝ) = m * n := by
  have hcard : (range m ×ˢ range n).card =
      ∑ d ∈ offsets m n, ((range m ×ˢ range n).filter fun c => (c.2 : ℤ) - c.1 = d).card :=
    card_eq_sum_card_fiberwise fun c hc => by
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hc
      simp only [offsets, coe_Ioo, Set.mem_Ioo]; omega
  have hfib : ∀ d ∈ offsets m n,
      ((range m ×ˢ range n).filter fun c => (c.2 : ℤ) - c.1 = d).card = diagLen m n d := by
    intro d hd
    simp only [offsets, mem_Ioo] at hd
    rw [← card_range (diagLen m n d)]
    refine card_nbij' (fun c => c.1 - (-d).toNat) (fun k => ((-d).toNat + k, d.toNat + k))
      ?_ ?_ ?_ ?_
    · intro c hc
      simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hc
      simp only [coe_range, Set.mem_Iio, diagLen]; omega
    · intro k hk
      simp only [coe_range, Set.mem_Iio, diagLen] at hk
      simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq]; omega
    · intro c hc
      simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hc
      ext <;> dsimp only <;> omega
    · intro k _; simp
  rw [card_product, card_range, card_range] at hcard
  rw [← Nat.cast_mul, hcard, Nat.cast_sum]
  exact sum_congr rfl fun d hd => by rw [hfib d hd]

end Pathwise

/-! ## The two-sequence model -/

section Model

variable {β : Type*} [Fintype β]

/-- Expectation of a functional `G` of an iid word of length `n` with letter law `p`. -/
noncomputable def wordExpect (p : β → ℝ) (n : ℕ) (G : List β → ℝ) : ℝ :=
  ∑ w : Fin n → β, bgLik p w * G (List.ofFn w)

/-- **The two-sequence model.** `u` (length `m`, letter law `p`) and `v` (length `n`, letter law
`q`) are independent iid words over the finite alphabet `β`; `twoExpect p q m n F` is the
expectation of `F u v`. -/
noncomputable def twoExpect (p q : β → ℝ) (m n : ℕ) (F : List β → List β → ℝ) : ℝ :=
  wordExpect p m fun u => wordExpect q n fun v => F u v

open Classical in
/-- The probability that the pair of words satisfies `P`. -/
noncomputable def twoProb (p q : β → ℝ) (m n : ℕ) (P : List β → List β → Prop) : ℝ :=
  twoExpect p q m n fun u v => if P u v then 1 else 0

/-- The law `(a, b) ↦ p a q b` of an aligned letter pair: one letter from each sequence. -/
def pairLaw (p q : β → ℝ) : β × β → ℝ := fun x => p x.1 * q x.2

/-- The score `s a b` of an aligned letter pair. -/
def pairScore (s : β → β → ℝ) : β × β → ℝ := fun x => s x.1 x.2

theorem isDist_pairLaw {p q : β → ℝ} (hp : IsDist p) (hq : IsDist q) : IsDist (pairLaw p q) :=
  ⟨fun x => mul_nonneg (hp.1 _) (hq.1 _), by
    simp only [pairLaw]; rw [Fintype.sum_prod_type]; simp [← mul_sum, hp.2, hq.2]⟩

/-- With a common letter law `p`, the pair-score MGF is the Karlin–Altschul MGF
`∑ pₐ p_b e^{θ s(a, b)}` of `Cslib.Bioinformatics.Motifs.PWM.pairMGF`. -/
theorem scoreMGF_pairLaw (p : β → ℝ) (s : β → β → ℝ) (θ : ℝ) :
    scoreMGF (pairLaw p p) (pairScore s) θ = pairMGF p s θ := by
  rw [scoreMGF, pairMGF, Fintype.sum_prod_type]; rfl

/-- **The Karlin–Altschul parameter `λ`** (Karlin and Altschul 1990): for a common letter law with
all letters of positive probability, negative expected score and some positive score, there is a
unique `λ > 0` with `E e^{λ s(A, B)} = 1` for independent letters `A, B`. -/
theorem existsUnique_karlinAltschul_root {p : β → ℝ} {s : β → β → ℝ} (hp : IsDist p)
    (hp0 : ∀ a, 0 < p a) (hneg : ∑ a, ∑ b, p a * p b * s a b < 0) (hpos : ∃ a b, 0 < s a b) :
    ∃! θ, 0 < θ ∧ scoreMGF (pairLaw p p) (pairScore s) θ = 1 := by
  simpa only [scoreMGF_pairLaw] using existsUnique_pairMGF_eq_one hp hp0 hneg hpos

section Word

variable (p : β → ℝ)

theorem wordExpect_zero (G : List β → ℝ) : wordExpect p 0 G = G [] := by
  simp [wordExpect, bgLik]

theorem wordExpect_succ (n : ℕ) (G : List β → ℝ) :
    wordExpect p (n + 1) G = ∑ a, p a * wordExpect p n fun l => G (a :: l) := by
  unfold wordExpect
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => β).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  simp [Fin.consEquiv, bgLik, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

theorem wordExpect_congr {n : ℕ} {G H : List β → ℝ} (h : ∀ l, l.length = n → G l = H l) :
    wordExpect p n G = wordExpect p n H :=
  sum_congr rfl fun _ _ => by rw [h _ List.length_ofFn]

theorem wordExpect_add (n : ℕ) (G H : List β → ℝ) :
    wordExpect p n (fun l => G l + H l) = wordExpect p n G + wordExpect p n H := by
  simp only [wordExpect, mul_add, sum_add_distrib]

theorem wordExpect_const_mul (n : ℕ) (c : ℝ) (G : List β → ℝ) :
    wordExpect p n (fun l => c * G l) = c * wordExpect p n G := by
  simp only [wordExpect, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem wordExpect_mul_const (n : ℕ) (c : ℝ) (G : List β → ℝ) :
    wordExpect p n (fun l => G l * c) = wordExpect p n G * c := by
  simp only [wordExpect, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

theorem wordExpect_sum {ι : Type*} (t : Finset ι) (n : ℕ) (G : ι → List β → ℝ) :
    wordExpect p n (fun l => ∑ i ∈ t, G i l) = ∑ i ∈ t, wordExpect p n (G i) := by
  simp only [wordExpect, mul_sum]
  exact sum_comm

theorem wordExpect_comm {γ : Type*} [Fintype γ] (q : γ → ℝ) (m n : ℕ)
    (H : List β → List γ → ℝ) :
    (wordExpect p m fun u => wordExpect q n fun v => H u v) =
      wordExpect q n fun v => wordExpect p m fun u => H u v := by
  simp only [wordExpect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

variable {p} in
theorem wordExpect_mono (hp : ∀ b, 0 ≤ p b) {n : ℕ} {G H : List β → ℝ}
    (h : ∀ l, l.length = n → G l ≤ H l) : wordExpect p n G ≤ wordExpect p n H :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _ List.length_ofFn)
    (prod_nonneg fun _ _ => hp _)

variable {p} in
theorem wordExpect_const (hp : IsDist p) (n : ℕ) (c : ℝ) : wordExpect p n (fun _ => c) = c := by
  induction n with
  | zero => exact wordExpect_zero p _
  | succ n ih => rw [wordExpect_succ]; simp only [ih, ← sum_mul, hp.2, one_mul]

/-- A word of length `k + n` is a word of length `k` followed by an independent word of
length `n`. -/
theorem wordExpect_append (k n : ℕ) (G : List β → ℝ) :
    wordExpect p (k + n) G = wordExpect p k fun u => wordExpect p n fun v => G (u ++ v) := by
  induction k generalizing G with
  | zero => rw [Nat.zero_add, wordExpect_zero]; rfl
  | succ k ih =>
      rw [Nat.add_right_comm, wordExpect_succ, wordExpect_succ]
      exact sum_congr rfl fun a _ => by rw [ih]; rfl

/-- Splitting a word at position `k ≤ n` into two independent pieces. -/
theorem wordExpect_take_drop {k n : ℕ} (hk : k ≤ n) (Φ : List β → List β → ℝ) :
    wordExpect p n (fun l => Φ (l.take k) (l.drop k)) =
      wordExpect p k fun u => wordExpect p (n - k) fun v => Φ u v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [wordExpect_append, Nat.add_sub_cancel_left]
  refine wordExpect_congr p fun u hu => wordExpect_congr p fun v _ => ?_
  rw [List.take_left' hu, List.drop_left' hu]

variable {p} in
/-- Dropping the first `k` letters of an iid word of length `n` leaves an iid word of length
`n - k`. -/
theorem wordExpect_drop (hp : IsDist p) (k n : ℕ) (G : List β → ℝ) :
    wordExpect p n (fun l => G (l.drop k)) = wordExpect p (n - k) G := by
  rcases le_total k n with hk | hk
  · rw [wordExpect_take_drop p hk (fun _ v => G v), wordExpect_const hp]
  · rw [Nat.sub_eq_zero_of_le hk, wordExpect_zero,
      wordExpect_congr p (H := fun _ => G []) fun l hl => by
        rw [List.drop_eq_nil_of_le (hl ▸ hk)],
      wordExpect_const hp]

/-- The score expectation of `SingleSequence` is a word expectation. -/
theorem scoreExpect_eq_wordExpect (f : β → ℝ) (n : ℕ) (F : List ℝ → ℝ) :
    scoreExpect p f n F = wordExpect p n fun w => F (w.map f) := by
  simp [scoreExpect, wordExpect, List.map_ofFn]; rfl

end Word

section Two

variable {p q : β → ℝ}

theorem twoExpect_mono (hp : ∀ b, 0 ≤ p b) (hq : ∀ b, 0 ≤ q b) {m n : ℕ}
    {F G : List β → List β → ℝ} (h : ∀ u v, u.length = m → v.length = n → F u v ≤ G u v) :
    twoExpect p q m n F ≤ twoExpect p q m n G :=
  wordExpect_mono hp fun u hu => wordExpect_mono hq fun v hv => h u v hu hv

theorem twoExpect_sum {ι : Type*} (t : Finset ι) (m n : ℕ) (F : ι → List β → List β → ℝ) :
    twoExpect p q m n (fun u v => ∑ i ∈ t, F i u v) = ∑ i ∈ t, twoExpect p q m n (F i) := by
  simp only [twoExpect, wordExpect_sum]

theorem twoExpect_add (m n : ℕ) (F G : List β → List β → ℝ) :
    twoExpect p q m n (fun u v => F u v + G u v) = twoExpect p q m n F + twoExpect p q m n G := by
  simp only [twoExpect, wordExpect_add]

theorem twoExpect_const_mul (m n : ℕ) (c : ℝ) (F : List β → List β → ℝ) :
    twoExpect p q m n (fun u v => c * F u v) = c * twoExpect p q m n F := by
  simp only [twoExpect, wordExpect_const_mul]

theorem twoExpect_const (hp : IsDist p) (hq : IsDist q) (m n : ℕ) (c : ℝ) :
    twoExpect p q m n (fun _ _ => c) = c := by
  simp only [twoExpect, wordExpect_const hq, wordExpect_const hp]

theorem twoProb_nonneg (hp : ∀ b, 0 ≤ p b) (hq : ∀ b, 0 ≤ q b) (m n : ℕ)
    (P : List β → List β → Prop) : 0 ≤ twoProb p q m n P := by
  classical
  have := twoExpect_mono (m := m) (n := n) (F := fun _ _ => 0)
    (G := fun u v => if P u v then (1 : ℝ) else 0) hp hq fun u v _ _ => by split_ifs <;> norm_num
  simpa [twoProb, twoExpect, wordExpect] using this

theorem twoProb_mono (hp : ∀ b, 0 ≤ p b) (hq : ∀ b, 0 ≤ q b) {m n : ℕ}
    {P Q : List β → List β → Prop} (h : ∀ u v, u.length = m → v.length = n → P u v → Q u v) :
    twoProb p q m n P ≤ twoProb p q m n Q := by
  classical
  exact twoExpect_mono hp hq fun u v hu hv => by
    by_cases hP : P u v
    · simp [hP, h u v hu hv hP]
    · simp only [hP, ite_false]; split_ifs <;> norm_num

theorem twoProb_congr {m n : ℕ} {P Q : List β → List β → Prop}
    (h : ∀ u v, u.length = m → v.length = n → (P u v ↔ Q u v)) :
    twoProb p q m n P = twoProb p q m n Q := by
  classical
  exact wordExpect_congr p fun u hu => wordExpect_congr q fun v hv => if_congr (h u v hu hv) rfl rfl

/-- **Aligning two independent iid words letter by letter gives an iid pair-score sequence**:
the scores `s(u₀, v₀), s(u₁, v₁), …` of the first `min m n` aligned pairs are iid with the law
of `s(A, B)`, `A ~ p`, `B ~ q` independent. -/
theorem twoExpect_zipWith (hp : IsDist p) (hq : IsDist q) (s : β → β → ℝ) (m n : ℕ)
    (F : List ℝ → ℝ) :
    twoExpect p q m n (fun u v => F (List.zipWith s u v)) =
      scoreExpect (pairLaw p q) (pairScore s) (min m n) F := by
  induction m generalizing n F with
  | zero =>
      simp [twoExpect, wordExpect_zero, wordExpect_const hq, scoreExpect_zero]
  | succ m ih =>
      cases n with
      | zero =>
          simp [twoExpect, wordExpect_zero, wordExpect_const hp, scoreExpect_zero]
      | succ n =>
          rw [show min (m + 1) (n + 1) = min m n + 1 by omega, scoreExpect_succ,
            Fintype.sum_prod_type, twoExpect, wordExpect_succ]
          refine sum_congr rfl fun a _ => ?_
          have hin : ∀ u : List β, (wordExpect q (n + 1) fun v => F (List.zipWith s (a :: u) v)) =
              ∑ b, q b * wordExpect q n fun v => F (s a b :: List.zipWith s u v) := fun u => by
            rw [wordExpect_succ]; rfl
          simp only [hin, wordExpect_sum, wordExpect_const_mul, mul_sum]
          refine sum_congr rfl fun b _ => ?_
          rw [← mul_assoc]
          exact congrArg (p a * q b * ·) (ih n fun l => F (s a b :: l))

/-- **Single-diagonal slice**: the score sequence along the diagonal with offset `d` of the
`m × n` grid has the law of an iid score sequence of length `diagLen m n d` with the pair law, so
every one-sequence result of `SingleSequence` applies to each diagonal. -/
theorem twoExpect_diag (hp : IsDist p) (hq : IsDist q) (s : β → β → ℝ) (m n : ℕ) (d : ℤ)
    (F : List ℝ → ℝ) :
    twoExpect p q m n (fun u v => F (diag s u v d)) =
      scoreExpect (pairLaw p q) (pairScore s) (diagLen m n d) F := by
  have hin : ∀ u' : List β, (wordExpect q n fun v => F (List.zipWith s u' (v.drop d.toNat))) =
      wordExpect q (n - d.toNat) fun v' => F (List.zipWith s u' v') := fun u' =>
    wordExpect_drop hq _ _ (fun v' => F (List.zipWith s u' v'))
  simp only [twoExpect, diag, diagFrom, hin]
  rw [wordExpect_drop hp (-d).toNat m
    (fun u' => wordExpect q (n - d.toNat) fun v' => F (List.zipWith s u' v'))]
  exact twoExpect_zipWith hp hq s _ _ F

/-- The single-diagonal slice for probabilities. -/
theorem twoProb_diag (hp : IsDist p) (hq : IsDist q) (s : β → β → ℝ) (m n : ℕ) (d : ℤ)
    (P : List ℝ → Prop) :
    twoProb p q m n (fun u v => P (diag s u v d)) =
      scoreProb (pairLaw p q) (pairScore s) (diagLen m n d) P := by
  classical
  exact twoExpect_diag hp hq s m n d fun l => if P l then 1 else 0

theorem twoProb_exists_le (hp : ∀ b, 0 ≤ p b) (hq : ∀ b, 0 ≤ q b) {ι : Type*} (t : Finset ι)
    (m n : ℕ) (P : ι → List β → List β → Prop) :
    twoProb p q m n (fun u v => ∃ i ∈ t, P i u v) ≤ ∑ i ∈ t, twoProb p q m n (P i) := by
  classical
  simp only [twoProb, ← twoExpect_sum]
  refine twoExpect_mono hp hq fun u v _ _ => ?_
  split_ifs with h
  · obtain ⟨i, hi, hP⟩ := h
    refine le_trans ?_ (single_le_sum (fun j _ => ?_) hi)
    · simp [hP]
    · split_ifs <;> norm_num
  · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

end Two

/-! ## Unconditional Karlin–Altschul bound -/

section Bound

variable {p q : β → ℝ}

/-- **Karlin–Altschul upper bound for two sequences** (the `m n e^{-λ t}` E-value bound): at a
Cramér root `θ ≥ 0` of the pair score, `P(M_{m,n} ≥ t) ≤ m n e^{-θ t}` for every `t > 0`. No
independence between diagonals is used: it is a union bound over the `m + n - 1` diagonals, each
bounded by the one-sequence estimate `SingleSequence.scoreProb_le_maxSegScore_le` through the
single-diagonal slice, and the diagonal lengths add up to `m n` (`sum_diagLen`). -/
theorem twoProb_le_maxAlignScore_le (hp : IsDist p) (hq : IsDist q) (s : β → β → ℝ) {θ : ℝ}
    (hθ : 0 ≤ θ) (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1) (m n : ℕ) {t : ℝ}
    (ht : 0 < t) :
    twoProb p q m n (fun u v => t ≤ maxAlignScore s u v) ≤ m * n * exp (-θ * t) := by
  calc twoProb p q m n (fun u v => t ≤ maxAlignScore s u v)
      ≤ twoProb p q m n (fun u v => ∃ d ∈ offsets m n, t ≤ maxSegScore (diag s u v d)) :=
        twoProb_mono hp.1 hq.1 fun u v hu hv h => by
          rw [← hu, ← hv]; exact (le_maxAlignScore_iff s u v ht).1 h
    _ ≤ ∑ d ∈ offsets m n, twoProb p q m n (fun u v => t ≤ maxSegScore (diag s u v d)) :=
        twoProb_exists_le hp.1 hq.1 _ _ _ _
    _ = ∑ d ∈ offsets m n,
          scoreProb (pairLaw p q) (pairScore s) (diagLen m n d) (fun l => t ≤ maxSegScore l) :=
        sum_congr rfl fun d _ => twoProb_diag hp hq s m n d (fun l => t ≤ maxSegScore l)
    _ ≤ ∑ d ∈ offsets m n, (diagLen m n d : ℝ) * exp (-θ * t) :=
        sum_le_sum fun d _ =>
          scoreProb_le_maxSegScore_le _ (isDist_pairLaw hp hq) hθ hroot _ ht
    _ = m * n * exp (-θ * t) := by rw [← sum_mul, sum_diagLen]

end Bound

/-! ## Letter-disjoint diagonals are independent -/

section Disjoint

variable {p q : β → ℝ}

private theorem zipWith_take_right {γ δ : Type*} (f : γ → δ → ℝ) :
    ∀ (l : List γ) (l' : List δ) (k : ℕ), min l.length l'.length ≤ k →
      List.zipWith f l l' = List.zipWith f l (l'.take k)
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | _ :: _, _ :: _, 0, h => by simp at h
  | a :: l, b :: l', k + 1, h => by
      simp only [List.zipWith_cons_cons, List.take_succ_cons, List.cons.injEq, true_and]
      exact zipWith_take_right f l l' k (by simp at h; omega)

private theorem zipWith_take_left {γ δ : Type*} (f : γ → δ → ℝ) :
    ∀ (l : List γ) (l' : List δ) (k : ℕ), min l.length l'.length ≤ k →
      List.zipWith f l l' = List.zipWith f (l.take k) l'
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | _ :: _, _ :: _, 0, h => by simp at h
  | a :: l, b :: l', k + 1, h => by
      simp only [List.zipWith_cons_cons, List.take_succ_cons, List.cons.injEq, true_and]
      exact zipWith_take_left f l l' k (by simp at h; omega)

/-- **Letter-disjoint diagonals are independent.** The diagonal with offset `-i` (starting at
`(i, 0)`) and the diagonal with offset `j` (starting at `(0, j)`) read disjoint sets of letters
when the first ends before column `j` and the second ends before row `i`; their score sequences
are then independent. Diagonals that share a letter are in general dependent (see the test
file). -/
theorem twoProb_diag_and_diag_of_disjoint (hp : IsDist p) (hq : IsDist q) (s : β → β → ℝ)
    {m n i j : ℕ} (hi : i ≤ m) (hj : j ≤ n) (hij : diagLen m n (-i) ≤ j)
    (hji : diagLen m n j ≤ i) (A B : List ℝ → Prop) :
    twoProb p q m n (fun u v => A (diag s u v (-i)) ∧ B (diag s u v j)) =
      twoProb p q m n (fun u v => A (diag s u v (-i))) *
        twoProb p q m n (fun u v => B (diag s u v j)) := by
  classical
  simp only [diagLen, neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast] at hij hji
  set gA : List ℝ → ℝ := fun l => if A l then 1 else 0
  set gB : List ℝ → ℝ := fun l => if B l then 1 else 0
  have hA : ∀ u v : List β, u.length = m → v.length = n →
      diag s u v (-i) = List.zipWith s (u.drop i) (v.take j) := fun u v hu hv => by
    simp only [diag, diagFrom, neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, List.drop_zero]
    exact zipWith_take_right s _ _ _ (by simp [hu, hv]; omega)
  have hB : ∀ u v : List β, u.length = m → v.length = n →
      diag s u v j = List.zipWith s (u.take i) (v.drop j) := fun u v hu hv => by
    simp only [diag, diagFrom, Int.toNat_natCast, Int.toNat_neg_natCast, List.drop_zero]
    exact zipWith_take_left s _ _ _ (by simp [hu, hv]; omega)
  -- the two marginals, as two-sequence expectations over the blocks they read
  have eA : twoProb p q m n (fun u v => A (diag s u v (-i))) =
      twoExpect p q (m - i) j fun u v => gA (List.zipWith s u v) := by
    rw [twoProb_diag hp hq, twoExpect_zipWith hp hq]
    simp only [diagLen, neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast]
    rw [show min (m - i) (n - 0) = min (m - i) j by omega]; rfl
  have eB : twoProb p q m n (fun u v => B (diag s u v j)) =
      twoExpect p q i (n - j) fun u v => gB (List.zipWith s u v) := by
    rw [twoProb_diag hp hq, twoExpect_zipWith hp hq]
    simp only [diagLen, Int.toNat_natCast, Int.toNat_neg_natCast]
    rw [show min (m - 0) (n - j) = min i (n - j) by omega]; rfl
  have eAB : twoProb p q m n (fun u v => A (diag s u v (-i)) ∧ B (diag s u v j)) =
      wordExpect p m fun u => wordExpect q n fun v =>
        gA (List.zipWith s (u.drop i) (v.take j)) * gB (List.zipWith s (u.take i) (v.drop j)) := by
    unfold twoProb twoExpect
    exact wordExpect_congr p fun u hu => wordExpect_congr q fun v hv => by
      beta_reduce
      rw [hA u v hu hv, hB u v hu hv]
      simp only [gA, gB]; split_ifs <;> simp_all
  have hsplit : ∀ u₁ u₂ : List β, (wordExpect q n fun v =>
      gA (List.zipWith s u₂ (v.take j)) * gB (List.zipWith s u₁ (v.drop j))) =
        (wordExpect q j fun v₁ => gA (List.zipWith s u₂ v₁)) *
          wordExpect q (n - j) fun v₂ => gB (List.zipWith s u₁ v₂) := fun u₁ u₂ => by
    rw [wordExpect_take_drop q hj (fun v₁ v₂ => gA (List.zipWith s u₂ v₁) *
      gB (List.zipWith s u₁ v₂))]
    simp only [wordExpect_const_mul, wordExpect_mul_const]
  rw [eAB, eA, eB, wordExpect_take_drop p hi (fun u₁ u₂ => wordExpect q n fun v =>
    gA (List.zipWith s u₂ (v.take j)) * gB (List.zipWith s u₁ (v.drop j)))]
  simp only [hsplit, wordExpect_const_mul, wordExpect_mul_const, twoExpect]

end Disjoint

end Model

/-! ## Poisson limit by the Bonferroni sieve -/

section Sieve

/-- The elementary symmetric sum `e_k(f) = ∑_{T ⊆ D, |T| = k} ∏_{i ∈ T} f i`: the `k`-th factorial
moment `E[C(W, k)]` of the number `W` of occurring events when the events `i ∈ D` are independent
with probabilities `f i`. -/
noncomputable def elemSymm {ι : Type*} (D : Finset ι) (f : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ D.powersetCard k, ∏ i ∈ T, f i

variable {ι : Type*}

theorem elemSymm_zero (D : Finset ι) (f : ι → ℝ) : elemSymm D f 0 = 1 := by
  simp [elemSymm]

theorem elemSymm_one (D : Finset ι) (f : ι → ℝ) : elemSymm D f 1 = ∑ i ∈ D, f i := by
  simp [elemSymm, powersetCard_one]

theorem elemSymm_nonneg {D : Finset ι} {f : ι → ℝ} (hf : ∀ i ∈ D, 0 ≤ f i) (k : ℕ) :
    0 ≤ elemSymm D f k :=
  sum_nonneg fun _ hT => prod_nonneg fun i hi => hf i ((mem_powersetCard.1 hT).1 hi)

theorem elemSymm_mono {D D' : Finset ι} {f : ι → ℝ} (hf : ∀ i ∈ D, 0 ≤ f i) (h : D' ⊆ D)
    (k : ℕ) : elemSymm D' f k ≤ elemSymm D f k :=
  sum_le_sum_of_subset_of_nonneg (powersetCard_mono h) fun _ hT _ =>
    prod_nonneg fun i hi => hf i ((mem_powersetCard.1 hT).1 hi)

/-- Splitting off one index: `e_{k+1}(D) = e_{k+1}(D ∖ i) + f i · e_k(D ∖ i)`. -/
theorem elemSymm_succ_erase [DecidableEq ι] {D : Finset ι} {i : ι} (hi : i ∈ D) (f : ι → ℝ)
    (k : ℕ) :
    elemSymm D f (k + 1) = elemSymm (D.erase i) f (k + 1) + f i * elemSymm (D.erase i) f k := by
  conv_lhs => rw [← insert_erase hi]
  rw [elemSymm, powersetCard_succ_insert (notMem_erase i D), sum_union, sum_image]
  · rw [elemSymm, elemSymm, mul_sum]
    congr 1
    refine sum_congr rfl fun T hT => ?_
    rw [prod_insert fun h => notMem_erase i D ((mem_powersetCard.1 hT).1 h)]
  · intro T hT T' hT' h
    have h1 : i ∉ T := fun h => notMem_erase i D ((mem_powersetCard.1 hT).1 h)
    have h2 : i ∉ T' := fun h => notMem_erase i D ((mem_powersetCard.1 hT').1 h)
    rw [← erase_insert h1, ← erase_insert h2]; exact congrArg (·.erase i) h
  · rw [disjoint_left]
    intro T hT hT'
    obtain ⟨U, -, rfl⟩ := mem_image.1 hT'
    exact notMem_erase i D ((mem_powersetCard.1 hT).1 (mem_insert_self i U))

/-- Double counting: `(k + 1) e_{k+1}(D) = ∑_{i ∈ D} f i · e_k(D ∖ i)`. -/
theorem succ_mul_elemSymm_succ [DecidableEq ι] (D : Finset ι) (f : ι → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * elemSymm D f (k + 1) = ∑ i ∈ D, f i * elemSymm (D.erase i) f k := by
  have h1 : (k + 1 : ℝ) * elemSymm D f (k + 1) =
      ∑ T ∈ D.powersetCard (k + 1), ∑ i ∈ T, f i * ∏ j ∈ T.erase i, f j := by
    rw [elemSymm, mul_sum]
    refine sum_congr rfl fun T hT => ?_
    rw [sum_congr rfl fun i hi => mul_prod_erase T f hi, sum_const,
      (mem_powersetCard.1 hT).2, nsmul_eq_mul]
    push_cast; ring
  rw [h1, sum_comm' (t' := D) (s' := fun i => (D.powersetCard (k + 1)).filter (i ∈ ·))]
  · refine sum_congr rfl fun i hi => ?_
    rw [elemSymm, mul_sum]
    refine sum_nbij' (fun T => T.erase i) (fun U => insert i U) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      obtain ⟨hT, hiT⟩ := mem_filter.1 hT
      rw [mem_powersetCard] at hT ⊢
      exact ⟨erase_subset_erase i hT.1, by rw [card_erase_of_mem hiT, hT.2]; rfl⟩
    · intro U hU
      rw [mem_powersetCard] at hU
      have hiU : i ∉ U := fun h => notMem_erase i D (hU.1 h)
      refine mem_filter.2 ⟨mem_powersetCard.2 ⟨insert_subset hi
        (hU.1.trans (erase_subset i D)), by rw [card_insert_of_notMem hiU, hU.2]⟩,
        mem_insert_self i U⟩
    · intro T hT; exact insert_erase (mem_filter.1 hT).2
    · intro U hU
      exact erase_insert fun h => notMem_erase i D ((mem_powersetCard.1 hU).1 h)
    · intro T _; rfl
  · intro T i
    simp only [mem_filter]
    constructor
    · rintro ⟨hT, hiT⟩; exact ⟨⟨hT, hiT⟩, (mem_powersetCard.1 hT).1 hiT⟩
    · rintro ⟨⟨hT, hiT⟩, -⟩; exact ⟨hT, hiT⟩

/-- The Newton-type recursion error: `0 ≤ σ e_{k+1}(D) - (k + 2) e_{k+2}(D) ≤ μ σ e_k(D)` where
`σ = ∑ f` and `μ` bounds every `f i`. -/
theorem elemSymm_recursion_bounds {D : Finset ι} {f : ι → ℝ} {μ : ℝ}
    (hf : ∀ i ∈ D, 0 ≤ f i) (hμ : ∀ i ∈ D, f i ≤ μ) (k : ℕ) :
    0 ≤ (∑ i ∈ D, f i) * elemSymm D f (k + 1) - (k + 2 : ℝ) * elemSymm D f (k + 2) ∧
      (∑ i ∈ D, f i) * elemSymm D f (k + 1) - (k + 2 : ℝ) * elemSymm D f (k + 2) ≤
        μ * (∑ i ∈ D, f i) * elemSymm D f k := by
  classical
  have hrec := succ_mul_elemSymm_succ D f (k + 1)
  push_cast at hrec
  rw [show (k : ℝ) + 2 = k + 1 + 1 by ring, hrec, sum_mul, ← sum_sub_distrib]
  have hterm : ∀ i ∈ D, f i * elemSymm D f (k + 1) - f i * elemSymm (D.erase i) f (k + 1) =
      f i * (f i * elemSymm (D.erase i) f k) := fun i hi => by
    rw [elemSymm_succ_erase hi f k]; ring
  rw [sum_congr rfl hterm]
  refine ⟨sum_nonneg fun i hi => mul_nonneg (hf i hi) (mul_nonneg (hf i hi)
    (elemSymm_nonneg (fun j hj => hf j (mem_of_mem_erase hj)) k)), ?_⟩
  rw [mul_assoc, sum_mul, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have he : 0 ≤ elemSymm (D.erase i) f k :=
    elemSymm_nonneg (fun j hj => hf j (mem_of_mem_erase hj)) k
  have hmono := elemSymm_mono hf (erase_subset i D) k
  calc f i * (f i * elemSymm (D.erase i) f k) ≤ f i * (μ * elemSymm D f k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hμ i hi) hmono he ((hf i hi).trans (hμ i hi)))
          (hf i hi)
    _ = μ * (f i * elemSymm D f k) := by ring

/-- **Elementary symmetric sums of many small probabilities.** If the probabilities are
nonnegative, uniformly small (`max f → 0`) and their sum tends to `c`, then
`e_k(f) → c^k / k!` for every `k`. -/
theorem tendsto_elemSymm {D : ℕ → Finset ι} {f : ℕ → ι → ℝ} {μ : ℕ → ℝ} {c : ℝ}
    (hf : ∀ N, ∀ i ∈ D N, 0 ≤ f N i) (hμ : ∀ᶠ N in atTop, ∀ i ∈ D N, f N i ≤ μ N)
    (hμ0 : Tendsto μ atTop (𝓝 0)) (hsum : Tendsto (fun N => ∑ i ∈ D N, f N i) atTop (𝓝 c))
    (k : ℕ) : Tendsto (fun N => elemSymm (D N) (f N) k) atTop (𝓝 (c ^ k / k.factorial)) := by
  suffices h : ∀ k, Tendsto (fun N => elemSymm (D N) (f N) k) atTop (𝓝 (c ^ k / k.factorial)) ∧
      Tendsto (fun N => elemSymm (D N) (f N) (k + 1)) atTop
        (𝓝 (c ^ (k + 1) / (k + 1).factorial)) from (h k).1
  intro k
  induction k with
  | zero => exact ⟨by simp [elemSymm_zero], by simpa [elemSymm_one] using hsum⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hb := hμ.mono fun N hN => elemSymm_recursion_bounds (hf N) hN k
    have herr : Tendsto (fun N => (∑ i ∈ D N, f N i) * elemSymm (D N) (f N) (k + 1) -
        (k + 2 : ℝ) * elemSymm (D N) (f N) (k + 2)) atTop (𝓝 0) := by
      have hup : Tendsto (fun N => μ N * (∑ i ∈ D N, f N i) * elemSymm (D N) (f N) k) atTop
          (𝓝 0) := by
        simpa using (hμ0.mul hsum).mul ih.1
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (hb.mono fun N h => h.1) (hb.mono fun N h => h.2)
    have hmain : Tendsto (fun N => (∑ i ∈ D N, f N i) * elemSymm (D N) (f N) (k + 1)) atTop
        (𝓝 (c * (c ^ (k + 1) / (k + 1).factorial))) := hsum.mul ih.2
    have h2 := (hmain.sub herr).div_const (k + 2 : ℝ)
    have hk : (k + 2 : ℝ) ≠ 0 := by positivity
    convert h2 using 1
    · funext N; rw [show k + 1 + 1 = k + 2 from rfl]; field_simp; ring
    · rw [sub_zero, Nat.factorial_succ (k + 1)]; push_cast; congr 1; field_simp; ring

/-- Partial alternating sums of binomial coefficients:
`∑_{k ≤ j} (-1)^k C(W, k) = (-1)^j C(W - 1, j)` for `W ≥ 1` (and `1` for `W = 0`). -/
theorem sum_range_neg_one_pow_mul_choose (W j : ℕ) :
    ∑ k ∈ range (j + 1), (-1 : ℝ) ^ k * W.choose k =
      if W = 0 then 1 else (-1) ^ j * ((W - 1).choose j : ℝ) := by
  induction j with
  | zero => split_ifs <;> simp
  | succ j ih =>
    rw [sum_range_succ, ih]
    rcases Nat.eq_zero_or_pos W with rfl | hW
    · simp
    · obtain ⟨W', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hW.ne'
      simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.choose_succ_succ, Nat.cast_add,
        pow_succ]
      ring

/-- **Bonferroni inequality, even order** (pointwise): `1[W = 0] ≤ ∑_{k ≤ 2r} (-1)^k C(W, k)`. -/
theorem indicator_le_bonferroni (W r : ℕ) :
    (if W = 0 then (1 : ℝ) else 0) ≤ ∑ k ∈ range (2 * r + 1), (-1 : ℝ) ^ k * W.choose k := by
  rw [sum_range_neg_one_pow_mul_choose]
  split_ifs
  · rfl
  · rw [pow_mul]; norm_num

/-- **Bonferroni inequality, odd order** (pointwise): `∑_{k ≤ 2r+1} (-1)^k C(W, k) ≤ 1[W = 0]`. -/
theorem bonferroni_le_indicator (W r : ℕ) :
    ∑ k ∈ range (2 * r + 2), (-1 : ℝ) ^ k * W.choose k ≤ if W = 0 then 1 else 0 := by
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, sum_range_neg_one_pow_mul_choose]
  split_ifs
  · rfl
  · rw [pow_succ, pow_mul]; norm_num

/-- `C(#{i ∈ D | E i}, k)` counts the `k`-subsets of `D` on which every `E i` holds. -/
theorem choose_card_filter {ι : Type*} (D : Finset ι) (E : ι → Prop) [DecidablePred E] (k : ℕ) :
    (((D.filter E).card.choose k : ℕ) : ℝ) =
      ∑ T ∈ D.powersetCard k, if ∀ i ∈ T, E i then 1 else 0 := by
  classical
  rw [sum_boole, ← card_powersetCard]
  congr 2
  ext T
  simp only [mem_powersetCard, mem_filter, subset_iff]
  constructor
  · rintro ⟨h, hk⟩; exact ⟨⟨fun i hi => (h hi).1, hk⟩, fun i hi => (h hi).2⟩
  · rintro ⟨⟨h, hk⟩, hE⟩; exact ⟨fun i hi => ⟨h hi, hE i hi⟩, hk⟩

/-- **Poisson limit from Bonferroni bounds and factorial moments.** If `P0 N` is sandwiched by the
alternating partial sums of the factorial moments `S k N` (Bonferroni inequalities of every
order), and `S k N → c^k / k!` for every `k`, then `P0 N → e^{-c}`. -/
theorem tendsto_of_bonferroni {P0 : ℕ → ℝ} {S : ℕ → ℕ → ℝ} {c : ℝ}
    (hup : ∀ r, ∀ᶠ N in atTop, P0 N ≤ ∑ k ∈ range (2 * r + 1), (-1) ^ k * S k N)
    (hlo : ∀ r, ∀ᶠ N in atTop, ∑ k ∈ range (2 * r + 2), (-1) ^ k * S k N ≤ P0 N)
    (hS : ∀ k, Tendsto (S k) atTop (𝓝 (c ^ k / k.factorial))) :
    Tendsto P0 atTop (𝓝 (exp (-c))) := by
  have hser : Tendsto (fun j => ∑ k ∈ range j, (-1 : ℝ) ^ k * (c ^ k / k.factorial)) atTop
      (𝓝 (exp (-c))) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-c)).tendsto_sum_nat
    rw [← Real.exp_eq_exp_ℝ] at h
    refine h.congr fun j => sum_congr rfl fun k _ => ?_
    rw [neg_pow]; ring
  have hfin : ∀ j, Tendsto (fun N => ∑ k ∈ range j, (-1 : ℝ) ^ k * S k N) atTop
      (𝓝 (∑ k ∈ range j, (-1 : ℝ) ^ k * (c ^ k / k.factorial))) := fun j =>
    tendsto_finsetSum _ fun k _ => (hS k).const_mul _
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have h2 := hser.comp (tendsto_atTop_mono (fun r => (by omega : r ≤ 2 * r + 2)) tendsto_id)
    obtain ⟨r, hr⟩ := (h2.eventually (lt_mem_nhds ha)).exists
    filter_upwards [hlo r, (hfin (2 * r + 2)).eventually (lt_mem_nhds hr)] with N h1 h3
    exact h3.trans_le h1
  · have h2 := hser.comp (tendsto_atTop_mono (fun r => (by omega : r ≤ 2 * r + 1)) tendsto_id)
    obtain ⟨r, hr⟩ := (h2.eventually (gt_mem_nhds ha)).exists
    filter_upwards [hup r, (hfin (2 * r + 1)).eventually (gt_mem_nhds hr)] with N h1 h3
    exact h1.trans_lt h3

end Sieve

/-! ## Cross-diagonal dependence and the Gumbel limit -/

section Gumbel

variable {β : Type*} [Fintype β] (p q : β → ℝ) (s : β → β → ℝ) (m n : ℕ) (t : ℝ)

/-- The number `W` of diagonals of the `m × n` grid containing a segment that scores more
than `t`. -/
noncomputable def exceedCount (u v : List β) : ℕ :=
  ((offsets m n).filter fun d => t < maxSegScore (diag s u v d)).card

/-- The probability `p_d = P(M_d > t)` that diagonal `d` contains a segment scoring more
than `t`. -/
noncomputable def exceedProb (d : ℤ) : ℝ :=
  twoProb p q m n fun u v => t < maxSegScore (diag s u v d)

/-- The `k`-th factorial (binomial) moment `S_k = E[C(W, k)]` of the number of exceeding
diagonals; `exceedMoment_eq_sum`: it is `∑_{|T| = k} P(every diagonal in T exceeds t)`. -/
noncomputable def exceedMoment (k : ℕ) : ℝ :=
  twoExpect p q m n fun u v => ((exceedCount s m n t u v).choose k : ℝ)

/-- **The `k`-th cross-diagonal dependence coefficient** `Δ_k = S_k - e_k(p)`: the excess of the
`k`-th factorial moment of the number of exceeding diagonals over its value `e_k(p)` for
independent diagonals with the same marginals. `crossDep_eq_sum`: it is the sum over `k`-sets
`T` of diagonals of `P(⋂_{d ∈ T} {M_d > t}) - ∏_{d ∈ T} P(M_d > t)`. It vanishes for `k ≤ 1`
(`crossDep_zero`, `crossDep_one`), and the terms of letter-disjoint pairs vanish
(`twoProb_diag_and_diag_of_disjoint`); the diagonals are not independent in general, so for
`k ≥ 2` nothing forces it to vanish (it does vanish for the degenerate zero score, `crossDep_s0`
in the test file). -/
noncomputable def crossDep (k : ℕ) : ℝ :=
  exceedMoment p q s m n t k - elemSymm (offsets m n) (exceedProb p q s m n t) k

variable {p q}

/-- By the single-diagonal slice, `p_d` is a one-sequence tail probability for a sequence of
length `diagLen m n d`. -/
theorem exceedProb_eq (hp : IsDist p) (hq : IsDist q) (d : ℤ) :
    exceedProb p q s m n t d =
      scoreProb (pairLaw p q) (pairScore s) (diagLen m n d) fun l => t < maxSegScore l :=
  twoProb_diag hp hq s m n d fun l => t < maxSegScore l

theorem exceedProb_nonneg (hp : IsDist p) (hq : IsDist q) (d : ℤ) :
    0 ≤ exceedProb p q s m n t d :=
  twoProb_nonneg hp.1 hq.1 _ _ _

/-- At a Cramér root, `p_d ≤ diagLen m n d · e^{-θ t}` for `t > 0`. -/
theorem exceedProb_le (hp : IsDist p) (hq : IsDist q) {θ : ℝ} (hθ : 0 ≤ θ)
    (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1) {t : ℝ} (ht : 0 < t) (d : ℤ) :
    exceedProb p q s m n t d ≤ diagLen m n d * exp (-θ * t) := by
  rw [exceedProb_eq s m n t hp hq]
  refine le_trans (scoreProb_mono _ (isDist_pairLaw hp hq).1 fun l _ h => h.le) ?_
  exact scoreProb_le_maxSegScore_le _ (isDist_pairLaw hp hq) hθ hroot _ ht

theorem exceedMoment_eq_sum (k : ℕ) :
    exceedMoment p q s m n t k = ∑ T ∈ (offsets m n).powersetCard k,
      twoProb p q m n fun u v => ∀ d ∈ T, t < maxSegScore (diag s u v d) := by
  simp only [twoProb, ← twoExpect_sum, exceedMoment, exceedCount]
  refine wordExpect_congr p fun u _ => wordExpect_congr q fun v _ => ?_
  beta_reduce
  rw [choose_card_filter]
  exact sum_congr rfl fun T _ => by split_ifs <;> rfl

/-- **The dependence coefficient as a sum of joint-minus-product terms.** -/
theorem crossDep_eq_sum (k : ℕ) :
    crossDep p q s m n t k = ∑ T ∈ (offsets m n).powersetCard k,
      ((twoProb p q m n fun u v => ∀ d ∈ T, t < maxSegScore (diag s u v d)) -
        ∏ d ∈ T, exceedProb p q s m n t d) := by
  rw [crossDep, exceedMoment_eq_sum, elemSymm, sum_sub_distrib]

theorem crossDep_zero (hp : IsDist p) (hq : IsDist q) : crossDep p q s m n t 0 = 0 := by
  rw [crossDep, elemSymm_zero, exceedMoment]
  simp [twoExpect_const hp hq]

theorem crossDep_one : crossDep p q s m n t 1 = 0 := by
  rw [crossDep_eq_sum, powersetCard_one, sum_map]
  simp [exceedProb]

/-- **Bonferroni upper bounds** (every even order `2r`): for `t ≥ 0`,
`P(M_{m,n} ≤ t) ≤ ∑_{k ≤ 2r} (-1)^k S_k`, with `S_k = e_k(p) + Δ_k`. -/
theorem twoProb_maxAlignScore_le_le (hp : IsDist p) (hq : IsDist q) {t : ℝ} (ht : 0 ≤ t)
    (r : ℕ) :
    twoProb p q m n (fun u v => maxAlignScore s u v ≤ t) ≤
      ∑ k ∈ range (2 * r + 1), (-1) ^ k * exceedMoment p q s m n t k := by
  simp only [exceedMoment, ← twoExpect_const_mul, ← twoExpect_sum, twoProb]
  refine twoExpect_mono hp.1 hq.1 fun u v hu hv => ?_
  have hiff : maxAlignScore s u v ≤ t ↔ exceedCount s m n t u v = 0 := by
    rw [maxAlignScore_le_iff s u v ht, exceedCount, card_eq_zero, filter_eq_empty_iff, hu, hv]
  rw [if_congr hiff rfl rfl]
  exact indicator_le_bonferroni _ r

/-- **Bonferroni lower bounds** (every odd order `2r + 1`): for `t ≥ 0`,
`∑_{k ≤ 2r+1} (-1)^k S_k ≤ P(M_{m,n} ≤ t)`. -/
theorem le_twoProb_maxAlignScore_le (hp : IsDist p) (hq : IsDist q) {t : ℝ} (ht : 0 ≤ t)
    (r : ℕ) :
    ∑ k ∈ range (2 * r + 2), (-1) ^ k * exceedMoment p q s m n t k ≤
      twoProb p q m n (fun u v => maxAlignScore s u v ≤ t) := by
  simp only [exceedMoment, ← twoExpect_const_mul, ← twoExpect_sum, twoProb]
  refine twoExpect_mono hp.1 hq.1 fun u v hu hv => ?_
  have hiff : maxAlignScore s u v ≤ t ↔ exceedCount s m n t u v = 0 := by
    rw [maxAlignScore_le_iff s u v ht, exceedCount, card_eq_zero, filter_eq_empty_iff, hu, hv]
  rw [if_congr hiff rfl rfl]
  exact bonferroni_le_indicator _ r

theorem exceedMoment_eq_elemSymm_add (k : ℕ) :
    exceedMoment p q s m n t k =
      elemSymm (offsets m n) (exceedProb p q s m n t) k + crossDep p q s m n t k := by
  rw [crossDep]; ring

/-- **Second-order dependence control**, explicit at every finite size: for `t ≥ 0`,
`1 - ∑_d p_d ≤ P(M_{m,n} ≤ t) ≤ 1 - ∑_d p_d + e_2(p) + Δ_2`, where `Δ_2` is the pairwise
cross-diagonal dependence coefficient. -/
theorem twoProb_maxAlignScore_le_second_order (hp : IsDist p) (hq : IsDist q) {t : ℝ}
    (ht : 0 ≤ t) :
    1 - ∑ d ∈ offsets m n, exceedProb p q s m n t d ≤
        twoProb p q m n (fun u v => maxAlignScore s u v ≤ t) ∧
      twoProb p q m n (fun u v => maxAlignScore s u v ≤ t) ≤
        1 - ∑ d ∈ offsets m n, exceedProb p q s m n t d +
          elemSymm (offsets m n) (exceedProb p q s m n t) 2 + crossDep p q s m n t 2 := by
  have h0 := le_twoProb_maxAlignScore_le s m n hp hq ht 0
  have h1 := twoProb_maxAlignScore_le_le s m n hp hq ht 1
  simp only [exceedMoment_eq_elemSymm_add] at h0 h1
  norm_num [sum_range_succ] at h0 h1
  have e0 := crossDep_zero s m n t hp hq
  have e1 := crossDep_one (p := p) (q := q) s m n t
  have f0 := elemSymm_zero (offsets m n) (exceedProb p q s m n t)
  have f1 := elemSymm_one (offsets m n) (exceedProb p q s m n t)
  constructor <;> linarith

/-- At most `2 L₀` diagonals of an `m × n` grid with `m, n ≥ L₀` are shorter than `L₀`. -/
theorem card_filter_diagLen_lt_le {m n L₀ : ℕ} (hm : L₀ ≤ m) (hn : L₀ ≤ n) :
    ((offsets m n).filter fun d => diagLen m n d < L₀).card ≤ 2 * L₀ := by
  calc ((offsets m n).filter fun d => diagLen m n d < L₀).card
      ≤ (Ioo (-(m : ℤ)) (L₀ - m) ∪ Ioo ((n : ℤ) - L₀) n).card := by
        refine card_le_card fun d hd => ?_
        rw [mem_filter, offsets, mem_Ioo, diagLen] at hd
        rw [mem_union, mem_Ioo, mem_Ioo]
        omega
    _ ≤ (Ioo (-(m : ℤ)) (L₀ - m)).card + (Ioo ((n : ℤ) - L₀) n).card := card_union_le _ _
    _ ≤ 2 * L₀ := by simp only [Int.card_Ioo]; omega

/-- `e^{-θ t} = e^{-θ x} / (m n)` at the threshold `t = log (m n) / θ + x`. -/
theorem exp_neg_mul_threshold {θ : ℝ} (hθ : θ ≠ 0) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    exp (-θ * (log y / θ + x)) = exp (-θ * x) / y := by
  rw [show -θ * (log y / θ + x) = -θ * x - log y by field_simp; ring, exp_sub, exp_log hy]

/-- **One-sequence tail input** for the maximal segment score `M_L` of `L` iid scores with law
`(q, f)`: `P(M_L > t) = (K + o(1)) L e^{-θ t}` as `L → ∞` and `L e^{-θ t} → 0`, uniformly over
thresholds `t ≤ η L` for some `η > 0`. This is the Iglehart (1972) / Karlin–Dembo (1992) tail in
the form the two-sequence problem needs; it is a hypothesis here, not derived.

The cap `t ≤ η L` is necessary: scores are bounded, so `P(M_L > t) = 0` once `t` exceeds `L` times
the largest score, and without the cap the relative-error bound would force `K = 0`. The classical
asymptotic holds only below the slope of the walk under the tilted law, which a small `η`
respects. The definition carries no nonlattice hypothesis. It is meant for the nondegenerate
classical regime `K > 0` of nonlattice scores: for nondegenerate scores on a lattice `hℤ` the
classical ratio `P(M_L > t) / (L e^{-θ t})` oscillates with the fractional part of `t / h`
(compare `LatticeRenewalInput` in `GumbelTail`). It also holds in degenerate cases: the
lattice-valued zero score satisfies it with `K = 0` (`oneSequenceTail_s0` in the test file). -/
def OneSequenceTail {γ : Type*} [Fintype γ] (q f : γ → ℝ) (θ K : ℝ) : Prop :=
  ∀ ε > 0, ∃ L₀ : ℕ, ∃ δ > 0, ∃ η > 0, ∀ L : ℕ, L₀ ≤ L → ∀ t : ℝ,
    (L : ℝ) * exp (-θ * t) ≤ δ → t ≤ η * L →
      |scoreProb q f L (fun l => t < maxSegScore l) - K * L * exp (-θ * t)| ≤ ε * L * exp (-θ * t)

section Marginal

variable {p q : β → ℝ} (s : β → β → ℝ)

/-- Finite-size form of the diagonal sum with cutoff `ℓ ≤ m, n`: if the one-sequence tail estimate
holds at threshold `t` for every diagonal length `ℓ ≤ L ≤ n`, then
`|∑_d p_d - K m n e^{-θ t}| ≤ ε m n e^{-θ t} + 2 (1 + |K|) ℓ² e^{-θ t}`. The long diagonals use the
tail estimate; the at most `2 ℓ` diagonals shorter than `ℓ` use the Cramér bound. -/
theorem abs_sum_exceedProb_sub_le (hp : IsDist p) (hq : IsDist q) {θ K ε : ℝ} {ℓ m n : ℕ}
    {t : ℝ} (hθ : 0 ≤ θ) (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : ∀ L : ℕ, ℓ ≤ L → L ≤ n →
      |scoreProb (pairLaw p q) (pairScore s) L (fun l => t < maxSegScore l) -
        K * L * exp (-θ * t)| ≤ ε * L * exp (-θ * t))
    (hε : 0 ≤ ε) (hm : ℓ ≤ m) (hn : ℓ ≤ n) (ht : 0 < t) :
    |∑ d ∈ offsets m n, exceedProb p q s m n t d - K * (m * n) * exp (-θ * t)| ≤
      ε * (m * n) * exp (-θ * t) + 2 * (1 + |K|) * ℓ ^ 2 * exp (-θ * t) := by
  set E := exp (-θ * t) with hE
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hterm : ∀ d ∈ offsets m n, |exceedProb p q s m n t d - K * diagLen m n d * E| ≤
      ε * diagLen m n d * E + if diagLen m n d < ℓ then (1 + |K|) * ℓ * E else 0 := by
    intro d _
    split_ifs with hshort
    · have h0 := exceedProb_nonneg s m n t hp hq d
      have h1 := exceedProb_le s m n hp hq hθ hroot ht d
      rw [← hE] at h1
      have hL : (diagLen m n d : ℝ) ≤ ℓ := by exact_mod_cast hshort.le
      have hLE : (diagLen m n d : ℝ) * E ≤ ℓ * E := mul_le_mul_of_nonneg_right hL hE0
      have hKLE : |K * diagLen m n d * E| ≤ |K| * (ℓ * E) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hE0, Nat.abs_cast, mul_assoc]
        exact mul_le_mul_of_nonneg_left hLE (abs_nonneg K)
      have hεLE : 0 ≤ ε * diagLen m n d * E := by positivity
      calc |exceedProb p q s m n t d - K * diagLen m n d * E|
          ≤ |exceedProb p q s m n t d| + |K * diagLen m n d * E| := abs_sub _ _
        _ ≤ ℓ * E + |K| * (ℓ * E) := by rw [abs_of_nonneg h0]; linarith
        _ ≤ ε * diagLen m n d * E + (1 + |K|) * ℓ * E := by linarith
    · rw [add_zero, exceedProb_eq s m n t hp hq]
      exact htail _ (not_lt.1 hshort) ((min_le_right _ _).trans (Nat.sub_le _ _))
  have hsum : K * (m * n) * E = ∑ d ∈ offsets m n, K * diagLen m n d * E := by
    rw [← sum_diagLen m n, mul_sum, sum_mul]
  rw [hsum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
  have hfirst : ∑ d ∈ offsets m n, ε * diagLen m n d * E = ε * (m * n) * E := by
    rw [← sum_diagLen m n, mul_sum, sum_mul]
  rw [hfirst]
  have hcard : (((offsets m n).filter fun d => diagLen m n d < ℓ).card : ℝ) ≤ 2 * ℓ := by
    exact_mod_cast card_filter_diagLen_lt_le hm hn
  have hc : 0 ≤ (1 + |K|) * ℓ * E := by positivity
  nlinarith

/-- Under the growth condition `log n / m → 0`, the threshold `t_N = log (m n) / θ + x` is
`o(m)`. -/
theorem tendsto_threshold_div {θ : ℝ} {m n : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    (hn : Tendsto n atTop atTop) (hlog : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (x : ℝ) : Tendsto (fun N => (log (m N * n N) / θ + x) / m N) atTop (𝓝 0) := by
  have hmR : Tendsto (fun N => (m N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun N => (n N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hlm : Tendsto (fun N => log (m N) / m N) atTop (𝓝 0) := by
    refine ((tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hmR).congr fun N => ?_
    simp
  have hlim : Tendsto (fun N => (log (m N) / m N + log (n N) / m N) / θ + x * (m N : ℝ)⁻¹)
      atTop (𝓝 0) := by
    simpa using ((hlm.add hlog).div_const θ).add (hmR.inv_tendsto_atTop.const_mul x)
  refine hlim.congr' ?_
  filter_upwards [hmR.eventually_gt_atTop 0, hnR.eventually_gt_atTop 0] with N hm0 hn0
  rw [log_mul hm0.ne' hn0.ne']
  field_simp

/-- **The expected number of exceeding diagonals**: at the threshold
`t_N = log (m_N n_N) / θ + x`, `∑_d P(M_d > t_N) → K e^{-θ x}` as `m_N, n_N → ∞` with
`log n_N / m_N → 0` and `log m_N / n_N → 0`. Diagonals shorter than
`ℓ_N = max L₀ ⌈t_N / η⌉ = o(min m_N n_N)` are handled by the Cramér bound, the others by the
one-sequence tail. -/
theorem tendsto_sum_exceedProb (hp : IsDist p) (hq : IsDist q) {θ K : ℝ} (hθ : 0 < θ)
    (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : OneSequenceTail (pairLaw p q) (pairScore s) θ K) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn' : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun N => ∑ d ∈ offsets (m N) (n N),
        exceedProb p q s (m N) (n N) (log (m N * n N) / θ + x) d) atTop
      (𝓝 (K * exp (-θ * x))) := by
  set A := exp (-θ * x) with hA
  have hA0 : 0 < A := exp_pos _
  have hmR : Tendsto (fun N => (m N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun N => (n N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmn : Tendsto (fun N => (m N : ℝ) * n N) atTop atTop := hmR.atTop_mul_atTop₀ hnR
  have htm := tendsto_threshold_div (θ := θ) hm hn hnm x
  have htn : Tendsto (fun N => (log (m N * n N) / θ + x) / n N) atTop (𝓝 0) := by
    simpa only [mul_comm (m _ : ℝ)] using tendsto_threshold_div (θ := θ) hn hm hmn' x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, δ, hδ, η, hη, hL⟩ := htail (ε / (2 * A)) (by positivity)
  set c := 2 * (1 + |K|) * A with hc
  have hc0 : 0 < c := by positivity
  set ρ := min 1 (ε / (4 * c)) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hcρ : c * ρ ^ 2 < ε / 2 := by
    have h1 : ρ ^ 2 ≤ ρ := by nlinarith
    have h2 : c * ρ ≤ ε / 4 :=
      (mul_le_mul_of_nonneg_left (min_le_right 1 (ε / (4 * c))) hc0.le).trans_eq
        (by field_simp)
    nlinarith
  -- `r N = L₀ + 1 + t_N / η` is `o(m)` and `o(n)`
  have hr : ∀ k : ℕ → ℕ, Tendsto (fun N => (k N : ℝ)) atTop atTop →
      Tendsto (fun N => (log (m N * n N) / θ + x) / k N) atTop (𝓝 0) →
      Tendsto (fun N => (L₀ + 1 + (log (m N * n N) / θ + x) / η) / k N) atTop (𝓝 0) := by
    intro k hk hkt
    have := (hk.inv_tendsto_atTop.const_mul ((L₀ : ℝ) + 1)).add (hkt.div_const η)
    simp only [mul_zero, zero_div, add_zero] at this
    refine this.congr fun N => ?_
    simp only [Pi.inv_apply]; ring
  have hev : ∀ᶠ N in atTop, A / δ ≤ m N ∧ A + 1 ≤ (m N : ℝ) * n N ∧
      (L₀ + 1 + (log (m N * n N) / θ + x) / η) / m N < ρ ∧
      (L₀ + 1 + (log (m N * n N) / θ + x) / η) / n N < ρ ∧ (0 : ℝ) < m N ∧ (0 : ℝ) < n N :=
    (hmR.eventually_ge_atTop _).and ((hmn.eventually_ge_atTop _).and
      (((hr m hmR htm).eventually (gt_mem_nhds hρ0)).and
        (((hr n hnR htn).eventually (gt_mem_nhds hρ0)).and
          ((hmR.eventually_gt_atTop 0).and (hnR.eventually_gt_atTop 0)))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h3, h4, hrm, hrn, hmpos, hnpos⟩ := hN₀ N hN
  set M := (m N : ℝ) * n N with hM
  have hM0 : 0 < M := mul_pos hmpos hnpos
  set t := log M / θ + x with ht
  have hEt : exp (-θ * t) = A / M := exp_neg_mul_threshold hθ.ne' hM0 x
  have htpos : 0 < t := by
    have : -θ * t < 0 := by
      rw [← Real.exp_lt_one_iff, hEt, div_lt_one hM0]; linarith
    nlinarith
  set r := (L₀ : ℝ) + 1 + t / η with hr_def
  have hrm' : r < ρ * m N := (div_lt_iff₀ hmpos).1 hrm
  have hrn' : r < ρ * n N := (div_lt_iff₀ hnpos).1 hrn
  set ℓ := max L₀ ⌈t / η⌉₊ with hℓ
  have htη : 0 ≤ t / η := by positivity
  have hℓr : (ℓ : ℝ) ≤ r := by
    rw [hℓ, Nat.cast_max]
    refine max_le (by linarith) ?_
    linarith [Nat.ceil_lt_add_one htη]
  have hℓm : ℓ ≤ m N := by
    have : (ℓ : ℝ) ≤ m N := by nlinarith
    exact_mod_cast this
  have hℓn : ℓ ≤ n N := by
    have : (ℓ : ℝ) ≤ n N := by nlinarith
    exact_mod_cast this
  have hnδ : (n N : ℝ) * exp (-θ * t) ≤ δ := by
    have hnA : (n N : ℝ) * (A / M) = A / m N := by rw [hM]; field_simp
    rw [hEt, hnA, div_le_iff₀ hmpos]
    rw [div_le_iff₀ hδ] at h3; linarith
  have htail' : ∀ L : ℕ, ℓ ≤ L → L ≤ n N →
      |scoreProb (pairLaw p q) (pairScore s) L (fun l => t < maxSegScore l) -
        K * L * exp (-θ * t)| ≤ ε / (2 * A) * L * exp (-θ * t) := by
    intro L hLℓ hLn
    refine hL L ((le_max_left _ _).trans hLℓ) t ?_ ?_
    · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hLn) (exp_pos _).le) hnδ
    · have h1 : t / η ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hLℓ)
      rwa [div_le_iff₀ hη, mul_comm] at h1
  have key := abs_sum_exceedProb_sub_le s hp hq hθ.le hroot htail' (by positivity) hℓm hℓn htpos
  rw [hEt] at key
  rw [Real.dist_eq]
  have e1 : K * M * (A / M) = K * A := by field_simp
  have e2 : ε / (2 * A) * M * (A / M) = ε / 2 := by field_simp
  have e3 : 2 * (1 + |K|) * (ℓ : ℝ) ^ 2 * (A / M) = c * ((ℓ : ℝ) ^ 2 / M) := by rw [hc]; ring
  rw [e1, e2, e3] at key
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hsq : (ℓ : ℝ) ^ 2 / M ≤ ρ ^ 2 := by
    rw [div_le_iff₀ hM0, hM]
    have h1 : (ℓ : ℝ) ≤ ρ * m N := by linarith
    have h2 : (ℓ : ℝ) ≤ ρ * n N := by linarith
    nlinarith
  have : c * ((ℓ : ℝ) ^ 2 / M) ≤ c * ρ ^ 2 := mul_le_mul_of_nonneg_left hsq hc0.le
  linarith

end Marginal

/-- **Gumbel limit for the maximal ungapped two-sequence alignment score, conditional on
asymptotic independence of diagonals** (Karlin and Altschul 1990; Dembo, Karlin and
Zeitouni 1994), given the one-sequence tail `OneSequenceTail`. No lattice hypothesis is imposed;
the intended regime is the classical nonlattice one with `K > 0`.

Two independent iid sequences of lengths `m_N, n_N → ∞`, with `log n_N / m_N → 0` and
`log m_N / n_N → 0`, letter laws `p, q`, are scored by `s`. Let `θ > 0` be the Karlin–Altschul root
`E e^{θ s(A, B)} = 1` (unique in the usual regime, `existsUnique_karlinAltschul_root`) and `K` the
one-sequence constant of the pair-score walk (`OneSequenceTail`). If the cross-diagonal dependence
coefficients vanish, `Δ_k(N) = crossDep … k → 0` for every `k`, then
`P(M_{m,n} ≤ log (m n) / θ + x) → exp (-K e^{-θ x})`.

The dependence is isolated in `Δ_k` at every finite size: the Bonferroni inequalities of every
order sandwich `P(M ≤ t)` between partial sums of `S_k = e_k(p) + Δ_k`
(`twoProb_maxAlignScore_le_le`, `le_twoProb_maxAlignScore_le`), and the marginals give
`∑_d p_d → K e^{-θ x}` (`tendsto_sum_exceedProb`) and `max_d p_d → 0`, hence
`e_k(p) → (K e^{-θ x})^k / k!` (`tendsto_elemSymm`). The limit takes `Δ_k → 0` as a hypothesis (it
is the Poisson-approximation step of Dembo–Karlin–Zeitouni, not proved here; it can fail when
their entropy condition fails); given the marginal limit it is equivalent to Poisson convergence
of the factorial moments `S_k`. -/
theorem tendsto_twoProb_maxAlignScore_le (hp : IsDist p) (hq : IsDist q) {θ K : ℝ} (hθ : 0 < θ)
    (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : OneSequenceTail (pairLaw p q) (pairScore s) θ K) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn' : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ)
    (hdep : ∀ k, Tendsto (fun N => crossDep p q s (m N) (n N) (log (m N * n N) / θ + x) k)
      atTop (𝓝 0)) :
    Tendsto (fun N => twoProb p q (m N) (n N)
        fun u v => maxAlignScore s u v ≤ log (m N * n N) / θ + x) atTop
      (𝓝 (exp (-(K * exp (-θ * x))))) := by
  set A := exp (-θ * x) with hA
  have hmR : Tendsto (fun N => (m N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun N => (n N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmn : Tendsto (fun N => (m N : ℝ) * n N) atTop atTop := hmR.atTop_mul_atTop₀ hnR
  -- eventually the threshold is positive and `e^{-θ t} = A / (m n)`
  have hpos : ∀ᶠ N in atTop, 0 < (m N : ℝ) ∧ 0 < (n N : ℝ) ∧ A + 1 ≤ (m N : ℝ) * n N :=
    (hmR.eventually_gt_atTop 0).and ((hnR.eventually_gt_atTop 0).and
      (hmn.eventually_ge_atTop _))
  have hthr : ∀ᶠ N in atTop, 0 < log (m N * n N) / θ + x ∧
      exp (-θ * (log (m N * n N) / θ + x)) = A / (m N * n N) := by
    filter_upwards [hpos] with N ⟨hm0, hn0, hA1⟩
    have hM0 : (0 : ℝ) < m N * n N := mul_pos hm0 hn0
    have hEt := exp_neg_mul_threshold hθ.ne' hM0 x
    refine ⟨?_, hEt⟩
    have : -θ * (log (m N * n N) / θ + x) < 0 := by
      rw [← Real.exp_lt_one_iff, hEt, div_lt_one hM0]; linarith
    nlinarith
  -- the factorial moments converge to those of a Poisson law
  have he : ∀ k, Tendsto (fun N => elemSymm (offsets (m N) (n N))
      (exceedProb p q s (m N) (n N) (log (m N * n N) / θ + x)) k) atTop
      (𝓝 ((K * A) ^ k / k.factorial)) := by
    intro k
    refine tendsto_elemSymm (μ := fun N => A / m N)
      (fun N d _ => exceedProb_nonneg s _ _ _ hp hq d) ?_ ?_
      (tendsto_sum_exceedProb s hp hq hθ hroot htail hm hn hnm hmn' x) k
    · filter_upwards [hpos, hthr] with N ⟨hm0, hn0, _⟩ ⟨ht, hEt⟩ d _
      refine (exceedProb_le s _ _ hp hq hθ.le hroot ht d).trans ?_
      rw [hEt]
      have hL : (diagLen (m N) (n N) d : ℝ) ≤ n N := by
        exact_mod_cast (min_le_right _ _).trans (Nat.sub_le _ _)
      calc (diagLen (m N) (n N) d : ℝ) * (A / (m N * n N)) ≤ n N * (A / (m N * n N)) :=
            mul_le_mul_of_nonneg_right hL (by positivity)
        _ = A / m N := by field_simp
    · have h := hmR.inv_tendsto_atTop.const_mul A
      rw [mul_zero] at h
      exact h.congr fun N => (div_eq_mul_inv _ _).symm
  have hS : ∀ k, Tendsto (fun N => exceedMoment p q s (m N) (n N) (log (m N * n N) / θ + x) k)
      atTop (𝓝 ((K * A) ^ k / k.factorial)) := fun k => by
    simpa [crossDep] using (he k).add (hdep k)
  exact tendsto_of_bonferroni
    (fun r => hthr.mono fun N h => twoProb_maxAlignScore_le_le s _ _ hp hq h.1.le r)
    (fun r => hthr.mono fun N h => le_twoProb_maxAlignScore_le s _ _ hp hq h.1.le r) hS

end Gumbel

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence
