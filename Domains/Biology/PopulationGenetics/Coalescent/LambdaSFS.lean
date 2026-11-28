/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
public import Domains.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
import Mathlib.Data.Nat.Choose.Sum

/-!
# The expected site frequency spectrum under Λ-coalescents

In a Λ-coalescent (`LambdaCoalescent`) with `b` blocks, each particular set of `k` blocks
(`2 ≤ k ≤ b`) merges at rate `λ_{b,k}`, and some merger happens at total rate `λ_b`. Only the
block sizes matter for the site frequency spectrum, so we follow the **jump chain** on lists of
block sizes: from the list `s` of `b` sizes, the blocks at a set `K` of positions merge
(`mergeSet s K`: drop them and append one block of their total size) with probability
`λ_{b,|K|} / λ_b`, and the chain holds `s` for an exponential time of mean `1 / λ_b`
(Pitman 1999). States with fewer than two blocks are absorbing.
`jumpStep` is the transition operator of this chain acting on statistics of block-size lists,
so its `j`-th iterate at `s` is the expectation of a statistic after `j` jumps.

A block of size `i` is a branch subtending `i` sample copies, so the expected total length of
branches subtending exactly `i` copies is the expected occupation sum
`E L_i(s) = ∑_{j ≥ 0} E [#{blocks of size i at jump j} / λ_{b_j}]` (`expectedLength`; the sum
is finite because every jump removes at least one block, see `expectedLength_eq_sum`). Under
neutral infinite-sites mutation at rate `θ / 2` per lineage, the expected number of sites whose
derived allele is carried by exactly `i` of the `n` sample copies is
`E ξ_i = (θ / 2) E L_i` (`expectedSFS`), as in the Kingman case
(`SiteFrequencySpectrum.integral_sfs`). Like `SiteFrequencySpectrum.joinStep`, this file works
with the transition operator of the chain and does not construct the process.

## Main definitions

* `mergeSet s K`: merge the blocks at the positions in `K`.
* `jumpStep Λ g s`: the transition operator of the block-size jump chain.
* `expectedLength Λ i s`: the expected length of branches subtending `i` copies, started from
  the block sizes `s`.
* `expectedSFS Λ θ n i`: the expected site frequency spectrum `E ξ_i` of a sample of `n`.

## Main results

* `expectedLength_eq`: the **first-step decomposition** of the jump chain's occupation sum,
  `E L_i(s) = #{size i in s} / λ_b + ∑_K (λ_{b,|K|} / λ_b) E L_i(mergeSet s K)`. Its
  block-count counterpart is the first-jump recursion (8) of Birkner, Blath & Eldon (2013) for
  the expected time `g(n, m)` spent with `m` blocks.
* `jumpStep_const`, `jumpStep_comp_length`: the transition probabilities sum to `1`, and the
  number of blocks jumps from `b` to `b + 1 - k` with probability `(b.choose k) λ_{b,k} / λ_b`,
  the jump chain of `LambdaCoalescent.blockCountingGenerator`.
* `expectedLength_dirac_zero`, `expectedSFS_dirac_zero`: for Kingman's coalescent
  (`Λ = δ₀`) the spectrum is Fu's `E ξ_i = θ / i`.
* `expectedLength_dirac_one`, `expectedSFS_dirac_one`: for the star coalescent (`Λ = δ₁`),
  where all `n` lineages merge at once, `E ξ_1 = n θ / 2` and `E ξ_i = 0` for `i ≥ 2`.
* `expectedLength_three_one`, `expectedLength_three_two`: for any `Λ ≠ 0` and `n = 3`,
  `E L_1 = 3 / λ_3 + 3 λ_{3,2} / (λ_3 λ_2)` and `E L_2 = 3 λ_{3,2} / (λ_3 λ_2)`.

Birkner, Blath & Eldon (2013) compute the spectrum on block counts instead: their Prop. 1.1
gives `E ξ_i = (θ / 2) ∑_k p⁽ⁿ⁾[k, i] k g(n, k)`, where `g(n, k)` solves the first-jump
recursion (8) and `p⁽ⁿ⁾[k, i]`, the probability that a given one of `k` blocks has size `i`,
solves the recursion of their Prop. A1. Prop. 1.1 and recursions (8) and (A1) are not
formalized here.

## References

* M. Birkner, J. Blath, B. Eldon, *Statistical properties of the site-frequency spectrum
  associated with Λ-coalescents*, Genetics 195 (2013), 1037–1053.
* J. Pitman, *Coalescents with multiple collisions*, Ann. Probab. 27 (1999), 1870–1902.
* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
-/

@[expose] public section

open MeasureTheory Finset unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaSFS

/-! ### Merging a set of blocks -/

/-- `eraseIdxs K l k`: the entries of `l` whose positions, counted from `k`, are not in `K`.
Elements of `K` below `k` or beyond the end of `l` remove nothing. -/
def eraseIdxs (K : Finset ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: l, k => if k ∈ K then eraseIdxs K l (k + 1) else a :: eraseIdxs K l (k + 1)

/-- Merge the blocks of the block-size list `b` at the positions in `K`: remove them and append
one block of their total size. A position beyond the end of `b` removes nothing and counts as
`0`; for `K = ∅` a block of size `0` is appended. For a pair `K = {i, j}` this is
`SiteFrequencySpectrum.mergeBlocks b i j` (`mergeSet_pair`). The intended use is a set `K` of at
least two positions of `b`; in the jump chain smaller sets have probability `0`. -/
def mergeSet (b : List ℕ) (K : Finset ℕ) : List ℕ :=
  eraseIdxs K b 0 ++ [∑ m ∈ K, b.getD m 0]

theorem eraseIdxs_of_lt {K : Finset ℕ} :
    ∀ (l : List ℕ) {k : ℕ}, (∀ x ∈ K, x < k) → eraseIdxs K l k = l
  | [], _, _ => rfl
  | a :: l, k, h => by
    have hk : k ∉ K := fun hk => lt_irrefl _ (h k hk)
    simp only [eraseIdxs, hk, ↓reduceIte]
    rw [eraseIdxs_of_lt l fun x hx => (h x hx).trans (Nat.lt_succ_self k)]

/-- For `m` the largest element of `K` and positions numbered from `k ≤ m`: removing the entry
at position `m` first (index `m - k` of `l`, by `List.eraseIdx`) and then the positions of
`K.erase m` gives the same list as removing the positions of `K`; it does not shift the other
positions. -/
theorem eraseIdxs_eq_eraseIdx {K : Finset ℕ} {m : ℕ} (hm : m ∈ K) (hK : ∀ x ∈ K, x ≤ m) :
    ∀ (l : List ℕ) {k : ℕ}, k ≤ m →
      eraseIdxs K l k = eraseIdxs (K.erase m) (l.eraseIdx (m - k)) k
  | [], _, _ => by simp [eraseIdxs]
  | a :: l, k, hkm => by
    rcases hkm.lt_or_eq with hlt | rfl
    · obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
      have hd' : m - (k + 1) = d := by omega
      have hkK : k ∈ K.erase m ↔ k ∈ K := by simp [Finset.mem_erase, hlt.ne]
      rw [hd, List.eraseIdx_cons_succ]
      simp only [eraseIdxs, hkK]
      rw [eraseIdxs_eq_eraseIdx hm hK l (k := k + 1) (by omega), hd']
    · simp only [Nat.sub_self, List.eraseIdx_cons_zero, eraseIdxs, hm, ↓reduceIte]
      rw [eraseIdxs_of_lt l (fun x hx => Nat.lt_succ_of_le (hK x hx)),
        eraseIdxs_of_lt l (fun x hx => lt_of_le_of_ne (hK x (Finset.mem_of_mem_erase hx))
          (Finset.ne_of_mem_erase hx))]

theorem length_eraseIdxs_add (K : Finset ℕ) : ∀ (l : List ℕ) (k : ℕ),
    (eraseIdxs K l k).length + ∑ m ∈ range l.length, (if k + m ∈ K then 1 else 0) = l.length
  | [], k => by simp [eraseIdxs]
  | a :: l, k => by
    have ih := length_eraseIdxs_add K l (k + 1)
    have hsum : ∑ m ∈ range l.length, (if k + (m + 1) ∈ K then 1 else 0) =
        ∑ m ∈ range l.length, (if k + 1 + m ∈ K then 1 else 0) :=
      sum_congr rfl fun m _ => by rw [show k + (m + 1) = k + 1 + m by omega]
    rw [List.length_cons, Finset.sum_range_succ', hsum, add_zero]
    by_cases hk : k ∈ K
    · simp only [eraseIdxs, hk, ↓reduceIte]; omega
    · simp only [eraseIdxs, hk, ↓reduceIte, List.length_cons]; omega

/-- Merging the blocks at `k` of the `b` positions leaves `b + 1 - k` blocks. -/
theorem length_mergeSet {b : List ℕ} {K : Finset ℕ} (hK : K ⊆ range b.length) :
    (mergeSet b K).length = b.length + 1 - K.card := by
  have h := length_eraseIdxs_add K b 0
  simp only [zero_add] at h
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hK,
    Nat.cast_id] at h
  rw [mergeSet, List.length_append, List.length_singleton]
  omega

/-- For a pair of positions `i < j`, `mergeSet` is `SiteFrequencySpectrum.mergeBlocks`. The only
hypothesis is `i < j`: if `j` is a position of `b` this is the merger of two blocks; if only `i`
is, both delete the entry at `i` and append its value; if neither is, both append `0`. -/
theorem mergeSet_pair (b : List ℕ) {i j : ℕ} (hij : i < j) :
    mergeSet b {i, j} = mergeBlocks b i j := by
  rw [mergeSet, mergeBlocks, sum_pair hij.ne]
  congr 1
  have hjmax : ∀ x ∈ ({i, j} : Finset ℕ), x ≤ j := by simp [hij.le]
  rw [eraseIdxs_eq_eraseIdx (m := j) (by simp) hjmax b (Nat.zero_le _), Nat.sub_zero,
    show ({i, j} : Finset ℕ).erase j = {i} by
      ext x; simp only [mem_erase, mem_insert, mem_singleton]; omega,
    eraseIdxs_eq_eraseIdx (m := i) (mem_singleton_self i) (by simp) _ (Nat.zero_le _),
    Nat.sub_zero, erase_singleton, eraseIdxs_of_lt _ (by simp)]

/-! ### The jump chain of the block sizes -/

variable (Λ : Measure I) [IsFiniteMeasure Λ]

/-- The **transition operator of the block-size jump chain** of the Λ-coalescent, acting on a
statistic `g` of block-size lists: from `b` (with `b.length` blocks), the blocks at the
positions in `K` merge with probability `λ_{b,|K|} / λ_b` (`mergerRate` vanishes unless
`2 ≤ |K|`). A state with total merger rate `0` (fewer than two blocks, or `Λ = 0`) is
absorbing. It is defined on all lists of naturals; the configurations of a genealogy are the
lists of positive block sizes. -/
def jumpStep (g : List ℕ → ℝ) (b : List ℕ) : ℝ :=
  if totalMergerRate Λ b.length = 0 then g b
  else ∑ K ∈ (range b.length).powerset,
    mergerRate Λ b.length K.card / totalMergerRate Λ b.length * g (mergeSet b K)

/-- The number of entries of `b` equal to `i`, divided by the total merger rate `λ_b`. With the
convention `x / 0 = 0` it is `0` when `λ_b = 0`. When `λ_b > 0` and `b` lists positive block
sizes, `1 / λ_b` is the mean holding time of `b` and this is the expected length, accumulated
while the chain sits in `b`, of branches subtending `i` copies; when `λ_b = 0` the state is never
left and that reading fails. -/
def holdingCount (i : ℕ) (b : List ℕ) : ℝ :=
  (b.count i : ℝ) / totalMergerRate Λ b.length

/-- The **expected total length of branches subtending exactly `i` sample copies**, for the
Λ-coalescent started from the block sizes `b`: the expected occupation sum
`∑_j E [holdingCount Λ i (X_j)]` over the jump chain `X`. It is defined for every list of
naturals; the branch-length reading needs `Λ ≠ 0`, positive block sizes and `i ≥ 1`. For
`Λ ≠ 0`, jumps after the first `b.length` contribute nothing (`expectedLength_eq_sum`). For
`Λ = 0` nothing ever merges, so from at least two blocks, one of size `i`, the true length is
infinite; the definition returns `0`, since every holding count is then `b.count i / 0 = 0`,
even when `b.count i > 0`, and this `0` is not an expected length. -/
def expectedLength (i : ℕ) (b : List ℕ) : ℝ :=
  ∑ j ∈ range b.length, (jumpStep Λ)^[j] (holdingCount Λ i) b

/-- The **expected site frequency spectrum** `E ξ_i = (θ / 2) E L_i` of a sample of `n` gene
copies under the Λ-coalescent, defined for every real `θ`. For `Λ ≠ 0`, `n ≥ 2` and `θ ≥ 0`,
with neutral infinite-sites mutation at rate `θ / 2` per lineage, it is the expected number of
segregating sites whose derived allele is carried by exactly `i` copies; for `θ < 0` it is not a
count. For `Λ = 0` and for `n ≤ 1` it is `0`, as `expectedLength` is (by `x / 0 = 0`); at
`Λ = 0` with `n ≥ 2` this `0` is not in general the expected count: for `θ > 0` the expected
number of singleton sites is infinite. -/
def expectedSFS (θ : ℝ) (n i : ℕ) : ℝ :=
  θ / 2 * expectedLength Λ i (List.replicate n 1)

/-! ### Rates -/

theorem mergerRate_of_lt_two {b k : ℕ} (hk : k < 2) : mergerRate Λ b k = 0 := by
  rw [mergerRate, ite_eq_right (by omega)]

theorem totalMergerRate_of_lt_two {b : ℕ} (hb : b < 2) : totalMergerRate Λ b = 0 := by
  rw [totalMergerRate, Icc_eq_empty (by omega), sum_empty]

/-- For `Λ ≠ 0`, some merger happens at positive rate as soon as there are two blocks. -/
theorem totalMergerRate_pos (hΛ : Λ ≠ 0) {b : ℕ} (hb : 2 ≤ b) : 0 < totalMergerRate Λ b := by
  have h2 : totalMergerRate Λ 2 = Λ.real Set.univ := by
    simp [totalMergerRate, mergerRate_two_two]
  have hpos : 0 < Λ.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hΛ) (measure_ne_top _ _)
  calc 0 < Λ.real Set.univ := hpos
    _ = totalMergerRate Λ 2 := h2.symm
    _ ≤ totalMergerRate Λ b := totalMergerRate_mono Λ hb

/-! ### The transition operator -/

theorem jumpStep_of_eq_zero {g : List ℕ → ℝ} {b : List ℕ}
    (h : totalMergerRate Λ b.length = 0) : jumpStep Λ g b = g b := by
  rw [jumpStep, ite_eq_left h]

theorem jumpStep_of_ne_zero {g : List ℕ → ℝ} {b : List ℕ}
    (h : totalMergerRate Λ b.length ≠ 0) :
    jumpStep Λ g b = ∑ K ∈ (range b.length).powerset,
      mergerRate Λ b.length K.card / totalMergerRate Λ b.length * g (mergeSet b K) := by
  rw [jumpStep, ite_eq_right h]

/-- **The block-counting projection.** When `λ_b ≠ 0`, on a statistic of the number of blocks
alone, the jump chain moves from `b` to `b + 1 - k` blocks with probability
`(b.choose k) λ_{b,k} / λ_b`: the jump chain of the block-counting process
`LambdaCoalescent.blockCountingGenerator`. -/
theorem jumpStep_comp_length (h : ℕ → ℝ) {b : List ℕ}
    (hb : totalMergerRate Λ b.length ≠ 0) :
    jumpStep Λ (fun s => h s.length) b = ∑ k ∈ Icc 2 b.length,
      (b.length.choose k : ℝ) * mergerRate Λ b.length k / totalMergerRate Λ b.length *
        h (b.length + 1 - k) := by
  rw [jumpStep_of_ne_zero Λ hb]
  set F : ℕ → ℝ := fun k => mergerRate Λ b.length k / totalMergerRate Λ b.length *
    h (b.length + 1 - k) with hF
  have hK : ∀ K ∈ (range b.length).powerset,
      mergerRate Λ b.length K.card / totalMergerRate Λ b.length * h (mergeSet b K).length =
        F K.card := fun K hK => by
    rw [hF, length_mergeSet (mem_powerset.1 hK)]
  rw [sum_congr rfl hK, sum_powerset_apply_card F, card_range]
  symm
  calc _ = ∑ k ∈ range (b.length + 1), (b.length.choose k : ℝ) * mergerRate Λ b.length k /
        totalMergerRate Λ b.length * h (b.length + 1 - k) := by
        refine sum_subset (fun k hk => mem_range.2 (by have := mem_Icc.1 hk; omega))
          fun k hk hk' => ?_
        have : k < 2 := by
          simp only [mem_range, mem_Icc, not_and, not_le] at hk hk'
          omega
        simp [mergerRate_of_lt_two Λ this]
    _ = _ := sum_congr rfl fun k _ => by rw [nsmul_eq_mul, hF]; ring

/-- The transition probabilities of the jump chain sum to `1`. -/
theorem jumpStep_const (c : ℝ) (b : List ℕ) : jumpStep Λ (fun _ => c) b = c := by
  by_cases hb : totalMergerRate Λ b.length = 0
  · exact jumpStep_of_eq_zero Λ hb
  · have h := jumpStep_comp_length Λ (fun _ => c) hb
    rw [h, ← sum_mul, ← sum_div, show ∑ k ∈ Icc 2 b.length,
      (b.length.choose k : ℝ) * mergerRate Λ b.length k = totalMergerRate Λ b.length from rfl,
      div_self hb, one_mul]

theorem iterate_jumpStep_of_eq_zero (g : List ℕ → ℝ) {b : List ℕ}
    (h : totalMergerRate Λ b.length = 0) (j : ℕ) : (jumpStep Λ)^[j] g b = g b := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', jumpStep_of_eq_zero Λ h, ih]

/-- For `Λ ≠ 0`, a statistic vanishing on absorbed states (fewer than two blocks) has
expectation `0` after `b.length` jumps from `b`: each jump removes at least one block. -/
theorem iterate_jumpStep_eq_zero (hΛ : Λ ≠ 0) {g : List ℕ → ℝ}
    (hg : ∀ s : List ℕ, s.length < 2 → g s = 0) :
    ∀ (j : ℕ) (b : List ℕ), b.length ≤ j → (jumpStep Λ)^[j] g b = 0 := by
  intro j
  induction j with
  | zero => intro b hb; exact hg b (by omega)
  | succ j ih =>
    intro b hb
    rcases lt_or_ge b.length 2 with h2 | h2
    · rw [iterate_jumpStep_of_eq_zero Λ g (totalMergerRate_of_lt_two Λ h2), hg b h2]
    · rw [Function.iterate_succ_apply', jumpStep_of_ne_zero Λ (totalMergerRate_pos Λ hΛ h2).ne']
      refine sum_eq_zero fun K hK => ?_
      by_cases hK2 : 2 ≤ K.card
      · rw [ih _ (by rw [length_mergeSet (mem_powerset.1 hK)]; omega), mul_zero]
      · rw [mergerRate_of_lt_two Λ (by omega), zero_div, zero_mul]

/-! ### The expected branch lengths -/

theorem holdingCount_of_lt_two (i : ℕ) {s : List ℕ} (hs : s.length < 2) :
    holdingCount Λ i s = 0 := by
  rw [holdingCount, totalMergerRate_of_lt_two Λ hs, div_zero]

/-- With fewer than two blocks there is no branch left. -/
theorem expectedLength_of_length_lt_two (i : ℕ) {b : List ℕ} (hb : b.length < 2) :
    expectedLength Λ i b = 0 := by
  refine sum_eq_zero fun j _ => ?_
  rw [iterate_jumpStep_of_eq_zero Λ _ (totalMergerRate_of_lt_two Λ hb),
    holdingCount_of_lt_two Λ i hb]

/-- For `Λ ≠ 0`, `expectedLength` is the whole occupation sum: jumps from the `b.length`-th on
add nothing. This holds for every list of naturals; the branch-length reading needs positive
block sizes. -/
theorem expectedLength_eq_sum (hΛ : Λ ≠ 0) (i : ℕ) {b : List ℕ} {N : ℕ} (hN : b.length ≤ N) :
    expectedLength Λ i b = ∑ j ∈ range N, (jumpStep Λ)^[j] (holdingCount Λ i) b := by
  rw [expectedLength, ← sum_range_add_sum_Ico _ hN,
    sum_eq_zero (s := Ico _ _) fun j hj => iterate_jumpStep_eq_zero Λ hΛ
      (fun s hs => holdingCount_of_lt_two Λ i hs) j b (mem_Ico.1 hj).1, add_zero]

/-- **First-step decomposition of the expected branch lengths**: for `Λ ≠ 0`, while `b` has at
least two blocks, the expected length of branches subtending `i` copies is the length
accumulated in `b`, `#{blocks of size i} / λ_b`, plus the average over the first merger `K`
(probability `λ_{b,|K|} / λ_b`) of the expected length after it. This follows from the
occupation-sum definition; its block-count counterpart is the first-jump recursion (8) of
Birkner, Blath & Eldon (2013). The identity holds for every list of at least two naturals,
including zero entries, and every `i`; the branch-length reading needs positive block sizes. -/
theorem expectedLength_eq (hΛ : Λ ≠ 0) (i : ℕ) {b : List ℕ} (hb : 2 ≤ b.length) :
    expectedLength Λ i b = (b.count i : ℝ) / totalMergerRate Λ b.length +
      ∑ K ∈ (range b.length).powerset, mergerRate Λ b.length K.card /
        totalMergerRate Λ b.length * expectedLength Λ i (mergeSet b K) := by
  obtain ⟨m, hm⟩ : ∃ m, b.length = m + 1 := ⟨b.length - 1, by omega⟩
  have hne := (totalMergerRate_pos Λ hΛ hb).ne'
  rw [expectedLength]
  conv_lhs => rw [show range b.length = range (m + 1) by rw [hm]]
  rw [sum_range_succ', Function.iterate_zero_apply, add_comm]
  congr 1
  simp_rw [Function.iterate_succ_apply', jumpStep_of_ne_zero Λ hne]
  rw [sum_comm]
  refine sum_congr rfl fun K hK => ?_
  rw [← mul_sum]
  by_cases hK2 : 2 ≤ K.card
  · rw [expectedLength_eq_sum Λ hΛ i (b := mergeSet b K) (N := m)
      (by rw [length_mergeSet (mem_powerset.1 hK)]; omega)]
  · rw [mergerRate_of_lt_two Λ (by omega), zero_div, zero_mul, zero_mul]

/-! ### Kingman's coalescent: `Λ = δ₀` -/

private lemma card_blockPairs_eq_zero {L : ℕ} (hL : L < 2) : (blockPairs L).card = 0 := by
  rw [card_eq_zero, blockPairs, filter_eq_empty_iff]
  intro p hp
  simp only [mem_product, mem_range] at hp
  omega

private lemma joinStep_of_length_lt_two (g : List ℕ → ℝ) {b : List ℕ} (hb : b.length < 2) :
    joinStep g b = g [] := by
  rw [joinStep, ite_eq_left (card_blockPairs_eq_zero hb)]

private lemma sum_powersetCard_two (L : ℕ) (G : Finset ℕ → ℝ) :
    ∑ K ∈ powersetCard 2 (range L), G K = ∑ p ∈ blockPairs L, G {p.1, p.2} := by
  symm
  refine sum_bij (fun p _ => {p.1, p.2}) (fun p hp => ?_) (fun p hp q hq hpq => ?_)
    (fun K hK => ?_) (fun p _ => rfl)
  · simp only [blockPairs, mem_filter, mem_product, mem_range] at hp
    rw [mem_powersetCard, card_pair hp.2.ne]
    refine ⟨fun x hx => ?_, rfl⟩
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]; omega
  · simp only [blockPairs, mem_filter, mem_product, mem_range] at hp hq
    have h1 : p.1 ∈ ({q.1, q.2} : Finset ℕ) := hpq ▸ mem_insert_self _ _
    have h2 : p.2 ∈ ({q.1, q.2} : Finset ℕ) := hpq ▸ mem_insert_of_mem (mem_singleton_self _)
    have h3 : q.1 ∈ ({p.1, p.2} : Finset ℕ) := hpq ▸ mem_insert_self _ _
    simp only [mem_insert, mem_singleton] at h1 h2 h3
    exact Prod.ext (by omega) (by omega)
  · rw [mem_powersetCard] at hK
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hK.2
    have hx : x < L := mem_range.1 (hK.1 (mem_insert_self _ _))
    have hy : y < L := mem_range.1 (hK.1 (mem_insert_of_mem (mem_singleton_self _)))
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨(x, y), by simp [blockPairs, hx, hy, h], rfl⟩
    · exact ⟨(y, x), by simp [blockPairs, hx, hy, h], pair_comm _ _⟩

private lemma card_blockPairs (L : ℕ) : ((blockPairs L).card : ℝ) = (L.choose 2 : ℝ) := by
  have h := sum_powersetCard_two L (fun _ => 1)
  simp only [sum_const, card_powersetCard, card_range, nsmul_eq_mul, mul_one] at h
  exact h.symm

private lemma jumpStep_dirac_zero {g : List ℕ → ℝ}
    (hg : ∀ s : List ℕ, s.length < 2 → g s = g []) :
    jumpStep (Measure.dirac 0) g = joinStep g := by
  funext b
  rcases lt_or_ge b.length 2 with hb | hb
  · rw [jumpStep_of_eq_zero _ (totalMergerRate_of_lt_two _ hb), joinStep_of_length_lt_two g hb,
      hg b hb]
  · have hc : (b.length.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hb).ne'
    have hne : totalMergerRate (Measure.dirac 0 : Measure I) b.length ≠ 0 := by
      rw [totalMergerRate_dirac_zero]; exact hc
    have hcard : (blockPairs b.length).card ≠ 0 := by
      intro h; apply hc; rw [← card_blockPairs, h, Nat.cast_zero]
    rw [jumpStep_of_ne_zero _ hne, joinStep, ite_eq_right hcard, totalMergerRate_dirac_zero]
    simp_rw [mergerRate_dirac_zero]
    have hterm : ∀ K ∈ (range b.length).powerset,
        (if K.card = 2 ∧ 2 ≤ b.length then (1 : ℝ) else 0) / (b.length.choose 2 : ℝ) *
          g (mergeSet b K) =
        if K.card = 2 then g (mergeSet b K) / (b.length.choose 2 : ℝ) else 0 := by
      intro K _
      by_cases h : K.card = 2
      · simp [h, hb, div_eq_mul_inv, mul_comm]
      · simp [h]
    rw [sum_congr rfl hterm, ← sum_filter, ← powersetCard_eq_filter, sum_powersetCard_two,
      ← sum_div, card_blockPairs]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    simp only [blockPairs, mem_filter] at hp
    rw [mergeSet_pair b hp.2]

private lemma iterate_jumpStep_dirac_zero {f : List ℕ → ℝ}
    (hf : ∀ s : List ℕ, s.length < 2 → f s = f []) (j : ℕ) :
    (jumpStep (Measure.dirac 0))^[j] f = joinStep^[j] f := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    apply jumpStep_dirac_zero
    rcases j with _ | j
    · exact hf
    · intro s hs
      rw [Function.iterate_succ_apply', joinStep_of_length_lt_two _ hs,
        joinStep_of_length_lt_two _ (by simp)]

private lemma length_mergeBlocks {b : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < b.length) :
    (mergeBlocks b i j).length = b.length - 1 := by
  simp only [mergeBlocks, List.length_append, List.length_singleton, List.length_eraseIdx]
  split_ifs <;> omega

private lemma iterate_joinStep_mul_length (c : List ℕ → ℝ) (h : ℕ → ℝ) :
    ∀ (j : ℕ) (b : List ℕ), j < b.length →
      joinStep^[j] (fun s => c s * h s.length) b = h (b.length - j) * joinStep^[j] c b := by
  intro j
  induction j with
  | zero => intro b _; simp [mul_comm]
  | succ j ih =>
    intro b hb
    have hne : (blockPairs b.length).card ≠ 0 := by
      rw [Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
      exact ⟨(0, 1), by simp [blockPairs]; omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', joinStep, joinStep,
      ite_eq_right hne, ite_eq_right hne, mul_div_assoc', mul_sum]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    simp only [blockPairs, mem_filter, mem_product, mem_range] at hp
    rw [ih _ (by rw [length_mergeBlocks hp.2 hp.1.2]; omega), length_mergeBlocks hp.2 hp.1.2,
      show b.length - 1 - j = b.length - (j + 1) by omega]

/-- **Kingman's coalescent** (`Λ = δ₀`): the expected length of branches subtending `i` of `n`
copies is `2 / i` for `1 ≤ i < n` (Fu 1995), recovered from `SiteFrequencySpectrum`'s
random-joining law. -/
theorem expectedLength_dirac_zero {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    expectedLength (Measure.dirac 0) i (List.replicate n 1) = 2 / i := by
  have hcls : ∀ s : List ℕ, s.length < 2 →
      holdingCount (Measure.dirac 0) i s = holdingCount (Measure.dirac 0) i [] := by
    intro s hs
    rw [holdingCount_of_lt_two _ i hs, holdingCount_of_lt_two _ i (by simp)]
  have hf : holdingCount (Measure.dirac 0) i =
      fun s => (s.count i : ℝ) * (fun m : ℕ => ((m.choose 2 : ℕ) : ℝ)⁻¹) s.length := by
    funext s; rw [holdingCount, totalMergerRate_dirac_zero, div_eq_mul_inv]
  rw [expectedLength, List.length_replicate]
  simp_rw [iterate_jumpStep_dirac_zero hcls]
  rw [hf, sum_congr rfl fun j hj => iterate_joinStep_mul_length (fun s => (s.count i : ℝ))
    (fun m : ℕ => ((m.choose 2 : ℕ) : ℝ)⁻¹) j _
    (by rw [List.length_replicate]; exact mem_range.1 hj)]
  simp only [List.length_replicate]
  have hR : ∀ k ∈ Icc 2 n, (k : ℝ) * ((n - i - 1).choose (k - 2) : ℝ) /
      ((n - 1).choose (k - 1) : ℝ) * ((k.choose 2 : ℕ) : ℝ)⁻¹ =
      joinStep^[n - k] (fun b => (b.count i : ℝ)) (List.replicate n 1) *
        ((k.choose 2 : ℕ) : ℝ)⁻¹ := fun k hk => by
    rw [joinStep_iterate_count (mem_Icc.1 hk).1 (mem_Icc.1 hk).2 hi hin]
  rw [← sum_blockCount_mul_inv_choose_two hi hin, sum_congr rfl hR]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ, show m + 1 - m = 1 by omega,
    show ((Nat.choose 1 2 : ℕ) : ℝ)⁻¹ = 0 by simp, zero_mul, add_zero]
  symm
  refine sum_nbij' (fun k => m + 1 - k) (fun j => m + 1 - j) ?_ ?_ ?_ ?_ ?_
  · intro k hk; rw [mem_Icc] at hk; rw [mem_range]; omega
  · intro j hj; rw [mem_range] at hj; rw [mem_Icc]; omega
  · intro k hk; rw [mem_Icc] at hk; omega
  · intro j hj; rw [mem_range] at hj; omega
  · intro k hk; rw [mem_Icc] at hk
    rw [show m + 1 - (m + 1 - k) = k by omega, mul_comm]

/-- **Fu's expected site frequency spectrum** `E ξ_i = θ / i` for Kingman's coalescent, for
`1 ≤ i < n` and every real `θ`; it is an expected number of sites only for `θ ≥ 0`. -/
theorem expectedSFS_dirac_zero (θ : ℝ) {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    expectedSFS (Measure.dirac 0) θ n i = θ / i := by
  rw [expectedSFS, expectedLength_dirac_zero hi hin]
  ring

/-! ### The star coalescent: `Λ = δ₁` -/

/-- With `Λ = δ₁` only total mergers happen: `λ_{b,k} = 0` for `k < b`. -/
theorem mergerRate_dirac_one {b k : ℕ} (hkb : k < b) :
    mergerRate (Measure.dirac 1) b k = 0 := by
  unfold mergerRate unitIntervalMoment
  split_ifs
  · rw [integral_dirac]; simp [show b - k ≠ 0 by omega]
  · rfl

/-- With `Λ = δ₁`, all `b ≥ 2` blocks merge at rate `1`. -/
theorem totalMergerRate_dirac_one {b : ℕ} (hb : 2 ≤ b) :
    totalMergerRate (Measure.dirac 1) b = 1 := by
  rw [totalMergerRate, sum_eq_single_of_mem b (mem_Icc.2 ⟨hb, le_rfl⟩) fun k hk hkb => by
    rw [mergerRate_dirac_one (lt_of_le_of_ne (mem_Icc.1 hk).2 hkb), mul_zero]]
  rw [Nat.choose_self, mergerRate_of_le _ hb le_rfl, integral_dirac]
  simp

/-- **The star coalescent** (`Λ = δ₁`): for `n ≥ 2`, all `n` lineages merge at once, after an
exponential time of mean `1`, so every branch subtends one copy: `E L_1 = n` and `E L_i = 0` for
`i ≠ 1`. -/
theorem expectedLength_dirac_one {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    expectedLength (Measure.dirac 1) i (List.replicate n 1) = if i = 1 then (n : ℝ) else 0 := by
  have hlam : totalMergerRate (Measure.dirac 1 : Measure I) (List.replicate n 1).length = 1 := by
    rw [List.length_replicate, totalMergerRate_dirac_one hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [expectedLength, List.length_replicate, sum_range_succ', sum_eq_zero, zero_add]
  · rw [Function.iterate_zero_apply, holdingCount, hlam, div_one, List.count_replicate]
    by_cases h : i = 1
    · subst h; simp
    · simp [Ne.symm h, h]
  · intro j _
    rw [Function.iterate_succ_apply', jumpStep_of_ne_zero _ (by rw [hlam]; exact one_ne_zero)]
    refine sum_eq_zero fun K hK => ?_
    have hKsub := mem_powerset.1 hK
    have hcard := card_le_card hKsub
    rw [card_range, List.length_replicate] at hcard
    rcases hcard.lt_or_eq with hlt | heq
    · rw [List.length_replicate, mergerRate_dirac_one hlt, zero_div, zero_mul]
    · have hlen : (mergeSet (List.replicate (m + 1) 1) K).length < 2 := by
        rw [length_mergeSet hKsub, List.length_replicate, heq]; omega
      rw [iterate_jumpStep_of_eq_zero _ _ (totalMergerRate_of_lt_two _ hlen),
        holdingCount_of_lt_two _ i hlen, mul_zero]

/-- For the star coalescent and `n ≥ 2`, `E ξ_1 = n θ / 2` and `E ξ_i = 0` for `i ≠ 1`, for every
real `θ`; these are expected numbers of sites only for `θ ≥ 0`. -/
theorem expectedSFS_dirac_one (θ : ℝ) {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    expectedSFS (Measure.dirac 1) θ n i = if i = 1 then θ / 2 * n else 0 := by
  rw [expectedSFS, expectedLength_dirac_one hn]
  split_ifs <;> simp

/-! ### Three sampled copies, any `Λ` -/

private lemma expectedLength_one_two (hΛ : Λ ≠ 0) (i : ℕ) :
    expectedLength Λ i [1, 2] = (([1, 2] : List ℕ).count i : ℝ) / Λ.real Set.univ := by
  have h2 : totalMergerRate Λ 2 = Λ.real Set.univ := by
    simp [totalMergerRate, mergerRate_two_two]
  rw [expectedLength_eq Λ hΛ i (by simp)]
  simp only [List.length_cons, List.length_nil, h2]
  rw [sum_eq_zero, add_zero]
  intro K hK
  rcases lt_or_ge K.card 2 with hK2 | hK2
  · rw [mergerRate_of_lt_two Λ hK2, zero_div, zero_mul]
  · rw [expectedLength_of_length_lt_two Λ i (by
      rw [length_mergeSet (mem_powerset.1 hK)]; simp; omega), mul_zero]

/-- The first-step decomposition of `E L_i` for a sample of three, for any `Λ ≠ 0`. -/
private lemma expectedLength_three (hΛ : Λ ≠ 0) (i : ℕ) :
    expectedLength Λ i [1, 1, 1] = (([1, 1, 1] : List ℕ).count i : ℝ) / totalMergerRate Λ 3 +
      3 * (mergerRate Λ 3 2 / totalMergerRate Λ 3) *
        ((([1, 2] : List ℕ).count i : ℝ) / Λ.real Set.univ) := by
  rw [expectedLength_eq Λ hΛ i (by simp)]
  simp only [List.length_cons, List.length_nil]
  congr 1
  rw [show (range 3).powerset = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by
      decide, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  have h12 : ∀ K : Finset ℕ, mergeSet [1, 1, 1] K = [1, 2] →
      expectedLength Λ i (mergeSet [1, 1, 1] K) = expectedLength Λ i [1, 2] :=
    fun K h => by rw [h]
  have hm01 : mergeSet [1, 1, 1] {0, 1} = [1, 2] := by decide
  have hm20 : mergeSet [1, 1, 1] {0, 2} = [1, 2] := by decide
  have hm21 : mergeSet [1, 1, 1] {1, 2} = [1, 2] := by decide
  have hc01 : ({0, 1} : Finset ℕ).card = 2 := by decide
  have hc20 : ({0, 2} : Finset ℕ).card = 2 := by decide
  have hc21 : ({1, 2} : Finset ℕ).card = 2 := by decide
  have hc201 : ({0, 1, 2} : Finset ℕ).card = 3 := by decide
  have hlen : (mergeSet [1, 1, 1] {0, 1, 2}).length < 2 := by decide
  rw [hm01, hm20, hm21, hc01, hc20, hc21, hc201, expectedLength_of_length_lt_two Λ i hlen,
    expectedLength_one_two Λ hΛ]
  simp only [card_empty, card_singleton, mergerRate_of_lt_two Λ (show 0 < 2 by norm_num),
    mergerRate_of_lt_two Λ (show 1 < 2 by norm_num), zero_div, zero_mul, mul_zero]
  ring

/-- For a sample of three and any `Λ ≠ 0`, the expected length of singleton branches is
`E L_1 = 3 / λ_3 + 3 λ_{3,2} / (λ_3 λ_2)`, where `λ_2 = Λ [0, 1]`. -/
theorem expectedLength_three_one (hΛ : Λ ≠ 0) :
    expectedLength Λ 1 [1, 1, 1] = 3 / totalMergerRate Λ 3 +
      3 * mergerRate Λ 3 2 / (totalMergerRate Λ 3 * Λ.real Set.univ) := by
  rw [expectedLength_three Λ hΛ]
  simp only [List.count_cons, List.count_nil]
  norm_num
  ring

/-- For a sample of three and any `Λ ≠ 0`, the expected length of doubleton branches is
`E L_2 = 3 λ_{3,2} / (λ_3 λ_2)`: a doubleton exists only after a binary merger. -/
theorem expectedLength_three_two (hΛ : Λ ≠ 0) :
    expectedLength Λ 2 [1, 1, 1] =
      3 * mergerRate Λ 3 2 / (totalMergerRate Λ 3 * Λ.real Set.univ) := by
  rw [expectedLength_three Λ hΛ]
  simp only [List.count_cons, List.count_nil]
  norm_num
  ring

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaSFS
