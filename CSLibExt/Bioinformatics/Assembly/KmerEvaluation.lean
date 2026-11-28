/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.DeBruijn
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Multiset.Bind

/-!
# k-mer consensus quality value and completeness

Merqury (Rhie, Walenz, Koren and Phillippy 2020) evaluates a genome assembly without a reference
genome by comparing its `k`-mers with those of high-accuracy reads of the same individual.

* **Consensus quality.** Let `𝒜` be the multiset of `k`-mers of the assembly, one for each window
  of `k` consecutive letters of one of its sequences, `K_total = |𝒜|`, `K_shared` the number of
  them, counted with multiplicity, that occur among the read `k`-mers, and
  `K_asm = K_total - K_shared` the number found only in the assembly. If every correct assembly
  `k`-mer occurs in the reads and errors occur independently at each base with probability `E`,
  a `k`-mer is error-free with probability `(1 - E) ^ k`; so the per-base accuracy is estimated
  by `P = (K_shared / K_total) ^ (1 / k)`, the error rate by `E = 1 - P`, and the consensus
  quality value on the phred scale by `QV = -10 log₁₀ E`, with `QV = +∞` when `E = 0`.
* **Completeness.** A read `k`-mer is reliable when its multiplicity in the reads is at least
  `x*`, the first multiplicity at which the `k`-mer count histogram has positive slope. The
  `k`-mer completeness is the fraction of the distinct reliable read `k`-mers that occur in the
  assembly.

## Main definitions

* `kmerMultiset k S`: the multiset of `k`-mers of a collection `S` of sequences, such as the
  sequences of an assembly or a read set; `(kmerMultiset k asm).card` is `K_total`.
* `sharedCount`, `asmOnlyCount`: `K_shared` and `K_asm`.
* `accuracy`, `errorRate`, `qualityValue`: `P`, `E` and `QV`, the last in `EReal`.
* `kmerHistogram`: the number of distinct read `k`-mers of each multiplicity.
* `HasReliableThreshold`, `reliableThreshold`: the threshold `x*`, and the assumption that it
  exists.
* `reliableKmers`, `completeness`: the reliable read `k`-mers and the `k`-mer completeness.

## Main results

* `card_kmerMultiset`: `K_total` is the sum over the sequences `s` of `|s| + 1 - k`.
* `sharedCount_add_asmOnlyCount`: `K_shared + K_asm = K_total`.
* `errorRate_eq`: the second form `E = 1 - (1 - K_asm / K_total) ^ (1 / k)`, for `K_total ≥ 1`.
* `errorRate_mem_Icc`, `qualityValue_nonneg`: `0 ≤ E ≤ 1` and `0 ≤ QV`.
* `qualityValue_eq_top_iff`: for `k ≥ 1` and `K_total ≥ 1`, `QV = +∞` exactly when every assembly
  `k`-mer occurs among the read `k`-mers, that is, when `K_asm = 0` (`asmOnlyCount_eq_zero_iff`).
* `qualityValue_eq_coe_iff`: `QV = q` exactly when `E = 10 ^ (-q / 10)`; so QV `30` is accuracy
  `99.9%` and QV `40` is accuracy `99.99%` (`qualityValue_eq_thirty_iff`,
  `qualityValue_eq_forty_iff`).
* `reliableThreshold_spec`, `kmerHistogram_le_of_lt_reliableThreshold`: `x*` is a multiplicity at
  which the histogram rises, and the first one.
* `reliableKmers_nonempty`, `completeness_mem_Icc`, `completeness_eq_one_iff`: some read `k`-mer
  is reliable, so the completeness is a fraction in `[0, 1]`, equal to `1` exactly when every
  reliable read `k`-mer occurs in the assembly.

## Conventions

* Sequences are lists over an alphabet `α` and `k`-mers are their windows (`DeBruijn.kmers`),
  compared as words; nothing identifies a `k`-mer with its reverse complement.
* The read `k`-mers that the consensus quality compares with form the set
  `R = (kmerMultiset k reads).toFinset`; membership in the multiset is membership in `R`.
* The definitions are total. The estimate assumes `k ≥ 1` and `K_total ≥ 1`; outside these,
  Lean's conventions `1 / 0 = 0` and `x ^ 0 = 1` give `P = 1`, `E = 0` and `QV = +∞` for
  `k = 0`, and `P = 0`, `E = 1` and `QV = 0` for an assembly with no window of length `k ≥ 1`.
* The histogram `h` (`kmerHistogram`) lives on the multiplicities `x ≥ 1` of the read `k`-mers.
  Its slope at `x ≥ 2` is the rise `h x - h (x - 1)` from the multiplicity before, so `x*` is the
  least `x ≥ 2` with `h (x - 1) < h x`, and the reliable `k`-mers are exactly those of
  multiplicity above `x* - 1`, the last multiplicity before the histogram first rises. This
  matches the cutoff of Koren et al. (2018), which Merqury follows: keep the `k`-mers whose
  coverage is above the first critical point of the histogram. The completeness is defined when
  `x*` exists (`HasReliableThreshold`), and then some read `k`-mer is reliable.

## References

* A. Rhie, B. P. Walenz, S. Koren and A. M. Phillippy, *Merqury: reference-free quality,
  completeness, and phasing assessment for genome assemblies*, Genome Biology 21 (2020), 245,
  Methods, "K-mer completeness" and "Consensus quality (QV) estimation".
* S. Koren, A. Rhie, B. P. Walenz et al., *De novo assembly of haplotype-resolved genomes with
  trio binning*, Nature Biotechnology 36 (2018), 1174–1182, Online Methods, "Haplotype k-mer
  identification".
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Assembly.KmerEvaluation

variable {α : Type*}

/-- **The `k`-mers of a collection of sequences.** The multiset of `k`-mers of the sequences in
`S`, such as the sequences of a genome assembly or a set of reads: one `k`-mer for each window of
`k` consecutive letters in a sequence of `S` (`DeBruijn.kmers`), counted with multiplicity. For an
assembly `asm`, its cardinality is `K_total`. -/
def kmerMultiset (k : ℕ) (S : Multiset (List α)) : Multiset (List α) :=
  S.bind fun s => (DeBruijn.kmers k s : Multiset (List α))

/-- `K_total` counts the windows: a sequence `s` has `|s| + 1 - k` windows of length `k`. -/
theorem card_kmerMultiset (k : ℕ) (S : Multiset (List α)) :
    (kmerMultiset k S).card = (S.map fun s => s.length + 1 - k).sum := by
  simp [kmerMultiset, Multiset.card_bind, DeBruijn.kmers, Function.comp_def]

variable [DecidableEq α]

/-- **`K_shared`.** The number of `k`-mers of the assembly `asm`, counted with multiplicity, that
occur among the `k`-mers of the reads `reads`. -/
def sharedCount (k : ℕ) (asm reads : Multiset (List α)) : ℕ :=
  ((kmerMultiset k asm).filter (· ∈ kmerMultiset k reads)).card

/-- **`K_asm`.** The number of `k`-mers of the assembly `asm`, counted with multiplicity, that do
not occur among the `k`-mers of the reads `reads`: those found only in the assembly. It is
`K_total - K_shared` (`asmOnlyCount_eq_sub`). -/
def asmOnlyCount (k : ℕ) (asm reads : Multiset (List α)) : ℕ :=
  ((kmerMultiset k asm).filter (· ∉ kmerMultiset k reads)).card

/-- **The per-base accuracy estimate** `P = (K_shared / K_total) ^ (1 / k)` of an assembly `asm`
against reads `reads`. If the reads cover the genome, so that every correct assembly `k`-mer occurs
among the read `k`-mers, and errors occur independently at each base, a `k`-mer is error-free
with probability `P ^ k`, which the fraction `K_shared / K_total` of assembly `k`-mers found in
the reads estimates. Meant for `k ≥ 1` and `K_total ≥ 1`; with Lean's `1 / 0 = 0` and `x ^ 0 = 1`
it is `1` for `k = 0` and `0` for an assembly with no window of length `k ≥ 1`. -/
noncomputable def accuracy (k : ℕ) (asm reads : Multiset (List α)) : ℝ :=
  ((sharedCount k asm reads : ℝ) / (kmerMultiset k asm).card) ^ (1 / (k : ℝ))

/-- **The consensus error rate** `E = 1 - P = 1 - (K_shared / K_total) ^ (1 / k)` of an assembly
`asm` against reads `reads`, where `P` is `accuracy`; equivalently
`E = 1 - (1 - K_asm / K_total) ^ (1 / k)` when `K_total ≥ 1` (`errorRate_eq`). -/
noncomputable def errorRate (k : ℕ) (asm reads : Multiset (List α)) : ℝ :=
  1 - accuracy k asm reads

/-- **The consensus quality value** of an assembly `asm` against reads `reads`: the error rate
`E` (`errorRate`) on the phred scale, `QV = -10 log₁₀ E`, and `QV = +∞` when `E = 0`, which for
`k ≥ 1` and `K_total ≥ 1` happens exactly when every assembly `k`-mer occurs among the read
`k`-mers (`qualityValue_eq_top_iff`). -/
noncomputable def qualityValue (k : ℕ) (asm reads : Multiset (List α)) : EReal :=
  if errorRate k asm reads = 0 then ⊤
  else ((-10 * Real.logb 10 (errorRate k asm reads) : ℝ) : EReal)

/-- **The `k`-mer count histogram** of the reads `reads`: at multiplicity `x`, the number of
distinct read `k`-mers that occur exactly `x` times among the `k`-mers of the reads. It vanishes
at `x = 0`. -/
def kmerHistogram (k : ℕ) (reads : Multiset (List α)) (x : ℕ) : ℕ :=
  ((kmerMultiset k reads).toFinset.filter fun w => (kmerMultiset k reads).count w = x).card

/-- **The reliable-`k`-mer threshold exists**: the `k`-mer count histogram `h` of the reads has
positive slope somewhere, that is, `h (x - 1) < h x` for some multiplicity `x ≥ 2`. The slope at
`x` is the rise from the multiplicity before; the histogram starts at multiplicity `1`. -/
def HasReliableThreshold (k : ℕ) (reads : Multiset (List α)) : Prop :=
  ∃ x, 2 ≤ x ∧ kmerHistogram k reads (x - 1) < kmerHistogram k reads x

/-- **The reliable-`k`-mer threshold** `x*`: the first multiplicity at which the `k`-mer count
histogram `h` of the reads has positive slope, that is, the least `x ≥ 2` with
`h (x - 1) < h x`, which `h` is assumed to have (`HasReliableThreshold`). The reliable read
`k`-mers, those of multiplicity at least `x*`, are those above `x* - 1`, the last multiplicity
before the histogram first rises, between the error peak and the genomic peak. -/
def reliableThreshold (k : ℕ) (reads : Multiset (List α)) (h : HasReliableThreshold k reads) :
    ℕ :=
  Nat.find h

/-- **The reliable read `k`-mers** at threshold `t`: the distinct `k`-mers of the reads `reads`
whose multiplicity among the read `k`-mers is at least `t`. -/
def reliableKmers (k : ℕ) (reads : Multiset (List α)) (t : ℕ) : Finset (List α) :=
  (kmerMultiset k reads).toFinset.filter fun w => t ≤ (kmerMultiset k reads).count w

/-- **The `k`-mer completeness** of an assembly `asm` against reads `reads`: the fraction of the
distinct reliable read `k`-mers, those whose multiplicity in the reads is at least the threshold
`x*` (`reliableThreshold`), that occur in the assembly. It is defined when `x*` exists
(`HasReliableThreshold`); then some read `k`-mer is reliable (`reliableKmers_nonempty`). -/
noncomputable def completeness (k : ℕ) (asm reads : Multiset (List α))
    (h : HasReliableThreshold k reads) : ℝ :=
  (((reliableKmers k reads (reliableThreshold k reads h)).filter
      (· ∈ kmerMultiset k asm)).card : ℝ) /
    (reliableKmers k reads (reliableThreshold k reads h)).card

/-! ### Counts -/

/-- `K_shared + K_asm = K_total`. -/
theorem sharedCount_add_asmOnlyCount (k : ℕ) (asm reads : Multiset (List α)) :
    sharedCount k asm reads + asmOnlyCount k asm reads = (kmerMultiset k asm).card := by
  rw [sharedCount, asmOnlyCount, ← Multiset.card_add, Multiset.filter_add_not]

theorem sharedCount_le_card (k : ℕ) (asm reads : Multiset (List α)) :
    sharedCount k asm reads ≤ (kmerMultiset k asm).card :=
  Multiset.card_le_card (Multiset.filter_le _ _)

/-- `K_asm = K_total - K_shared`. -/
theorem asmOnlyCount_eq_sub (k : ℕ) (asm reads : Multiset (List α)) :
    asmOnlyCount k asm reads = (kmerMultiset k asm).card - sharedCount k asm reads := by
  rw [← sharedCount_add_asmOnlyCount k asm reads, Nat.add_sub_cancel_left]

/-- `K_asm = 0` exactly when every assembly `k`-mer occurs among the read `k`-mers. -/
theorem asmOnlyCount_eq_zero_iff (k : ℕ) (asm reads : Multiset (List α)) :
    asmOnlyCount k asm reads = 0 ↔ ∀ w ∈ kmerMultiset k asm, w ∈ kmerMultiset k reads := by
  simp [asmOnlyCount, Multiset.filter_eq_nil]

/-! ### Accuracy, error rate and quality value -/

private theorem ratio_mem_Icc (k : ℕ) (asm reads : Multiset (List α)) :
    0 ≤ (sharedCount k asm reads : ℝ) / (kmerMultiset k asm).card ∧
      (sharedCount k asm reads : ℝ) / (kmerMultiset k asm).card ≤ 1 :=
  ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast sharedCount_le_card k asm reads)
    (by positivity)⟩

theorem accuracy_mem_Icc (k : ℕ) (asm reads : Multiset (List α)) :
    accuracy k asm reads ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h₀, h₁⟩ := ratio_mem_Icc k asm reads
  exact ⟨Real.rpow_nonneg h₀ _, Real.rpow_le_one h₀ h₁ (by positivity)⟩

/-- The error rate lies in `[0, 1]`. -/
theorem errorRate_mem_Icc (k : ℕ) (asm reads : Multiset (List α)) :
    errorRate k asm reads ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h₀, h₁⟩ := accuracy_mem_Icc k asm reads
  exact ⟨by rw [errorRate]; linarith, by rw [errorRate]; linarith⟩

theorem accuracy_eq_one_sub_errorRate (k : ℕ) (asm reads : Multiset (List α)) :
    accuracy k asm reads = 1 - errorRate k asm reads := by
  rw [errorRate, sub_sub_cancel]

/-- **The second form of the error rate**: `E = 1 - (1 - K_asm / K_total) ^ (1 / k)` when
`K_total ≥ 1`. -/
theorem errorRate_eq (k : ℕ) (asm reads : Multiset (List α))
    (htotal : 0 < (kmerMultiset k asm).card) :
    errorRate k asm reads =
      1 - (1 - (asmOnlyCount k asm reads : ℝ) / (kmerMultiset k asm).card) ^ (1 / (k : ℝ)) := by
  have hsum : (sharedCount k asm reads : ℝ) + asmOnlyCount k asm reads =
      (kmerMultiset k asm).card := by
    exact_mod_cast sharedCount_add_asmOnlyCount k asm reads
  have hne : ((kmerMultiset k asm).card : ℝ) ≠ 0 := by exact_mod_cast htotal.ne'
  rw [errorRate, accuracy]
  congr 2
  field_simp
  linarith

/-- For `k ≥ 1` and `K_total ≥ 1`, the error rate vanishes exactly when `K_asm = 0`. -/
theorem errorRate_eq_zero_iff (k : ℕ) (asm reads : Multiset (List α)) (hk : 1 ≤ k)
    (htotal : 0 < (kmerMultiset k asm).card) :
    errorRate k asm reads = 0 ↔ asmOnlyCount k asm reads = 0 := by
  obtain ⟨h₀, -⟩ := ratio_mem_Icc k asm reads
  have hne : ((kmerMultiset k asm).card : ℝ) ≠ 0 := by exact_mod_cast htotal.ne'
  have hexp : (1 / (k : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  rw [errorRate, sub_eq_zero, eq_comm, accuracy, asmOnlyCount_eq_sub, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    have hr : (sharedCount k asm reads : ℝ) / (kmerMultiset k asm).card = 1 :=
      Real.rpow_left_injOn hexp h₀ zero_le_one (show _ ^ _ = (1 : ℝ) ^ _ by rw [h, Real.one_rpow])
    rw [div_eq_one_iff_eq hne] at hr
    exact_mod_cast hr.ge
  · intro h
    have hr : (sharedCount k asm reads : ℝ) = (kmerMultiset k asm).card := by
      exact_mod_cast le_antisymm (sharedCount_le_card k asm reads) h
    rw [hr, div_self hne, Real.one_rpow]

/-- **`QV = +∞` exactly when every assembly `k`-mer occurs among the read `k`-mers**, for `k ≥ 1`
and `K_total ≥ 1`; that is, when `K_asm = 0` (`asmOnlyCount_eq_zero_iff`). -/
theorem qualityValue_eq_top_iff (k : ℕ) (asm reads : Multiset (List α)) (hk : 1 ≤ k)
    (htotal : 0 < (kmerMultiset k asm).card) :
    qualityValue k asm reads = ⊤ ↔ ∀ w ∈ kmerMultiset k asm, w ∈ kmerMultiset k reads := by
  rw [← asmOnlyCount_eq_zero_iff, ← errorRate_eq_zero_iff k asm reads hk htotal, qualityValue]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    exact EReal.coe_ne_top _

/-- The quality value is nonnegative. -/
theorem qualityValue_nonneg (k : ℕ) (asm reads : Multiset (List α)) :
    0 ≤ qualityValue k asm reads := by
  obtain ⟨h₀, h₁⟩ := errorRate_mem_Icc k asm reads
  rw [qualityValue]
  split_ifs with h
  · exact le_top
  · rw [EReal.coe_nonneg]
    have := Real.logb_nonpos (b := 10) (by norm_num) h₀ h₁
    linarith

/-- **The phred scale**: `QV = q` exactly when `E = 10 ^ (-q / 10)`, for every real `q`. -/
theorem qualityValue_eq_coe_iff (k : ℕ) (asm reads : Multiset (List α)) (q : ℝ) :
    qualityValue k asm reads = q ↔ errorRate k asm reads = 10 ^ (-q / 10) := by
  obtain ⟨h₀, -⟩ := errorRate_mem_Icc k asm reads
  rw [qualityValue]
  split_ifs with h
  · rw [h]
    simp only [EReal.top_ne_coe, false_iff]
    exact (Real.rpow_pos_of_pos (by norm_num) _).ne
  · have hE : 0 < errorRate k asm reads := lt_of_le_of_ne h₀ (Ne.symm h)
    rw [EReal.coe_eq_coe_iff]
    constructor
    · intro h'
      have hlog : Real.logb 10 (errorRate k asm reads) = -q / 10 := by linarith
      exact ((Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hE).mp hlog).symm
    · intro h'
      have hlog : Real.logb 10 (errorRate k asm reads) = -q / 10 :=
        (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hE).mpr h'.symm
      linarith

private theorem ten_rpow_neg_mul_div_ten (n : ℕ) :
    (10 : ℝ) ^ (-(10 * (n : ℝ)) / 10) = 1 / 10 ^ n := by
  rw [show -(10 * (n : ℝ)) / 10 = -(n : ℝ) by ring, Real.rpow_neg (by norm_num),
    Real.rpow_natCast, one_div]

/-- **QV `30` is accuracy `99.9%`**: `QV = 30` exactly when `P = 999 / 1000`. -/
theorem qualityValue_eq_thirty_iff (k : ℕ) (asm reads : Multiset (List α)) :
    qualityValue k asm reads = 30 ↔ accuracy k asm reads = 999 / 1000 := by
  have h := qualityValue_eq_coe_iff k asm reads 30
  rw [show ((30 : ℝ) : EReal) = 30 from rfl, show (30 : ℝ) = 10 * ((3 : ℕ) : ℝ) by norm_num,
    ten_rpow_neg_mul_div_ten] at h
  rw [h, accuracy_eq_one_sub_errorRate]
  constructor <;> intro h' <;> norm_num at h' ⊢ <;> linarith

/-- **QV `40` is accuracy `99.99%`**: `QV = 40` exactly when `P = 9999 / 10000`. -/
theorem qualityValue_eq_forty_iff (k : ℕ) (asm reads : Multiset (List α)) :
    qualityValue k asm reads = 40 ↔ accuracy k asm reads = 9999 / 10000 := by
  have h := qualityValue_eq_coe_iff k asm reads 40
  rw [show ((40 : ℝ) : EReal) = 40 from rfl, show (40 : ℝ) = 10 * ((4 : ℕ) : ℝ) by norm_num,
    ten_rpow_neg_mul_div_ten] at h
  rw [h, accuracy_eq_one_sub_errorRate]
  constructor <;> intro h' <;> norm_num at h' ⊢ <;> linarith

/-! ### Reliable `k`-mers and completeness -/

theorem kmerHistogram_zero (k : ℕ) (reads : Multiset (List α)) : kmerHistogram k reads 0 = 0 := by
  simp [kmerHistogram, Multiset.count_eq_zero]

/-- `x*` is a multiplicity `x ≥ 2` at which the histogram has positive slope:
`h (x* - 1) < h x*`. -/
theorem reliableThreshold_spec (k : ℕ) (reads : Multiset (List α))
    (h : HasReliableThreshold k reads) :
    2 ≤ reliableThreshold k reads h ∧
      kmerHistogram k reads (reliableThreshold k reads h - 1) <
        kmerHistogram k reads (reliableThreshold k reads h) :=
  Nat.find_spec h

/-- `x*` is the first such multiplicity: the histogram does not rise at any `2 ≤ x < x*`. -/
theorem kmerHistogram_le_of_lt_reliableThreshold (k : ℕ) (reads : Multiset (List α))
    (h : HasReliableThreshold k reads) {x : ℕ} (hx : 2 ≤ x)
    (hlt : x < reliableThreshold k reads h) :
    kmerHistogram k reads x ≤ kmerHistogram k reads (x - 1) :=
  not_lt.mp fun hrise => Nat.find_min h hlt ⟨hx, hrise⟩

/-- **Some read `k`-mer is reliable**: the histogram is positive at `x*`, so some distinct read
`k`-mer has multiplicity exactly `x*`. -/
theorem reliableKmers_nonempty (k : ℕ) (reads : Multiset (List α))
    (h : HasReliableThreshold k reads) :
    (reliableKmers k reads (reliableThreshold k reads h)).Nonempty := by
  obtain ⟨-, hrise⟩ := reliableThreshold_spec k reads h
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hrise)
  rw [Finset.mem_filter] at hw
  exact ⟨w, Finset.mem_filter.mpr ⟨hw.1, hw.2.ge⟩⟩

/-- The completeness lies in `[0, 1]`. -/
theorem completeness_mem_Icc (k : ℕ) (asm reads : Multiset (List α))
    (h : HasReliableThreshold k reads) :
    completeness k asm reads h ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by rw [completeness]; positivity,
    div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)⟩

/-- The completeness is `1` exactly when every reliable read `k`-mer occurs in the assembly. -/
theorem completeness_eq_one_iff (k : ℕ) (asm reads : Multiset (List α))
    (h : HasReliableThreshold k reads) :
    completeness k asm reads h = 1 ↔
      ∀ w ∈ reliableKmers k reads (reliableThreshold k reads h), w ∈ kmerMultiset k asm := by
  have hpos := (reliableKmers_nonempty k reads h).card_pos
  rw [completeness, div_eq_one_iff_eq (by exact_mod_cast hpos.ne'), Nat.cast_inj,
    Finset.card_filter_eq_iff]

end Cslib.Bioinformatics.Assembly.KmerEvaluation
