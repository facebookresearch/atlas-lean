/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.KmerEvaluation
public meta import CSLibExt.Bioinformatics.Assembly.KmerEvaluation

/-!
# k-mer consensus quality value and completeness tests

Fixtures over the nucleotides `A, C, G, T`: the `k`-mer counts of a two-sequence assembly; the
error rate `1 / 10` and QV `10` of a `1`-mer assembly with one base in ten missing from the reads,
and QV `30` with one in a thousand; the accuracy `(1 / 4) ^ (1 / 2) = 1 / 2` of a `2`-mer assembly;
`QV = +∞` exactly when every assembly `k`-mer occurs in the reads. Over the letters `1, …, 6`: a
read set whose histogram `3, 1, 2` falls, then rises at multiplicity `3`, so that `x* = 3`, the
`k`-mer of multiplicity `2` at the minimum is not reliable, and an assembly holding one of the two
reliable `k`-mers has completeness `1 / 2`; a histogram that rises at once (`x* = 2`). Boundary
cases: a histogram that never rises (no threshold), and the documented totalized values for
`k = 0` and for an assembly with no window of length `k`.
-/

namespace Cslib.Bioinformatics.Assembly.KmerEvaluation

/-- Nucleotides, for the fixtures. -/
inductive Base
  | A | C | G | T
  deriving DecidableEq, Repr

open Base

/-! ### Counts -/

/-- Two sequences, `ACGTA` and `GT`. -/
def asm₁ : Multiset (List Base) := {[A, C, G, T, A], [G, T]}

/-- One read, `ACGG`. -/
def reads₁ : Multiset (List Base) := {[A, C, G, G]}

-- The `2`-mers of the assembly: `AC, CG, GT, TA` and `GT`; of the reads: `AC, CG, GG`.
#guard kmerMultiset 2 asm₁ = {[A, C], [C, G], [G, T], [T, A], [G, T]}
#guard (kmerMultiset 2 asm₁).card = 5
#guard sharedCount 2 asm₁ reads₁ = 2
#guard asmOnlyCount 2 asm₁ reads₁ = 3

example : (kmerMultiset 2 asm₁).card = 5 := by
  rw [card_kmerMultiset]
  decide

example : sharedCount 2 asm₁ reads₁ + asmOnlyCount 2 asm₁ reads₁ = 5 := by
  rw [sharedCount_add_asmOnlyCount]
  decide

/-! ### Quality value -/

/-- Ten bases, `AAAAAAAAAC`. -/
def asm₂ : Multiset (List Base) := {[A, A, A, A, A, A, A, A, A, C]}

/-- Reads with no `C`. -/
def reads₂ : Multiset (List Base) := {[A, G], [T, A]}

-- `1`-mers: nine of the ten assembly bases occur in the reads, so `P = 9 / 10`,
-- `E = 1 / 10` and `QV = 10`.
example : errorRate 1 asm₂ reads₂ = 1 / 10 := by
  have hs : sharedCount 1 asm₂ reads₂ = 9 := by decide
  have ht : (kmerMultiset 1 asm₂).card = 10 := by decide
  rw [errorRate, accuracy, hs, ht]
  norm_num

example : qualityValue 1 asm₂ reads₂ = 10 := by
  have hs : sharedCount 1 asm₂ reads₂ = 9 := by decide
  have ht : (kmerMultiset 1 asm₂).card = 10 := by decide
  rw [show (10 : EReal) = ((10 : ℝ) : EReal) from rfl, qualityValue_eq_coe_iff, errorRate,
    accuracy, hs, ht]
  norm_num

-- QV `30` is accuracy `99.9%`: a thousand one-base sequences, one of them `C`, against reads
-- with no `C`.
example : qualityValue 1 (Multiset.replicate 999 [A] + {[C]}) {[A]} = 30 := by
  have hs : sharedCount 1 (Multiset.replicate 999 [A] + {[C]}) {[A]} = 999 := by decide +kernel
  have ht : (kmerMultiset 1 (Multiset.replicate 999 [A] + {[C]})).card = 1000 := by
    decide +kernel
  rw [qualityValue_eq_thirty_iff, accuracy, hs, ht]
  norm_num

/-- `ACGTA`, with `2`-mers `AC, CG, GT, TA`. -/
def asm₃ : Multiset (List Base) := {[A, C, G, T, A]}

-- One of the four assembly `2`-mers occurs in the reads `AC`: `P = (1 / 4) ^ (1 / 2) = 1 / 2`.
example : accuracy 2 asm₃ {[A, C]} = 1 / 2 := by
  have hs : sharedCount 2 asm₃ {[A, C]} = 1 := by decide
  have ht : (kmerMultiset 2 asm₃).card = 4 := by decide
  rw [accuracy, hs, ht, show ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num)]
  norm_num

-- Every assembly `3`-mer (`ACG`, `CGT`) occurs in the read `ACGTT`: `QV = +∞`.
example : qualityValue 3 {[A, C, G, T]} {[A, C, G, T, T]} = ⊤ :=
  (qualityValue_eq_top_iff 3 _ _ (by decide) (by decide)).mpr (by decide)

-- With a `3`-mer missing from the reads the quality value is finite.
example : qualityValue 3 {[A, C, G, T]} {[A, C, G]} ≠ ⊤ := by
  rw [ne_eq, qualityValue_eq_top_iff 3 _ _ (by decide) (by decide)]
  decide

-- The documented totalized values: `k = 0` gives `E = 0` and `QV = +∞` ...
example : qualityValue 0 asm₂ reads₂ = ⊤ := by
  simp [qualityValue, errorRate, accuracy]

-- ... and an assembly with no window of length `k ≥ 1` gives `E = 1` and `QV = 0`.
example : (kmerMultiset 3 {[A, C]}).card = 0 := by decide

example : qualityValue 3 {[A, C]} reads₂ = 0 := by
  have ht : (kmerMultiset 3 ({[A, C]} : Multiset (List Base))).card = 0 := by decide
  simp [qualityValue, errorRate, accuracy, ht]

/-! ### Reliable `k`-mers and completeness -/

/-- One read over the letters `1, …, 6`, whose `1`-mers `1, 2, 3` occur once (errors), `4` twice
(at the minimum of the histogram) and `5, 6` three times (genomic). -/
def reads₅ : Multiset (List ℕ) :=
  {[1, 2, 3, 4, 4, 5, 5, 5, 6, 6, 6]}

-- The histogram is `3, 1, 2` at multiplicities `1, 2, 3`, and `0` at `0` and above `3`.
#guard (List.range 6).map (kmerHistogram 1 reads₅) = [0, 3, 1, 2, 0, 0]

example : kmerHistogram 1 reads₅ 0 = 0 := kmerHistogram_zero 1 reads₅

/-- The histogram of `reads₅` rises at multiplicity `3`. -/
theorem hasReliableThreshold₅ : HasReliableThreshold 1 reads₅ := ⟨3, by decide, by decide⟩

/-- The histogram of `reads₅` falls at `2` and rises at `3`, so `x* = 3`, not the minimum `2`. -/
theorem reliableThreshold₅ : reliableThreshold 1 reads₅ hasReliableThreshold₅ = 3 :=
  (Nat.find_eq_iff hasReliableThreshold₅).mpr ⟨⟨by decide, by decide⟩, by decide⟩

-- The reliable `1`-mers are `5` and `6`; `4`, of multiplicity `2`, is not.
#guard reliableKmers 1 reads₅ 3 = {[5], [6]}
example : [4] ∉ reliableKmers 1 reads₅ (reliableThreshold 1 reads₅ hasReliableThreshold₅) := by
  rw [reliableThreshold₅]
  decide

-- An assembly holding `5` (and the error `1` and the non-reliable `4`) but not `6`:
-- completeness `1 / 2`.
example : completeness 1 {[5, 4, 1]} reads₅ hasReliableThreshold₅ = 1 / 2 := by
  have hr : (reliableKmers 1 reads₅ 3).card = 2 := by decide
  have hf : ((reliableKmers 1 reads₅ 3).filter
      (· ∈ kmerMultiset 1 ({[5, 4, 1]} : Multiset (List ℕ)))).card = 1 := by decide
  rw [completeness, reliableThreshold₅, hr, hf]
  norm_num

-- An assembly holding both reliable `k`-mers is complete.
example : completeness 1 {[6, 5]} reads₅ hasReliableThreshold₅ = 1 := by
  rw [completeness_eq_one_iff, reliableThreshold₅]
  decide

-- The general facts, instantiated.
example : (reliableKmers 1 reads₅ (reliableThreshold 1 reads₅ hasReliableThreshold₅)).Nonempty :=
  reliableKmers_nonempty 1 reads₅ hasReliableThreshold₅
example : completeness 1 {[5, 4, 1]} reads₅ hasReliableThreshold₅ ∈ Set.Icc (0 : ℝ) 1 :=
  completeness_mem_Icc _ _ _ _

-- A histogram that rises at once, `1, 2` at multiplicities `1, 2`: `x* = 2`.
example : reliableThreshold 1 {[1, 2, 2, 3, 3]} ⟨2, by decide, by decide⟩ = 2 :=
  (Nat.find_eq_iff _).mpr ⟨⟨by decide, by decide⟩, by decide⟩

-- A histogram that never rises (every read `1`-mer occurs once): no threshold.
example : ¬ HasReliableThreshold 1 {[1, 2, 3]} := by
  have hone : ∀ w ∈ (kmerMultiset 1 ({[1, 2, 3]} : Multiset (List ℕ))).toFinset,
      (kmerMultiset 1 ({[1, 2, 3]} : Multiset (List ℕ))).count w = 1 := by decide
  rintro ⟨x, hx, hlt⟩
  have h0 : kmerHistogram 1 {[1, 2, 3]} x = 0 := by
    rw [kmerHistogram, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw
    rw [hone w hw]
    omega
  omega

end Cslib.Bioinformatics.Assembly.KmerEvaluation
