/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ExponentialMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FieldSimp

/-!
# Extended haplotype homozygosity

Extended haplotype homozygosity (EHH, Sabeti et al. 2002) measures how far haplotype identity
extends away from a core locus. A sample of haplotypes is a family `h : ι → ℕ → α`: `h i k` is
the allele carried by haplotype `i` at the site `k` steps away from the core, in a fixed
direction. The *window* of radius `d` of haplotype `i` is the restriction `window h d i` of
`h i` to the first `d` sites.

For a finite set `C` of haplotypes (in applications, the carriers of one core allele),
`ehh h C d` is the probability that two haplotypes drawn from `C` without replacement carry the
same window of radius `d`: the number of ordered pairs of distinct haplotypes with equal
windows, divided by `#C * (#C - 1)`.

Two further statements are about the neutral model. Under the coalescent with recombination,
and in units of `2N` generations with `ρ = 4Nr` the scaled recombination rate per site, the two
lineages of a pair carry recombination events at total rate `ρ * d` while they are distinct, so
given a pair coalescence time `T₂` the probability that no recombination falls on the pair's
genealogy within distance `d` is `exp (-(ρ * d) * T₂)`; for `T₂` exponential of rate `1` its
expectation is `(1 + ρ * d)⁻¹`. This is **not** `E[EHH(d)]`: a lineage that recombines may carry
the same alleles anyway (by recombining onto an identical haplotype, or by coalescing back), so
the quantity computed here is a lower bound for the expected EHH rather than its value.

## Main results

* `window_eq_iff`: equal windows of radius `d` means equal alleles at every site `k < d`.
* `ehh_nonneg`, `ehh_le_one`, `ehh_zero_window`: `0 ≤ EHH ≤ 1` and `EHH(0) = 1`
  (for samples of at least two haplotypes).
* `ehh_antitone`: `EHH(d)` is nonincreasing in `d`.
* `ehh_eq_sum_counts`: `EHH(d) = ∑_t c_t (c_t - 1) / (#C (#C - 1))`, the sampling-without-
  replacement homozygosity of the partition of `C` into window types.
* `ehh_eq_zero_of_card_le_one`: the junk value `0` returned outside the domain `2 ≤ #C`.
* `rehh`, `one_lt_rehh_iff`: the relative EHH of Sabeti et al.'s long-range haplotype test
  exceeds `1` exactly when the core allele has the larger EHH.
* `integral_pairNoRecomb`: `E[exp (-(ρ d) T₂)] = (1 + ρ d)⁻¹` for `T₂` exponential of rate `1`,
  with `pairNoRecomb_le_one` and `pairNoRecomb_antitone` the corresponding bound and decay.

## References

* P. C. Sabeti, D. E. Reich, J. M. Higgins, H. Z. P. Levine, D. J. Richter, S. F. Schaffner,
  S. B. Gabriel, J. V. Platko, N. J. Patterson, G. J. McDonald, H. C. Ackerman, S. J. Campbell,
  D. Altshuler, R. Cooper, D. Kwiatkowski, R. Ward and E. S. Lander, *Detecting recent positive
  selection in the human genome from haplotype structure*, Nature 419 (2002), 832–837.
* R. R. Hudson, *Gene genealogies and the coalescent process*, Oxford Surveys in Evolutionary
  Biology 7 (1990), 1–44 (coalescent with recombination; scaling `ρ = 4Nr`).
-/

open MeasureTheory Set Real Finset ProbabilityTheory

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.SelectionScan

section Sample

variable {ι α : Type*}

/-- The window of radius `d` of haplotype `i`: its alleles at the `d` sites closest to the
core, in the direction indexed by `ℕ`. -/
def window (h : ι → ℕ → α) (d : ℕ) (i : ι) : Fin d → α := fun k => h i k

/-- Two haplotypes have the same window of radius `d` exactly when they agree at every site
`k < d`. -/
theorem window_eq_iff (h : ι → ℕ → α) (d : ℕ) (i j : ι) :
    window h d i = window h d j ↔ ∀ k < d, h i k = h j k := by
  constructor
  · intro hw k hk
    exact congrFun hw ⟨k, hk⟩
  · intro hw
    funext k
    exact hw k k.isLt

variable [DecidableEq ι] [DecidableEq α]

/-- The number of ordered pairs of distinct haplotypes of `C` whose windows of radius `d`
agree. -/
def concordantPairs (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) : ℕ :=
  ((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h d p.1 = window h d p.2).card

/-- Extended haplotype homozygosity at radius `d` of the haplotype set `C`: the probability
that two distinct haplotypes drawn from `C` without replacement agree at all `d` sites nearest
the core (Sabeti et al. 2002). For `#C ≤ 1` the denominator vanishes and the junk value `0` is
returned; every statement below that needs the probabilistic reading assumes `2 ≤ #C`. -/
noncomputable def ehh (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) : ℝ :=
  (concordantPairs h C d : ℝ) / ((C.card : ℝ) * ((C.card : ℝ) - 1))

/-- Outside the domain `2 ≤ #C` the definition returns the junk value `0`. -/
theorem ehh_eq_zero_of_card_le_one (h : ι → ℕ → α) {C : Finset ι} (hC : C.card ≤ 1) (d : ℕ) :
    ehh h C d = 0 := by
  have hzero : ((C.card : ℝ)) * ((C.card : ℝ) - 1) = 0 := by
    interval_cases hc : C.card <;> norm_num
  rw [ehh, hzero, div_zero]

theorem ehh_nonneg (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) : 0 ≤ ehh h C d := by
  rcases Nat.eq_zero_or_pos C.card with hc | hc
  · simp [ehh, hc]
  · refine div_nonneg (Nat.cast_nonneg _) ?_
    have h1 : (1 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hc
    nlinarith

theorem concordantPairs_le (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) :
    concordantPairs h C d ≤ C.card * (C.card - 1) := by
  have hsub : ((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h d p.1 = window h d p.2)
      ⊆ C.offDiag := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_offDiag.mpr ⟨hp.1.1, hp.1.2, hp.2.1⟩
  calc concordantPairs h C d ≤ C.offDiag.card := Finset.card_le_card hsub
    _ = C.card * C.card - C.card := Finset.offDiag_card C
    _ = C.card * (C.card - 1) := by rw [Nat.mul_sub, mul_one]

theorem ehh_le_one (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) : ehh h C d ≤ 1 := by
  rcases le_or_gt C.card 1 with hc | hc
  · rw [ehh_eq_zero_of_card_le_one h hc]
    norm_num
  · have h2 : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hc
    have hden : (0 : ℝ) < (C.card : ℝ) * ((C.card : ℝ) - 1) := by nlinarith
    rw [ehh, div_le_one hden]
    have hle := concordantPairs_le h C d
    have h1 : 1 ≤ C.card := le_of_lt hc
    calc ((concordantPairs h C d : ℕ) : ℝ) ≤ ((C.card * (C.card - 1) : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = (C.card : ℝ) * ((C.card : ℝ) - 1) := by
          push_cast [Nat.cast_sub h1]
          ring

/-- At radius `0` every pair of haplotypes agrees, so `EHH(0) = 1`. -/
theorem ehh_zero_window (h : ι → ℕ → α) {C : Finset ι} (hC : 2 ≤ C.card) :
    ehh h C 0 = 1 := by
  have hw : ∀ i j : ι, window h 0 i = window h 0 j := fun i j => funext fun k => k.elim0
  have hfilter : ((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h 0 p.1 = window h 0 p.2)
      = C.offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3, hw _ _⟩
  have h2 : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hC
  have hden : (0 : ℝ) < (C.card : ℝ) * ((C.card : ℝ) - 1) := by nlinarith
  have h1 : C.card ≤ C.card * C.card := Nat.le_mul_of_pos_left C.card (by omega)
  rw [ehh, concordantPairs, hfilter, Finset.offDiag_card C, div_eq_one_iff_eq hden.ne']
  push_cast [Nat.cast_sub h1]
  ring

/-- EHH is nonincreasing in the radius: widening the window can only break ties. -/
theorem ehh_antitone (h : ι → ℕ → α) (C : Finset ι) {d d' : ℕ} (hd : d ≤ d') :
    ehh h C d' ≤ ehh h C d := by
  rcases le_or_gt C.card 1 with hc | hc
  · rw [ehh_eq_zero_of_card_le_one h hc, ehh_eq_zero_of_card_le_one h hc]
  · have h2 : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hc
    have hden : (0 : ℝ) < (C.card : ℝ) * ((C.card : ℝ) - 1) := by nlinarith
    have hsub : ((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h d' p.1 = window h d' p.2)
        ⊆ ((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h d p.1 = window h d p.2) := by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, hp.2.1, ?_⟩
      exact (window_eq_iff h d p.1 p.2).mpr fun k hk =>
        (window_eq_iff h d' p.1 p.2).mp hp.2.2 k (lt_of_lt_of_le hk hd)
    have hcard : concordantPairs h C d' ≤ concordantPairs h C d := Finset.card_le_card hsub
    have hcast : ((concordantPairs h C d' : ℕ) : ℝ) ≤ ((concordantPairs h C d : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [ehh, ehh]
    gcongr

/-- EHH as the sampling-without-replacement homozygosity of the partition of `C` into window
types: `EHH(d) = ∑_t c_t (c_t - 1) / (#C (#C - 1))`, where `c_t` is the number of haplotypes of
`C` with window `t`. This is the form in which EHH is usually defined. -/
theorem ehh_eq_sum_counts (h : ι → ℕ → α) (C : Finset ι) (d : ℕ) :
    ehh h C d = (∑ t ∈ C.image (window h d),
        ((C.filter fun i => window h d i = t).card : ℝ) *
          (((C.filter fun i => window h d i = t).card : ℝ) - 1)) /
      ((C.card : ℝ) * ((C.card : ℝ) - 1)) := by
  have hmem : ∀ p ∈ ((C ×ˢ C).filter
      fun p => p.1 ≠ p.2 ∧ window h d p.1 = window h d p.2),
      (fun p : ι × ι => window h d p.1) p ∈ C.image (window h d) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.mem_image.mpr ⟨p.1, hp.1.1, rfl⟩
  have hnat : concordantPairs h C d = ∑ t ∈ C.image (window h d),
      (C.filter fun i => window h d i = t).card *
        ((C.filter fun i => window h d i = t).card - 1) := by
    rw [concordantPairs, Finset.card_eq_sum_card_fiberwise hmem]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hset : (((C ×ˢ C).filter fun p => p.1 ≠ p.2 ∧ window h d p.1 = window h d p.2).filter
        fun p : ι × ι => window h d p.1 = t)
        = (C.filter fun i => window h d i = t).offDiag := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
        exact ⟨⟨h1, h5⟩, ⟨h2, h4 ▸ h5⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
        exact ⟨⟨⟨h1, h3⟩, h5, by rw [h2, h4]⟩, h2⟩
    rw [hset, Finset.offDiag_card, Nat.mul_sub, mul_one]
  rw [ehh, hnat, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  have hc1 : 1 ≤ (C.filter fun j => window h d j = window h d i).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  push_cast [Nat.cast_sub hc1]
  ring

/-- Relative extended haplotype homozygosity: the EHH of the core-allele carriers `C` divided
by the EHH of the complementary set `D` of haplotypes carrying the other core alleles. This is
the statistic of the long-range haplotype test (Sabeti et al. 2002). It is a junk value `0`
when the denominator vanishes; `one_lt_rehh_iff` assumes a positive denominator. -/
noncomputable def rehh (h : ι → ℕ → α) (C D : Finset ι) (d : ℕ) : ℝ :=
  ehh h C d / ehh h D d

/-- With a positive reference EHH, the relative EHH exceeds `1` exactly when the core allele's
haplotypes are the more homozygous ones. -/
theorem one_lt_rehh_iff (h : ι → ℕ → α) (C D : Finset ι) {d : ℕ} (hD : 0 < ehh h D d) :
    1 < rehh h C D d ↔ ehh h D d < ehh h C d := by
  rw [rehh, one_lt_div hD]

end Sample

section Neutral

/-- The probability that no recombination falls on the genealogy of a pair of lineages within
genetic distance `d` of the core, given that the pair coalesces at time `t` (time in units of
`2N` generations, `ρ = 4Nr` the scaled recombination rate per site): the two lineages carry
recombination events at total rate `ρ * d` until they coalesce.

This is a lower bound for the probability that the two haplotypes are identical over the
window — a recombined lineage may still carry the same alleles — so it is a lower bound for
the expected EHH, not its value. -/
noncomputable def pairNoRecomb (ρ d t : ℝ) : ℝ := exp (-(ρ * d) * t)

theorem pairNoRecomb_pos (ρ d t : ℝ) : 0 < pairNoRecomb ρ d t := exp_pos _

theorem pairNoRecomb_le_one {ρ d t : ℝ} (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    pairNoRecomb ρ d t ≤ 1 := by
  rw [pairNoRecomb, exp_le_one_iff]
  nlinarith [mul_nonneg (mul_nonneg hρ hd) ht]

/-- The no-recombination probability decays in the distance from the core. -/
theorem pairNoRecomb_antitone {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) {d d' : ℝ} (hd : d ≤ d') :
    pairNoRecomb ρ d' t ≤ pairNoRecomb ρ d t := by
  rw [pairNoRecomb, pairNoRecomb, exp_le_exp]
  nlinarith [mul_nonneg (mul_nonneg hρ ht) (sub_nonneg.mpr hd)]

theorem integrable_pairNoRecomb {ρ d : ℝ} (hρ : 0 ≤ ρ) (hd : 0 ≤ d) :
    Integrable (pairNoRecomb ρ d) (expMeasure 1) := by
  have ht : -(ρ * d) < 1 := by nlinarith [mul_nonneg hρ hd]
  have h := integrable_exp_mul_gammaMeasure (a := 1) (r := 1) one_pos one_pos ht
  change Integrable (pairNoRecomb ρ d) (gammaMeasure 1 1)
  exact h

/-- Averaging over the pair coalescence time `T₂`, which is exponential of rate `1` in units of
`2N` generations under the neutral coalescent, the probability that no recombination falls on
the pair's genealogy within distance `d` is `1 / (1 + ρ d)`. Since a recombined lineage can
still carry an identical haplotype, this is a lower bound for `E[EHH(d)]`. -/
theorem integral_pairNoRecomb {ρ d : ℝ} (hρ : 0 ≤ ρ) (hd : 0 ≤ d) :
    ∫ t, pairNoRecomb ρ d t ∂(expMeasure 1) = (1 + ρ * d)⁻¹ := by
  have ht : -(ρ * d) < 1 := by nlinarith [mul_nonneg hρ hd]
  have h := mgf_gammaMeasure_of_lt (a := 1) (r := 1) one_pos one_pos ht
  rw [mgf, Real.rpow_one] at h
  change ∫ t, pairNoRecomb ρ d t ∂(gammaMeasure 1 1) = (1 + ρ * d)⁻¹
  rw [show (1 : ℝ) + ρ * d = 1 - -(ρ * d) by ring, ← one_div]
  exact h

end Neutral

end MathlibExt.Biology.PopulationGenetics.SelectionScan
