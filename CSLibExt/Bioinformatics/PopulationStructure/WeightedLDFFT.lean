/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod

import MathlibExt.Analysis.Fourier.ZModConvolution
import Mathlib.Analysis.RCLike.Basic

/-!
# ALDER's Fourier-transform computation of weighted LD

ALDER (Loh et al. 2013) computes, for every distance bin, the sum over SNP pairs of the
weighted sample covariance `ẑ(x, y) w(x) w(y)`. Instead of binning the genetic distance of each
pair, it discretizes the genetic map positions themselves into grid cells `c x ∈ ℕ` (default
resolution 0.05 cM) and groups the ordered pairs `(x, y)` by the cell offset `c y - c x = j`.
The weighted sum then becomes, for each individual `i`, the autocorrelation at lag `j` of the
cell totals `U_i k = ∑_{c x = k} (g_i(x) - ḡ(x)) w(x)`, which a fast Fourier transform
evaluates as the inverse transform of `|𝓕 U_i|^2` after zero padding.

We prove that this transform computation equals the brute-force sum over pairs.

## Main results

* `pairSum_eq_sum_cellSum`: grouping ordered pairs by cell offset,
  `∑_{x, y : c y = c x + j} u x v y = ∑_{k < K} U k V (k + j)` for the cell totals `U`, `V`.
* `autocorrDFT_eq`: zero-padded circular autocorrelation through the discrete Fourier
  transform on `ZMod N`, `𝓕⁻(|𝓕 Ũ|^2)(j) = ∑_k U k U (k + j)`, whenever `U` vanishes from `K`
  on, `2 K ≤ N + 1` and `j < K`.
* `dftWeightedLD_eq_bruteWeightedLD`: the transform algorithm returns exactly the brute-force
  weighted-LD sum `∑_{x, y : c y = c x + j} ẑ(x, y) w(x) w(y)` with the unbiased sample
  covariance `ẑ`.
* `autocorrDFT_cellCount`: the number of pairs at offset `j` (ALDER's normalizer) is computed
  the same way.

## Scope

"FFT" here means any algorithm that computes `ZMod.dft`; the radix-2 Cooley–Tukey splitting is
`MathlibExt.Analysis.Fourier.FastFourierTransform`. The pairs are binned by grid-cell offset,
as in ALDER, not by exact genetic distance. Lag `j = 0` includes the diagonal pairs `x = y`;
for `j > 0` every counted pair has `x ≠ y`. The sample covariance divides by `m - 1`, which is
meaningful for `m ≥ 2` individuals; the identities hold for every `m` because both sides use
the same factor.

## References

* P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger,
  *Inferring admixture histories of human populations using linkage disequilibrium*,
  Genetics 193 (2013), 1233–1254 (section "Fast Fourier transform algorithm for computing
  weighted LD").
-/

@[expose] public section

open ZMod

namespace Cslib.Bioinformatics.PopulationStructure.WeightedLDFFT

variable {S : Type*} [Fintype S] (c : S → ℕ)

/-! ### Binning by grid-cell offset -/

/-- The total `U k = ∑_{x : c x = k} u x` of a per-SNP quantity `u` over grid cell `k`. -/
def cellSum (u : S → ℝ) (k : ℕ) : ℝ := ∑ x with c x = k, u x

/-- The brute-force sum `∑_{x, y : c y = c x + j} u x v y` over ordered SNP pairs whose grid
cells differ by `j`. -/
def pairSum (u v : S → ℝ) (j : ℕ) : ℝ := ∑ x, ∑ y, if c y = c x + j then u x * v y else 0

/-- Grouping pairs by cell offset: if every SNP lies in a cell `c x < K`, the pair sum at
offset `j` is the lag-`j` cross-correlation of the cell totals. -/
theorem pairSum_eq_sum_cellSum {K : ℕ} (hc : ∀ x, c x < K) (u v : S → ℝ) (j : ℕ) :
    pairSum c u v j = ∑ k ∈ Finset.range K, cellSum c u k * cellSum c v (k + j) := by
  have h1 : pairSum c u v j = ∑ x, u x * cellSum c v (c x + j) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cellSum, Finset.mul_sum, Finset.sum_filter]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range K) (g := c)
    (fun x _ => Finset.mem_range.2 (hc x))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cellSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-! ### Autocorrelation through the discrete Fourier transform -/

/-- Zero padding: the sequence `U` read on `ZMod N` through `k ↦ U k.val`. When `U` vanishes
from `K` on and `K ≤ N`, this is `U` followed by `N - K` zeros. -/
def pad (N : ℕ) (U : ℕ → ℝ) : ZMod N → ℂ := fun k => (U k.val : ℂ)

/-- The transform computation of the lag-`j` autocorrelation: the inverse discrete Fourier
transform of the power spectrum `|𝓕 Ũ|^2` of the zero-padded sequence, read at `j`. -/
noncomputable def autocorrDFT (N : ℕ) [NeZero N] (U : ℕ → ℝ) (j : ℕ) : ℂ :=
  𝓕⁻ (fun ξ => (Complex.normSq (𝓕 (pad N U) ξ) : ℂ)) (j : ZMod N)

private theorem conj_dft_pad (N : ℕ) [NeZero N] (U : ℕ → ℝ) (ξ : ZMod N) :
    starRingEnd ℂ (𝓕 (pad N U) ξ) = 𝓕 (fun k => pad N U (-k)) ξ := by
  rw [dft_comp_neg]
  dsimp only
  rw [dft_apply, dft_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_eq_mul, map_mul, pad, Complex.conj_ofReal]
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

/-- Zero-padded circular autocorrelation equals the linear one: if `U k = 0` for `k ≥ K`,
`2 K ≤ N + 1` and `j < K`, then `𝓕⁻(|𝓕 Ũ|^2)(j) = ∑_{k < K} U k U (k + j)`. -/
theorem autocorrDFT_eq {N K : ℕ} [NeZero N] {U : ℕ → ℝ} (hU : ∀ k, K ≤ k → U k = 0)
    (hN : 2 * K ≤ N + 1) {j : ℕ} (hj : j < K) :
    autocorrDFT N U j = ((∑ k ∈ Finset.range K, U k * U (k + j) : ℝ) : ℂ) := by
  have h1 : autocorrDFT N U j = ∑ i : ZMod N, pad N U (-i) * pad N U ((j : ZMod N) - i) := by
    rw [autocorrDFT, ← invDFT_mul_dft]
    refine congrArg (fun F => (𝓕⁻ F) (j : ZMod N)) (funext fun ξ => ?_)
    rw [Complex.normSq_eq_conj_mul_self, conj_dft_pad]
  have h2 : ∑ i : ZMod N, pad N U (-i) * pad N U ((j : ZMod N) - i) =
      ∑ k : ZMod N, pad N U k * pad N U ((j : ZMod N) + k) := by
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun i => ?_
    simp [sub_eq_add_neg]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  rw [h1, h2]
  have h3 : ∑ k : ZMod (n + 1), pad (n + 1) U k * pad (n + 1) U ((j : ZMod (n + 1)) + k) =
      ∑ k ∈ Finset.range (n + 1), ((U k * U ((j + k) % (n + 1)) : ℝ) : ℂ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pad, Complex.ofReal_mul]
    congr 3
    rw [ZMod.val_add, ZMod.val_natCast]
    simp [Nat.add_mod]
    rfl
  rw [h3, ← Complex.ofReal_sum]
  congr 1
  symm
  calc ∑ k ∈ Finset.range K, U k * U (k + j)
      = ∑ k ∈ Finset.range K, U k * U ((j + k) % (n + 1)) :=
        Finset.sum_congr rfl fun k hk => by
          rw [Finset.mem_range] at hk
          rw [Nat.mod_eq_of_lt (by omega), add_comm]
    _ = _ := Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => by
        rw [hU k (by simpa using hk), zero_mul]

/-! ### Weighted LD -/

variable {m : ℕ} (g : Fin m → S → ℝ) (w : S → ℝ)

/-- The sample mean genotype `ḡ(x) = (1/m) ∑ i, g i x` at SNP `x` over `m` individuals. -/
noncomputable def meanGeno (x : S) : ℝ := (∑ i, g i x) / m

/-- The unbiased sample covariance `ẑ(x, y) = (1/(m - 1)) ∑ i, (g i x - ḡ x) (g i y - ḡ y)`
of the genotypes at SNPs `x` and `y` (Loh et al. 2013, Eq. 5; meaningful for `m ≥ 2`). -/
noncomputable def sampleCov (x y : S) : ℝ :=
  (∑ i, (g i x - meanGeno g x) * (g i y - meanGeno g y)) / ((m : ℝ) - 1)

/-- The brute-force weighted-LD sum at cell offset `j`:
`∑_{x, y : c y = c x + j} ẑ(x, y) w(x) w(y)`, costing a pass over all pairs. -/
noncomputable def bruteWeightedLD (j : ℕ) : ℝ :=
  ∑ x, ∑ y, if c y = c x + j then sampleCov g x y * w x * w y else 0

private theorem cellSum_eq_zero {K : ℕ} (hc : ∀ x, c x < K) (u : S → ℝ) {k : ℕ}
    (hk : K ≤ k) : cellSum c u k = 0 :=
  Finset.sum_eq_zero fun x hx => absurd (Finset.mem_filter.1 hx).2 (by have := hc x; omega)

/-- The centred weighted genotype `(g i x - ḡ x) w x` of individual `i` at SNP `x`. -/
noncomputable def centredWeighted (i : Fin m) (x : S) : ℝ := (g i x - meanGeno g x) * w x

/-- ALDER's transform algorithm: for each individual, the zero-padded autocorrelation of the
cell totals of its centred weighted genotypes, computed through `𝓕`; summed over individuals
and divided by `m - 1`. -/
noncomputable def dftWeightedLD (N : ℕ) [NeZero N] (j : ℕ) : ℂ :=
  (∑ i, autocorrDFT N (cellSum c (centredWeighted g w i)) j) / ((m : ℂ) - 1)

/-- The transform algorithm computes the brute-force weighted-LD sum exactly, for every lag
`j < K`, when all SNPs lie in cells `c x < K` and the transform length satisfies
`2 K ≤ N + 1`. -/
theorem dftWeightedLD_eq_bruteWeightedLD {N K : ℕ} [NeZero N] (hc : ∀ x, c x < K)
    (hN : 2 * K ≤ N + 1) {j : ℕ} (hj : j < K) :
    dftWeightedLD c g w N j = (bruteWeightedLD c g w j : ℂ) := by
  have hi : ∀ i, autocorrDFT N (cellSum c (centredWeighted g w i)) j =
      (pairSum c (centredWeighted g w i) (centredWeighted g w i) j : ℂ) := fun i => by
    rw [autocorrDFT_eq (fun k hk => cellSum_eq_zero c hc _ hk) hN hj,
      pairSum_eq_sum_cellSum c hc]
  have hb : bruteWeightedLD c g w j =
      (∑ i, pairSum c (centredWeighted g w i) (centredWeighted g w i) j) / ((m : ℝ) - 1) := by
    simp only [bruteWeightedLD, pairSum, sampleCov, centredWeighted]
    simp_rw [Finset.sum_div]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp
  rw [dftWeightedLD, hb]
  simp_rw [hi]
  push_cast
  rfl

/-- The number of ordered SNP pairs at cell offset `j`, by which ALDER divides the weighted
sum. -/
def pairCount (j : ℕ) : ℕ := ∑ x, ∑ y, if c y = c x + j then 1 else 0

/-- The pair count is the zero-padded autocorrelation of the cell occupancy counts. -/
theorem autocorrDFT_cellCount {N K : ℕ} [NeZero N] (hc : ∀ x, c x < K)
    (hN : 2 * K ≤ N + 1) {j : ℕ} (hj : j < K) :
    autocorrDFT N (cellSum c fun _ => 1) j = (pairCount c j : ℂ) := by
  rw [autocorrDFT_eq (fun k hk => cellSum_eq_zero c hc _ hk) hN hj,
    ← pairSum_eq_sum_cellSum c hc]
  simp [pairSum, pairCount]

end Cslib.Bioinformatics.PopulationStructure.WeightedLDFFT
