/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics

/-!
# f-statistics and PCA from coalescence times

## f-statistics (Peter 2016)

For allele frequencies `a`, `b` in two populations at a biallelic site, `hetPair a b =
a (1 - b) + b (1 - a)` is the probability that a gene drawn from the first population and a
gene drawn from the second carry different alleles; `hetPair a a = 2 a (1 - a)` is the
heterozygosity of a population (two genes drawn independently, i.e. with replacement). The
exact identity `(a - b) ^ 2 = hetPair a b - (hetPair a a + hetPair b b) / 2`
(`sq_sub_eq_hetPair`) gives Peter's (2016) expression of `f2` through expected
heterozygosities `π X Y = 𝔼[hetPair (p X) (p Y)]` (`f2_eq_meanHet`):

  `f2 A B = π A B - (π A A + π B B) / 2`.

Under neutral infinite-sites mutation (time in units of `2N` generations, `θ = 4Nu`) the
expected number of differences between two genes is `θ` times their expected coalescence
time, `π X Y = θ 𝔼[T X Y]` (`CoalescentModel`), whence

* `f2 A B = θ (𝔼 T_AB - (𝔼 T_AA + 𝔼 T_BB) / 2)`,
* `f3 C A B = θ / 2 * (𝔼 T_CA + 𝔼 T_CB - 𝔼 T_AB - 𝔼 T_CC)`,
* `f4 A B C D = θ / 2 * (𝔼 T_AD + 𝔼 T_BC - 𝔼 T_AC - 𝔼 T_BD)`.

## PCA (McVean 2009)

For a genotype matrix `Z` (samples `ι` × loci `S`) with columns centred over the samples, the
sample covariance `C i j = (1 / L) ∑ s, X i s * X j s` (`L = |S|`, `X` the centred matrix) is
the double centring of the pairwise-difference matrix `d i j = ∑ s, (Z i s - Z j s) ^ 2`:

  `C i j = (d̄ i· + d̄ ·j - d i j - d̄ ··) / (2 L)`

(`genCov_eq_doubleCenter`, an exact finite identity). If `𝔼[d i j] = θ t i j` with `t i j` the
expected coalescence time of samples `i` and `j`, then
`𝔼[C i j] = θ / (2 L) * (t̄ i· + t̄ ·j - t i j - t̄ ··)` (`McVeanModel.integral_genCov`):
the expected PCA matrix is determined by the expected pairwise coalescence times.

Allele frequencies lie in `[0, 1]`, `θ ≥ 0` and coalescence times are nonnegative in the
biological model, but every identity here holds for all real values. The coalescent link
`π = θ 𝔼 T` is a model assumption (`CoalescentModel`, `McVeanModel`), not derived from a
genealogical process. Divisions by the number of samples are meaningful because a sample index
exists; the division by the number of loci `L` is meaningful for `L ≥ 1` (for `L = 0` both
sides of McVean's identity are `0` by the convention `x / 0 = 0`).

## Main results

* `sq_sub_eq_hetPair`, `f2_eq_meanHet`: Peter's heterozygosity form of `f2`.
* `CoalescentModel.f2_eq`, `CoalescentModel.f3_eq`, `CoalescentModel.f4_eq`.
* `genCov_eq_doubleCenter`, `McVeanModel.integral_genCov`: McVean's identity.

## References

* B. M. Peter, *Admixture, population structure, and F-statistics*, Genetics 202 (2016),
  1485–1501.
* G. McVean, *A genealogical interpretation of principal components analysis*, PLoS Genet. 5
  (2009), e1000686.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics

/-! ### f-statistics from heterozygosities and coalescence times -/

/-- The probability `a (1 - b) + b (1 - a)` that a gene from a population with allele frequency
`a` and a gene from a population with allele frequency `b` differ at a biallelic site. -/
def hetPair (a b : ℝ) : ℝ := a * (1 - b) + b * (1 - a)

/-- `(a - b) ^ 2 = hetPair a b - (hetPair a a + hetPair b b) / 2`. -/
theorem sq_sub_eq_hetPair (a b : ℝ) :
    (a - b) ^ 2 = hetPair a b - (hetPair a a + hetPair b b) / 2 := by
  unfold hetPair
  ring

variable {Ω P : Type*} {m : MeasurableSpace Ω}

/-- The expected heterozygosity `π X Y = 𝔼[hetPair (p X) (p Y)]` between populations `X` and
`Y` (within population `X` when `Y = X`). -/
noncomputable def meanHet (μ : Measure Ω) (p : P → Ω → ℝ) (X Y : P) : ℝ :=
  ∫ ω, hetPair (p X ω) (p Y ω) ∂μ

/-- `hetPair` of square-integrable frequencies is integrable on a finite measure space. -/
theorem integrable_hetPair {μ : Measure Ω} [IsFiniteMeasure μ] {p : P → Ω → ℝ}
    (hp : ∀ X, MemLp (p X) 2 μ) (X Y : P) :
    Integrable (fun ω => hetPair (p X ω) (p Y ω)) μ := by
  have h : (fun ω => hetPair (p X ω) (p Y ω)) =
      fun ω => p X ω + p Y ω - 2 * (p X ω * p Y ω) := by
    funext ω
    unfold hetPair
    ring
  rw [h]
  exact (((hp X).integrable one_le_two).add ((hp Y).integrable one_le_two)).sub
    (((hp X).integrable_mul (hp Y)).const_mul 2)

/-- Peter (2016): `f2 A B = π A B - (π A A + π B B) / 2`. -/
theorem f2_eq_meanHet {μ : Measure Ω} [IsFiniteMeasure μ] {p : P → Ω → ℝ}
    (hp : ∀ X, MemLp (p X) 2 μ) (A B : P) :
    f2 μ p A B = meanHet μ p A B - (meanHet μ p A A + meanHet μ p B B) / 2 := by
  unfold f2 meanHet
  simp_rw [sq_sub_eq_hetPair]
  have h : Integrable (fun ω => (hetPair (p A ω) (p A ω) + hetPair (p B ω) (p B ω)) / 2) μ :=
    ((integrable_hetPair hp A A).add (integrable_hetPair hp B B)).div_const 2
  rw [integral_sub (integrable_hetPair hp A B) h, integral_div,
    integral_add (integrable_hetPair hp A A) (integrable_hetPair hp B B)]

/-- The relation between allele frequencies and coalescence times under neutral
infinite-sites mutation, taken as the model assumption: the expected heterozygosity between
populations `X` and `Y` is `θ` times the expected coalescence time `coalTime X Y` of a gene
from `X` and a gene from `Y` (two genes drawn independently, so with replacement, when
`X = Y`). Time is in units of `2N` generations and `θ = 4Nu`. The measure `μ` is finite: it
ranges over the evolutionary randomness and, in practice, over a finite set of loci. For
`θ = 0` the coalescence times are not determined by the frequencies, and the identities below
then say that the f-statistics vanish. -/
structure CoalescentModel (μ : Measure Ω) (P : Type*) where
  /-- Allele frequencies of the populations. -/
  freq : P → Ω → ℝ
  /-- The scaled mutation rate `θ = 4Nu`. -/
  theta : ℝ
  /-- Expected pairwise coalescence times `𝔼[T X Y]`. -/
  coalTime : P → P → ℝ
  /-- Frequencies are square integrable. -/
  memLp_freq : ∀ X, MemLp (freq X) 2 μ
  /-- Infinite sites: `π X Y = θ 𝔼[T X Y]`. -/
  meanHet_eq : ∀ X Y, meanHet μ freq X Y = theta * coalTime X Y

namespace CoalescentModel

variable {μ : Measure Ω} [IsFiniteMeasure μ] (M : CoalescentModel μ P)

/-- `f2 A B = θ (𝔼 T_AB - (𝔼 T_AA + 𝔼 T_BB) / 2)`. -/
theorem f2_eq (A B : P) :
    f2 μ M.freq A B =
      M.theta * (M.coalTime A B - (M.coalTime A A + M.coalTime B B) / 2) := by
  rw [f2_eq_meanHet M.memLp_freq, M.meanHet_eq, M.meanHet_eq, M.meanHet_eq]
  ring

/-- `f3 C A B = θ / 2 * (𝔼 T_CA + 𝔼 T_CB - 𝔼 T_AB - 𝔼 T_CC)`. -/
theorem f3_eq (C A B : P) :
    f3 μ M.freq C A B =
      M.theta / 2 * (M.coalTime C A + M.coalTime C B - M.coalTime A B - M.coalTime C C) := by
  rw [f3_eq_f2 M.memLp_freq, M.f2_eq, M.f2_eq, M.f2_eq]
  ring

/-- `f4 A B C D = θ / 2 * (𝔼 T_AD + 𝔼 T_BC - 𝔼 T_AC - 𝔼 T_BD)`. -/
theorem f4_eq (A B C D : P) :
    f4 μ M.freq A B C D =
      M.theta / 2 * (M.coalTime A D + M.coalTime B C - M.coalTime A C - M.coalTime B D) := by
  rw [f4_eq_f2 M.memLp_freq, M.f2_eq, M.f2_eq, M.f2_eq, M.f2_eq]
  ring

end CoalescentModel

/-! ### PCA from coalescence times (McVean 2009) -/

section PCA

variable {ι S : Type*} [Fintype ι] [Fintype S]

/-- The column mean `(1 / n) ∑ i, Z i s` of locus `s` over the `n` samples. -/
noncomputable def colMean (Z : ι → S → ℝ) (s : S) : ℝ := (∑ i, Z i s) / Fintype.card ι

/-- The genotype matrix with columns centred over the samples. -/
noncomputable def centered (Z : ι → S → ℝ) (i : ι) (s : S) : ℝ := Z i s - colMean Z s

/-- The sample covariance `C i j = (1 / L) ∑ s, X i s * X j s` of the centred genotype matrix
`X` over the `L` loci. -/
noncomputable def genCov (Z : ι → S → ℝ) (i j : ι) : ℝ :=
  (∑ s, centered Z i s * centered Z j s) / Fintype.card S

/-- The number of pairwise differences `d i j = ∑ s, (Z i s - Z j s) ^ 2` (for `0`/`1`
haplotypes, the number of loci at which samples `i` and `j` differ). -/
def pairDiff (Z : ι → S → ℝ) (i j : ι) : ℝ := ∑ s, (Z i s - Z j s) ^ 2

/-- The double centring `t̄ i· + t̄ ·j - t i j - t̄ ··` of a square matrix `t` (row, column and
grand means over the `n` indices). -/
noncomputable def doubleCenter (t : ι → ι → ℝ) (i j : ι) : ℝ :=
  (∑ k, t i k) / Fintype.card ι + (∑ k, t k j) / Fintype.card ι - t i j -
    (∑ k, ∑ l, t k l) / (Fintype.card ι : ℝ) ^ 2

private theorem sum_sq_sub {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ℝ) :
    (∑ k, (x - a k) ^ 2) =
      Fintype.card ι * x ^ 2 - 2 * x * (∑ k, a k) + ∑ k, a k ^ 2 := by
  classical
  calc
    (∑ k, (x - a k) ^ 2) = ∑ k, (x ^ 2 - (2 * x) * a k + a k ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem doubleCenter_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) (i j : ι) :
    doubleCenter (fun k l => (a k - a l) ^ 2) i j =
      2 * (a i - (∑ k, a k) / Fintype.card ι) *
        (a j - (∑ k, a k) / Fintype.card ι) := by
  classical
  let : Nonempty ι := ⟨i⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcol : (∑ k, (a k - a j) ^ 2) = ∑ k, (a j - a k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hgrand : (∑ k, ∑ l, (a k - a l) ^ 2) =
      2 * Fintype.card ι * (∑ k, a k ^ 2) - 2 * (∑ k, a k) ^ 2 := by
    simp_rw [sum_sq_sub]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  unfold doubleCenter
  rw [hcol, hgrand, sum_sq_sub, sum_sq_sub]
  field_simp [hn]
  ring

private theorem doubleCenter_sum {ι S : Type*} [Fintype ι] [Fintype S]
    (t : S → ι → ι → ℝ) (i j : ι) :
    doubleCenter (fun k l => ∑ s, t s k l) i j = ∑ s, doubleCenter (t s) i j := by
  classical
  have hgrand : (∑ k, ∑ l, ∑ s, t s k l) = ∑ s, ∑ k, ∑ l, t s k l := by
    calc
      (∑ k, ∑ l, ∑ s, t s k l) = ∑ k, ∑ s, ∑ l, t s k l := by
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold doubleCenter
  rw [hgrand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
  congr 3 <;> exact Finset.sum_comm

/-- McVean (2009), deterministic form: the covariance of the centred genotype matrix is the
double centring of the pairwise-difference matrix, divided by `2 L`. -/
theorem genCov_eq_doubleCenter (Z : ι → S → ℝ) (i j : ι) :
    genCov Z i j = doubleCenter (pairDiff Z) i j / (2 * Fintype.card S) := by
  classical
  unfold genCov pairDiff
  rw [doubleCenter_sum]
  simp_rw [doubleCenter_sq]
  simp_rw [mul_assoc (2 : ℝ)]
  rw [← Finset.mul_sum]
  simp only [centered, colMean]
  ring

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- McVean's genealogical setting for PCA, taken as the model assumption: random genotypes
`Z i s` (sample `i`, locus `s`), square integrable, whose expected numbers of pairwise
differences are `θ` times the expected pairwise coalescence times `coalTime i j` (neutral
infinite sites, time in units of `2N` generations, `θ` the total scaled mutation rate of the
`L` loci). For `θ = 0` the coalescence times are not determined by the genotypes. -/
structure McVeanModel (μ : Measure Ω) (ι S : Type*) [Fintype ι] [Fintype S] where
  /-- Random genotypes. -/
  geno : ι → S → Ω → ℝ
  /-- The scaled mutation rate. -/
  theta : ℝ
  /-- Expected pairwise coalescence times of the samples. -/
  coalTime : ι → ι → ℝ
  /-- Genotypes are square integrable. -/
  memLp_geno : ∀ i s, MemLp (geno i s) 2 μ
  /-- Infinite sites: `𝔼[d i j] = θ t i j`. -/
  integral_pairDiff : ∀ i j, ∫ ω, pairDiff (fun k s => geno k s ω) i j ∂μ = theta * coalTime i j

/-- McVean (2009): the expected genotype covariance is `θ / (2 L)` times the double centring of
the expected pairwise coalescence times,
`𝔼[C i j] = θ / (2 L) * (t̄ i· + t̄ ·j - t i j - t̄ ··)`. -/
theorem McVeanModel.integral_genCov {μ : Measure Ω} (M : McVeanModel μ ι S) (i j : ι) :
    ∫ ω, genCov (fun k s => M.geno k s ω) i j ∂μ =
      M.theta / (2 * Fintype.card S) * doubleCenter M.coalTime i j := by
  classical
  let d : ι → ι → Ω → ℝ := fun k l ω => pairDiff (fun k s => M.geno k s ω) k l
  have hd (k l : ι) : Integrable (d k l) μ := by
    apply integrable_finsetSum
    intro s _
    exact ((M.memLp_geno k s).sub (M.memLp_geno l s)).integrable_sq
  have hr (k : ι) : Integrable (fun ω => ∑ l, d k l ω) μ :=
    integrable_finsetSum _ (fun l _ => hd k l)
  have hc (l : ι) : Integrable (fun ω => ∑ k, d k l ω) μ :=
    integrable_finsetSum _ (fun k _ => hd k l)
  have hg : Integrable (fun ω => ∑ k, ∑ l, d k l ω) μ :=
    integrable_finsetSum _ (fun k _ => hr k)
  have ha : Integrable (fun ω => (∑ l, d i l ω) / Fintype.card ι +
      (∑ k, d k j ω) / Fintype.card ι) μ :=
    ((hr i).div_const _).add ((hc j).div_const _)
  have hb : Integrable (fun ω => (∑ l, d i l ω) / Fintype.card ι +
      (∑ k, d k j ω) / Fintype.card ι - d i j ω) μ := ha.sub (hd i j)
  simp_rw [genCov_eq_doubleCenter]
  rw [integral_div]
  change (∫ ω, doubleCenter (fun k l => d k l ω) i j ∂μ) /
    (2 * Fintype.card S) = _
  unfold doubleCenter
  rw [integral_sub hb (hg.div_const _),
    integral_sub ha (hd i j),
    integral_add ((hr i).div_const _) ((hc j).div_const _),
    integral_div, integral_div, integral_div,
    integral_finsetSum _ (fun k _ => hd i k),
    integral_finsetSum _ (fun k _ => hd k j),
    integral_finsetSum _ (fun k _ => hr k)]
  simp_rw [integral_finsetSum _ (fun l _ => hd _ l)]
  simp only [d, M.integral_pairDiff, ← Finset.mul_sum]
  ring

end PCA

end MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics
