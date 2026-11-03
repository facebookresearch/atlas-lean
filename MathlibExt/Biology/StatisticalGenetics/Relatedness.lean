/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Relatedness: genomic relationship moments

In Malécot's model two gene copies that are identical by descent (IBD) carry the same allele,
and copies that are not IBD carry independent alleles with the population frequency `p`.
`IBDModel` records exactly the resulting first and second moments of the allele indicators at a
biallelic locus. With the kinship coefficient
`φ_ij = ¼ Σ_{a,b} P(copy a of i and copy b of j are IBD)` and the inbreeding coefficient
`F_i = P(the two copies of i are IBD)`, the genotypes `x_i ∈ {0, 1, 2}` satisfy
`𝔼[(x_i - 2p)(x_j - 2p)] = 2p(1 - p) · 2φ_ij`. Hence the genetic relationship matrix (GRM)
entry `(x_i - 2p)(x_j - 2p) / (2p(1 - p))` of Yang et al. (2010) is unbiased for `2φ_ij`, the
KING statistic satisfies `𝔼[(x_i - x_j)²] = 4p(1 - p)(1 - 2φ_ij)` for non-inbred individuals
(Manichaikul et al. 2010), and the GCTA diagonal estimator is unbiased for `1 + F_i`
(Yang et al. 2011). All of these are exact identities at one locus with known `p`; the
estimators of the cited papers average them over loci and plug in sample frequencies, which is
not covered here. IBD probabilities on a pedigree are computed in
`MathlibExt.Biology.StatisticalGenetics.Kinship`.

## Main results

* `IBDModel`: Malécot's IBD model at one locus (first and second moments);
  `IBDModel.ibd_self`, `IBDModel.ibd_comm`, `IBDModel.kinship_self` (`φ_ii = (1 + F_i)/2`).
* `IBDModel.integral_genotype`, `IBDModel.integral_genotype_mul`: `𝔼[x_i] = 2p`,
  `𝔼[x_i x_j] = 4p² + 4p(1 - p) φ_ij`.
* `IBDModel.integral_grm`: `𝔼[A_ij] = 2φ_ij` for the GRM entry;
  `IBDModel.integral_grm_self`: `𝔼[A_ii] = 1 + F_i`.
* `IBDModel.integral_sub_sq`, `IBDModel.integral_sub_sq_of_inbreeding_eq_zero`: the KING
  moment `𝔼[(x_i - x_j)²] = 4p(1 - p)(1 - 2φ_ij)` for non-inbred `i, j`.
* `IBDModel.integral_grmDiag`: the GCTA diagonal estimator is unbiased for `1 + F_i`.

## References

* G. Malécot, *Les mathématiques de l'hérédité*, Masson, Paris, 1948.
* J. Yang, B. Benyamin, B. P. McEvoy, et al., *Common SNPs explain a large proportion of the
  heritability for human height*, Nat. Genet. 42 (2010), 565–569.
* J. Yang, S. H. Lee, M. E. Goddard, P. M. Visscher, *GCTA: a tool for genome-wide complex
  trait analysis*, Am. J. Hum. Genet. 88 (2011), 76–82.
* A. Manichaikul, J. C. Mychaleckyj, S. S. Rich, K. Daly, M. Sale, W.-M. Chen, *Robust
  relationship inference in genome-wide association studies*, Bioinformatics 26 (2010),
  2867–2873.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Biology.StatisticalGenetics.Relatedness

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Malécot's identity-by-descent model at one biallelic locus, at the level of second
moments. The individuals are `ι`; individual `i` carries the gene copies `(i, 0)` (paternal) and
`(i, 1)` (maternal), and `allele c ∈ {0, 1}` indicates the reference allele on copy `c`. The
reference allele has frequency `p ∈ (0, 1)` (a polymorphic locus), and `ibd c d` is the
probability that the copies `c` and `d` are identical by descent: IBD copies carry the same
allele and non-IBD copies are independent draws with frequency `p` (Malécot 1948), which gives
the second moments `𝔼[a_c a_d] = p² + p (1 - p) ibd c d`. Only these first and second moments
are assumed. `ibd` is determined by the moments (`p (1 - p) ≠ 0`), and `ibd c c = 1`
(`IBDModel.ibd_self`). In Malécot's model `ibd c d ∈ [0, 1]`; the structure does not require
this, and the identities below hold for any real `ibd` (for example a correlation relative to a
reference population, which can be negative). A monomorphic locus (`p ∈ {0, 1}`) is excluded:
there the GRM denominator `2p(1 - p)` vanishes. -/
structure IBDModel (μ : Measure Ω) (ι : Type*) where
  /-- The reference-allele frequency. -/
  p : ℝ
  /-- The locus is polymorphic: `0 < p`. -/
  p_pos : 0 < p
  /-- The locus is polymorphic: `p < 1`. -/
  p_lt_one : p < 1
  /-- The reference-allele indicator of each gene copy. -/
  allele : ι × Fin 2 → Ω → ℝ
  /-- The allele indicators are random variables. -/
  measurable_allele : ∀ c, Measurable (allele c)
  /-- The allele indicators take the values `0` and `1`. -/
  allele_mem : ∀ c ω, allele c ω = 0 ∨ allele c ω = 1
  /-- The probability that two gene copies are identical by descent. -/
  ibd : ι × Fin 2 → ι × Fin 2 → ℝ
  /-- Every copy carries the reference allele with probability `p`. -/
  integral_allele : ∀ c, ∫ ω, allele c ω ∂μ = p
  /-- Malécot's second moments: `𝔼[a_c a_d] = p² + p (1 - p) ibd c d`. -/
  integral_allele_mul : ∀ c d, ∫ ω, allele c ω * allele d ω ∂μ = p ^ 2 + p * (1 - p) * ibd c d

namespace IBDModel

variable {μ : Measure Ω} {ι : Type*} (D : IBDModel μ ι)

/-- The genotype (reference-allele count) `x_i ∈ {0, 1, 2}` of individual `i`. -/
def genotype (i : ι) (ω : Ω) : ℝ := D.allele (i, 0) ω + D.allele (i, 1) ω

/-- The kinship coefficient `φ_ij`: the probability that a copy drawn at random from `i` and a
copy drawn at random from `j` are identical by descent. -/
noncomputable def kinship (i j : ι) : ℝ := (∑ a : Fin 2, ∑ b : Fin 2, D.ibd (i, a) (j, b)) / 4

/-- The inbreeding coefficient `F_i`: the probability that the two copies of `i` are identical
by descent. -/
def inbreeding (i : ι) : ℝ := D.ibd (i, 0) (i, 1)

/-- The genetic relationship matrix entry of Yang et al. (2010) at one locus,
`A_ij = (x_i - 2p)(x_j - 2p) / (2p(1 - p))`. -/
noncomputable def grm (i j : ι) (ω : Ω) : ℝ :=
  (D.genotype i ω - 2 * D.p) * (D.genotype j ω - 2 * D.p) / (2 * D.p * (1 - D.p))

/-- The diagonal estimator of GCTA (Yang et al. 2011) at one locus,
`A_ii = 1 + (x_i² - (1 + 2p) x_i + 2p²) / (2p(1 - p))`. -/
noncomputable def grmDiag (i : ι) (ω : Ω) : ℝ :=
  1 + (D.genotype i ω ^ 2 - (1 + 2 * D.p) * D.genotype i ω + 2 * D.p ^ 2) /
    (2 * D.p * (1 - D.p))

private theorem norm_allele_le (c : ι × Fin 2) (ω : Ω) : ‖D.allele c ω‖ ≤ 1 := by
  rcases D.allele_mem c ω with h | h <;> simp [h]

variable [IsFiniteMeasure μ] in
/-- The allele indicators are integrable. -/
theorem integrable_allele (c : ι × Fin 2) : Integrable (D.allele c) μ :=
  Integrable.of_bound (D.measurable_allele c).aestronglyMeasurable 1
    (ae_of_all _ (D.norm_allele_le c))

variable [IsFiniteMeasure μ] in
/-- Products of allele indicators are integrable. -/
theorem integrable_allele_mul (c d : ι × Fin 2) :
    Integrable (fun ω => D.allele c ω * D.allele d ω) μ :=
  (D.integrable_allele d).bdd_mul (D.measurable_allele c).aestronglyMeasurable
    (ae_of_all _ (D.norm_allele_le c))

/-- A gene copy is identical by descent with itself: `ibd c c = 1`. -/
theorem ibd_self (c : ι × Fin 2) : D.ibd c c = 1 := by
  have hsq : (fun ω => D.allele c ω * D.allele c ω) = D.allele c := by
    funext ω; rcases D.allele_mem c ω with h | h <;> simp [h]
  have h := D.integral_allele_mul c c
  rw [hsq, D.integral_allele] at h
  have hp : D.p * (1 - D.p) ≠ 0 := mul_ne_zero D.p_pos.ne' (sub_pos.mpr D.p_lt_one).ne'
  have : D.p * (1 - D.p) * (D.ibd c c - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hp
  · linarith

/-- Identity by descent is symmetric. -/
theorem ibd_comm (c d : ι × Fin 2) : D.ibd c d = D.ibd d c := by
  have h1 := D.integral_allele_mul c d
  have h2 := D.integral_allele_mul d c
  simp_rw [mul_comm (D.allele d _)] at h2
  have hp : D.p * (1 - D.p) ≠ 0 := mul_ne_zero D.p_pos.ne' (sub_pos.mpr D.p_lt_one).ne'
  have : D.p * (1 - D.p) * (D.ibd c d - D.ibd d c) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hp
  · linarith

/-- `φ_ii = (1 + F_i) / 2`. -/
theorem kinship_self (i : ι) : D.kinship i i = (1 + D.inbreeding i) / 2 := by
  simp only [kinship, inbreeding, Fin.sum_univ_two, D.ibd_self]
  rw [D.ibd_comm (i, 1) (i, 0)]
  ring

/-- Kinship is symmetric. -/
theorem kinship_comm (i j : ι) : D.kinship i j = D.kinship j i := by
  simp only [kinship, Fin.sum_univ_two, D.ibd_comm (i, _) (j, _)]
  ring

variable [IsProbabilityMeasure μ]

/-- Genotypes are integrable. -/
theorem integrable_genotype (i : ι) : Integrable (D.genotype i) μ :=
  (D.integrable_allele _).add (D.integrable_allele _)

/-- Products of genotypes are integrable. -/
theorem integrable_genotype_mul (i j : ι) :
    Integrable (fun ω => D.genotype i ω * D.genotype j ω) μ := by
  simp only [genotype, add_mul, mul_add]
  exact (((D.integrable_allele_mul _ _).add (D.integrable_allele_mul _ _)).add
    ((D.integrable_allele_mul _ _).add (D.integrable_allele_mul _ _)))

/-- `𝔼[x_i] = 2p`. -/
theorem integral_genotype (i : ι) : ∫ ω, D.genotype i ω ∂μ = 2 * D.p := by
  simp only [genotype]
  rw [integral_add (by exact (D.integrable_allele _))
      (by exact (D.integrable_allele _)), D.integral_allele,
    D.integral_allele]
  ring

/-- `𝔼[x_i x_j] = 4p² + 4p(1 - p) φ_ij`. -/
theorem integral_genotype_mul (i j : ι) :
    ∫ ω, D.genotype i ω * D.genotype j ω ∂μ =
      4 * D.p ^ 2 + 4 * D.p * (1 - D.p) * D.kinship i j := by
  simp only [genotype, add_mul, mul_add]
  rw [integral_add (by exact ((D.integrable_allele_mul _ _).add (D.integrable_allele_mul _ _)))
      (by exact ((D.integrable_allele_mul _ _).add (D.integrable_allele_mul _ _))),
    integral_add (by exact (D.integrable_allele_mul _ _)) (by exact (D.integrable_allele_mul _ _)),
    integral_add (by exact (D.integrable_allele_mul _ _)) (by exact (D.integrable_allele_mul _ _))]
  simp only [D.integral_allele_mul, kinship, Fin.sum_univ_two]
  ring

/-- **The genetic relationship covariance** (Yang et al. 2010):
`𝔼[(x_i - 2p)(x_j - 2p)] = 2p(1 - p) · 2 φ_ij`. -/
theorem integral_centered_mul (i j : ι) :
    ∫ ω, (D.genotype i ω - 2 * D.p) * (D.genotype j ω - 2 * D.p) ∂μ =
      2 * D.p * (1 - D.p) * (2 * D.kinship i j) := by
  have h : (fun ω => (D.genotype i ω - 2 * D.p) * (D.genotype j ω - 2 * D.p)) =
      fun ω => D.genotype i ω * D.genotype j ω - 2 * D.p * D.genotype i ω -
        2 * D.p * D.genotype j ω + 4 * D.p ^ 2 := by
    funext ω; ring
  rw [h, integral_add (by exact (((D.integrable_genotype_mul i j).sub
      ((D.integrable_genotype i).const_mul _)).sub ((D.integrable_genotype j).const_mul _)))
      (by exact (integrable_const _)),
    integral_sub (by exact ((D.integrable_genotype_mul i j).sub
      ((D.integrable_genotype i).const_mul _))) (by exact ((D.integrable_genotype j).const_mul _)),
    integral_sub (by exact (D.integrable_genotype_mul i j))
        (by exact ((D.integrable_genotype i).const_mul _)),
    integral_const_mul, integral_const_mul, D.integral_genotype_mul, D.integral_genotype,
    D.integral_genotype, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **The GRM is unbiased for twice the kinship** (Yang et al. 2010):
`𝔼[A_ij] = 2 φ_ij`, for every pair `i, j` (including `i = j`, where `2 φ_ii = 1 + F_i`). -/
theorem integral_grm (i j : ι) : ∫ ω, D.grm i j ω ∂μ = 2 * D.kinship i j := by
  have hp : D.p * (1 - D.p) ≠ 0 := by
    have := D.p_pos; have := D.p_lt_one; positivity
  simp only [grm]
  rw [integral_div, D.integral_centered_mul]
  field_simp
  exact mul_div_cancel_left₀ _ hp

/-- The diagonal GRM entry is unbiased for `1 + F_i`: `𝔼[A_ii] = 1 + F_i`. -/
theorem integral_grm_self (i : ι) : ∫ ω, D.grm i i ω ∂μ = 1 + D.inbreeding i := by
  rw [integral_grm, kinship_self]
  ring

/-- **The KING moment** (Manichaikul et al. 2010), general form:
`𝔼[(x_i - x_j)²] = 2p(1 - p)(1 + F_i) + 2p(1 - p)(1 + F_j) - 8p(1 - p) φ_ij`. -/
theorem integral_sub_sq (i j : ι) :
    ∫ ω, (D.genotype i ω - D.genotype j ω) ^ 2 ∂μ =
      2 * D.p * (1 - D.p) * (1 + D.inbreeding i) + 2 * D.p * (1 - D.p) * (1 + D.inbreeding j) -
        8 * D.p * (1 - D.p) * D.kinship i j := by
  have h : (fun ω => (D.genotype i ω - D.genotype j ω) ^ 2) =
      fun ω => D.genotype i ω * D.genotype i ω - 2 * (D.genotype i ω * D.genotype j ω) +
        D.genotype j ω * D.genotype j ω := by
    funext ω; ring
  rw [h, integral_add (by exact ((D.integrable_genotype_mul i i).sub
      ((D.integrable_genotype_mul i j).const_mul _))) (by exact (D.integrable_genotype_mul j j)),
    integral_sub (by exact (D.integrable_genotype_mul i i))
      (by exact ((D.integrable_genotype_mul i j).const_mul _)),
    integral_const_mul, D.integral_genotype_mul, D.integral_genotype_mul,
    D.integral_genotype_mul, D.kinship_self, D.kinship_self]
  ring

/-- **The KING moment** (Manichaikul et al. 2010) for two non-inbred individuals:
`𝔼[(x_i - x_j)²] = 4p(1 - p)(1 - 2φ_ij)`. -/
theorem integral_sub_sq_of_inbreeding_eq_zero {i j : ι} (hi : D.inbreeding i = 0)
    (hj : D.inbreeding j = 0) :
    ∫ ω, (D.genotype i ω - D.genotype j ω) ^ 2 ∂μ =
      4 * D.p * (1 - D.p) * (1 - 2 * D.kinship i j) := by
  rw [integral_sub_sq, hi, hj]
  ring

/-- **The GCTA diagonal estimator is unbiased for `1 + F_i`** (Yang et al. 2011):
`𝔼[1 + (x_i² - (1 + 2p) x_i + 2p²) / (2p(1 - p))] = 1 + F_i`. -/
theorem integral_grmDiag (i : ι) : ∫ ω, D.grmDiag i ω ∂μ = 1 + D.inbreeding i := by
  have hp : D.p * (1 - D.p) ≠ 0 := by
    have := D.p_pos; have := D.p_lt_one; positivity
  have hint : Integrable (fun ω => D.genotype i ω ^ 2 - (1 + 2 * D.p) * D.genotype i ω +
      2 * D.p ^ 2) μ := by
    simp only [sq]
    exact ((D.integrable_genotype_mul i i).sub ((D.integrable_genotype i).const_mul _)).add
      (integrable_const _)
  have hnum : ∫ ω, (D.genotype i ω ^ 2 - (1 + 2 * D.p) * D.genotype i ω + 2 * D.p ^ 2) ∂μ =
      2 * D.p * (1 - D.p) * D.inbreeding i := by
    simp only [sq]
    rw [integral_add (by exact ((D.integrable_genotype_mul i i).sub
        ((D.integrable_genotype i).const_mul _))) (by exact (integrable_const _)),
      integral_sub (by exact (D.integrable_genotype_mul i i))
          (by exact ((D.integrable_genotype i).const_mul _)),
      integral_const_mul, D.integral_genotype_mul, D.integral_genotype, D.kinship_self,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  simp only [grmDiag]
  rw [integral_add (by exact (integrable_const _))
      (by exact (hint.div_const _)), integral_const, integral_div, hnum]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp
  rw [mul_div_cancel_left₀ _ hp]

end IBDModel

end MathlibExt.Biology.StatisticalGenetics.Relatedness
