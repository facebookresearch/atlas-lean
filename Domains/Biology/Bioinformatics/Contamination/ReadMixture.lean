/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.HardyWeinberg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Read-mixture likelihood for the contamination fraction

A DNA sample is a mixture of a targeted individual (fraction `1 - α`) and one unrelated
contaminating individual (fraction `α`), and the same fraction `α` of the sequence reads comes
from the contaminant. This file defines the likelihood of `α` given the base calls of the reads
covering a finite set of biallelic sites (Jun et al. 2012, Equations 1 and 2).

## Model

* Bases are `Fin 4` (order `A, C, G, T`). A `Site` has two distinct alleles `ref` and `alt`, the
  number `depth` of reads covering it, and the phred base quality `quality j` of the base call of
  read `j`. A genotype `g : Fin 3` is the number of copies of `alt`.
* `errorProb Q e` is the law of the sequencing-error indicator `e` (`true` for an error) of a call
  of phred quality `Q`: `P(e = 1) = 10^(-Q/10)` (`phredErrorProb`).
* `alleleCallProb a e b`: a read of allele `a` is called `a` without an error, and each of the
  three other bases with probability `1/3` on an error.
* `callProb s g e b`, the probability `P(b | g, e)` of Table 1 of the source: the read carries one
  of the two alleles of `g`, chosen uniformly, and is then called as `alleleCallProb` says.
* `hwGenotype G` is the genotype law of an individual born of random mating in a population whose
  parents have genotype law `G` (`HardyWeinberg.offspring`). By `HardyWeinberg.offspring_apply` it
  is the Hardy–Weinberg law `q², 2pq, p²` of the population's allele frequencies `p` of `alt` and
  `q` of `ref` (`hwGenotype_zero`, `hwGenotype_one`, `hwGenotype_two`), so the population allele
  frequencies at a site are `HardyWeinberg.gamete G`.

## Main definitions

* `likelihoodWithPriors s π₁ π₂ b α`: the likelihood
  `∏ᵢ ∑_{g₁} ∑_{g₂} {∏ⱼ ∑ₑ [(1 - α) P(bᵢⱼ | g₁, e) + α P(bᵢⱼ | g₂, e)] P(eᵢⱼ)} π₂ᵢ(g₂) π₁ᵢ(g₁)`
  for genotype priors `π₁ i` of the target and `π₂ i` of the contaminant at each site `i`.
* `likelihood s pop b α`: the sequence-only likelihood `L(α)` (Equation 2), where both genotypes
  have the Hardy–Weinberg law `hwGenotype (pop i)`.
* `arrayGenotypeProb G r`: the prior `P(g | G) = ∑_ε P(g | ε; G) P(ε)` of the target's genotype
  given its array genotype `G` and genotyping-error probability `r`, a law for `0 ≤ r ≤ 1`.
* `arrayLikelihood s pop G r b α`: the likelihood with array genotypes of the target
  (Equation 1).

## Main results

* `likelihoodWithPriors_one_sub`: swapping target and contaminant replaces `α` by `1 - α`.
* `likelihood_one_sub`: the reflection `L(1 - α) = L(α)`.
* `likelihood_eq_prod_of_depth_le_one`: with at most one read per site, every `α` has the same
  likelihood `∏ᵢ ∑_g P(g) P(bᵢ | g)`.
* `sum_likelihoodWithPriors` and `likelihoodWithPriors_nonneg`: for `α ∈ [0, 1]` and genotype
  priors that are probability vectors, the likelihood is a probability mass function of the base
  calls.
* `arrayLikelihood_eq`: Equation 1 as the source writes it, with the sum over the genotyping-error
  indicator inside the product over sites.

## References

* G. Jun, M. Flickinger, K. N. Hetrick et al., *Detecting and estimating contamination of human
  DNA samples in sequencing and array-based genotype data*, American Journal of Human Genetics 91
  (2012), 839–848, Material and Methods (Equations 1 and 2, Table 1),
  <https://doi.org/10.1016/j.ajhg.2012.09.004>.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Domains.Biology.Bioinformatics.Contamination.ReadMixture

open MathlibExt.Biology.PopulationGenetics

/-! ### Sites and base calls -/

/-- A **biallelic site covered by sequencing reads**: two distinct alleles `ref` and `alt` among
the bases `Fin 4` (order `A, C, G, T`), the number `depth` of reads covering the site, and the
phred base quality `quality j` of the base call of read `j`, on the phred scale
`Q = -10 log₁₀ p` of the probability `p` that the call is wrong (`phredErrorProb`). -/
structure Site where
  /-- The reference allele. -/
  ref : Fin 4
  /-- The alternative allele. -/
  alt : Fin 4
  /-- The two alleles are distinct. -/
  ref_ne_alt : ref ≠ alt
  /-- The number of reads covering the site. -/
  depth : ℕ
  /-- The phred base quality of the base call of each read, on the phred scale. -/
  quality : Fin depth → ℝ≥0

/-- The **phred error probability** `10^(-Q/10)` of a base call of phred base quality `Q`: the
phred scale is `Q = -10 log₁₀ p` for the probability `p` that the call is wrong, so quality `10`
means `p = 1/10` and quality `20` means `p = 1/100`. It lies in `[0, 1]`
(`phredErrorProb_nonneg`, `phredErrorProb_le_one`). -/
noncomputable def phredErrorProb (Q : ℝ≥0) : ℝ := (10 : ℝ) ^ (-(Q : ℝ) / 10)

/-- The **law of the sequencing-error indicator** `e` (`true` for an error) of a base call of phred
base quality `Q`: `P(e = 1) = 10^(-Q/10)` and `P(e = 0) = 1 - 10^(-Q/10)` (`phredErrorProb`).
It is a probability law for every `Q : ℝ≥0` (`errorProb_nonneg`, `sum_errorProb`). -/
noncomputable def errorProb (Q : ℝ≥0) (e : Bool) : ℝ :=
  if e then phredErrorProb Q else 1 - phredErrorProb Q

/-- The **probability that a read carrying allele `a` is called as base `b`**, among the bases
`Fin 4`, given its sequencing-error indicator `e` (`true` for an error): without an error the call
is `a`, and an error is equally likely to produce each of the three other bases, with probability
`1/3` each. For each `a` and `e` it is a probability law on `b` (`alleleCallProb_nonneg`,
`sum_alleleCallProb`). -/
noncomputable def alleleCallProb (a : Fin 4) (e : Bool) (b : Fin 4) : ℝ :=
  if e then (if b = a then 0 else 1 / 3) else (if b = a then 1 else 0)

/-- The **probability of a base call given the genotype and the error indicator**, `P(b | g, e)`:
the probability that a read at the biallelic site `s` (alleles `s.ref ≠ s.alt` among the bases
`Fin 4`) from an individual of genotype `g`, the number of copies of `s.alt`, is called as base
`b`, given its sequencing-error indicator `e` (`true` for an error). The read carries one of the
two alleles of `g` chosen uniformly, so `s.alt` with probability `g / 2` and `s.ref` with
probability `(2 - g) / 2`; without an error it is called as that allele, and an error is equally
likely to produce each of the three other bases (`alleleCallProb`; Table 1 of Jun et al. 2012). -/
noncomputable def callProb (s : Site) (g : Fin 3) (e : Bool) (b : Fin 4) : ℝ :=
  ((g : ℕ) : ℝ) / 2 * alleleCallProb s.alt e b + (2 - ((g : ℕ) : ℝ)) / 2 * alleleCallProb s.ref e b

theorem phredErrorProb_nonneg (Q : ℝ≥0) : 0 ≤ phredErrorProb Q :=
  Real.rpow_nonneg (by norm_num) _

theorem phredErrorProb_le_one (Q : ℝ≥0) : phredErrorProb Q ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by have := Q.coe_nonneg; linarith)

theorem errorProb_nonneg (Q : ℝ≥0) (e : Bool) : 0 ≤ errorProb Q e := by
  cases e
  · simpa [errorProb] using phredErrorProb_le_one Q
  · simpa [errorProb] using phredErrorProb_nonneg Q

theorem sum_errorProb (Q : ℝ≥0) : ∑ e, errorProb Q e = 1 := by
  simp [errorProb]

theorem alleleCallProb_nonneg (a : Fin 4) (e : Bool) (b : Fin 4) : 0 ≤ alleleCallProb a e b := by
  unfold alleleCallProb
  split_ifs <;> norm_num

theorem sum_alleleCallProb (a : Fin 4) (e : Bool) : ∑ b, alleleCallProb a e b = 1 := by
  cases e <;> fin_cases a <;> simp [alleleCallProb, Fin.sum_univ_four] <;> norm_num

theorem callProb_nonneg (s : Site) (g : Fin 3) (e : Bool) (b : Fin 4) :
    0 ≤ callProb s g e b := by
  have hg : ((g : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp g.isLt
  unfold callProb
  have := alleleCallProb_nonneg s.alt e b
  have := alleleCallProb_nonneg s.ref e b
  positivity

theorem sum_callProb (s : Site) (g : Fin 3) (e : Bool) : ∑ b, callProb s g e b = 1 := by
  simp only [callProb, Finset.sum_add_distrib, ← Finset.mul_sum, sum_alleleCallProb]
  ring

/-! ### Hardy–Weinberg genotype law -/

/-- The **genotype of an ordered pair of alleles** at a biallelic site, as the number `0`, `1` or
`2` of copies of the alternative allele `true` (the reference allele is `false`). -/
def altCount : Bool × Bool → Fin 3
  | (false, false) => 0
  | (true, false) => 1
  | (false, true) => 1
  | (true, true) => 2

/-- The **Hardy–Weinberg genotype law** at a biallelic site, counting copies of the alternative
allele (`true`): the genotype law of an individual born of random mating in a population whose
parents have genotype law `G` (`HardyWeinberg.offspring G`). Its masses are `q²`, `2pq` and `p²`,
where `p` and `q` are the population's frequencies `HardyWeinberg.gamete G` of the alternative and
the reference allele (`hwGenotype_zero`, `hwGenotype_one`, `hwGenotype_two`). -/
noncomputable def hwGenotype (G : PMF (Bool × Bool)) : PMF (Fin 3) :=
  (HardyWeinberg.offspring G).map altCount

theorem hwGenotype_zero (G : PMF (Bool × Bool)) :
    hwGenotype G 0 = HardyWeinberg.gamete G false ^ 2 := by
  simp [hwGenotype, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, altCount,
    HardyWeinberg.offspring_apply, sq]

theorem hwGenotype_one (G : PMF (Bool × Bool)) :
    hwGenotype G 1 = 2 * HardyWeinberg.gamete G true * HardyWeinberg.gamete G false := by
  simp only [hwGenotype, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    altCount, HardyWeinberg.offspring_apply]
  simp
  ring

theorem hwGenotype_two (G : PMF (Bool × Bool)) :
    hwGenotype G 2 = HardyWeinberg.gamete G true ^ 2 := by
  simp [hwGenotype, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, altCount,
    HardyWeinberg.offspring_apply, sq]

theorem hwGenotype_congr {G G' : PMF (Bool × Bool)}
    (h : HardyWeinberg.gamete G = HardyWeinberg.gamete G') : hwGenotype G = hwGenotype G' := by
  simp only [hwGenotype, HardyWeinberg.offspring, h]

theorem sum_toReal_hwGenotype (G : PMF (Bool × Bool)) : ∑ g, (hwGenotype G g).toReal = 1 := by
  have h := (hwGenotype G).tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun g _ => PMF.apply_ne_top _ g, h, ENNReal.toReal_one]

/-! ### The likelihood -/

variable {ι : Type*} [Fintype ι]

/-- The **read-mixture likelihood** of the contamination fraction `α`, for genotype priors `π₁ i`
of the target and `π₂ i` of the contaminant at each site `s i`,

`L(α) = ∏ᵢ ∑_{g₁} ∑_{g₂} {∏ⱼ ∑ₑ [(1 - α) P(bᵢⱼ | g₁, e) + α P(bᵢⱼ | g₂, e)] P(eᵢⱼ = e)}
π₂ᵢ(g₂) π₁ᵢ(g₁)`,

where `b i j` is the base call of read `j` at site `s i`, `P(b | g, e)` is `callProb`, and the
sequencing-error indicator of read `j` has `P(eᵢⱼ = 1) = 10^(-Qᵢⱼ/10)` and
`P(eᵢⱼ = 0) = 1 - 10^(-Qᵢⱼ/10)` for the phred quality `Qᵢⱼ = (s i).quality j` of its call
(`errorProb`). For `α ∈ [0, 1]` and genotype priors `π₁ i` and `π₂ i` that are probability
vectors, this is the likelihood of the following model. The genotype pairs of different sites are
independent, and the two genotypes `g₁, g₂` of a site are independent with laws `π₁ i` and `π₂ i`.
The error indicators `eᵢⱼ` are independent across reads and independent of the genotypes and of
which individual each read comes from, with the laws above. Conditionally on the genotype pair of
its site and on its own error indicator, each read's base call is drawn, independently of the
other reads, from the two-sample mixture `(1 - α) P(b | g₁, eᵢⱼ) + α P(b | g₂, eᵢⱼ)`. With the
array-genotype priors `arrayGenotypeProb` of the target and of a study individual `k` as `π₁` and
`π₂` it is the source's likelihood `L(α, k)`, which the source maximises over `(α, k)` to find the
most likely contaminating sample. -/
noncomputable def likelihoodWithPriors (s : ι → Site) (π₁ π₂ : ι → Fin 3 → ℝ)
    (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) : ℝ :=
  ∏ i, ∑ g₁ : Fin 3, ∑ g₂ : Fin 3,
    (∏ j, ∑ e : Bool,
      ((1 - α) * callProb (s i) g₁ e (b i j) + α * callProb (s i) g₂ e (b i j)) *
        errorProb ((s i).quality j) e) * π₂ i g₂ * π₁ i g₁

/-- The **sequence-only read-mixture likelihood** of the contamination fraction `α` (Jun et al.
2012, Equation 2). Each site `s i` is biallelic, with two distinct alleles among the bases `Fin 4`,
and a genotype is the number `g ∈ {0, 1, 2}` of copies of its alternative allele. The genotypes
`g₁` of the target and `g₂` of the contaminant at site `i` are unknown, independent, and both drawn
from the Hardy–Weinberg proportions `P(g) = hwGenotype (pop i) g` at the population allele
frequencies `HardyWeinberg.gamete (pop i)`, where `pop i` is the genotype law of the population's
parents at site `i`; the genotype pairs of different sites are independent. The sequencing-error
indicators `eᵢⱼ` of the reads are independent across reads and independent of the genotypes and
of which individual each read comes from, with `P(eᵢⱼ = 1) = 10^(-Qᵢⱼ/10)` and
`P(eᵢⱼ = 0) = 1 - 10^(-Qᵢⱼ/10)` for the phred quality `Qᵢⱼ = (s i).quality j` of the call
(`errorProb`). Conditionally on the genotype pair of its site and on its own error indicator, each
read's base call `b i j` is drawn, independently of the other reads, from the two-sample mixture
`(1 - α) P(b | g₁, eᵢⱼ) + α P(b | g₂, eᵢⱼ)`, where `P(b | g, e)` is `callProb`. The likelihood is

`L(α) = ∏ᵢ ∑_{g₁} ∑_{g₂} {∏ⱼ ∑ₑ [(1 - α) P(bᵢⱼ | g₁, e) + α P(bᵢⱼ | g₂, e)] P(eᵢⱼ = e)}
P(g₂) P(g₁)`,

the likelihood `likelihoodWithPriors` with both genotype priors Hardy–Weinberg. The model takes
`α ∈ [0, 1]`. -/
noncomputable def likelihood (s : ι → Site) (pop : ι → PMF (Bool × Bool))
    (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) : ℝ :=
  likelihoodWithPriors s (fun i g => (hwGenotype (pop i) g).toReal)
    (fun i g => (hwGenotype (pop i) g).toReal) b α

/-- The **law of the genotyping-error indicator** `ε` (`true` for an error) of an array genotype
with genotyping-error probability `r`: `P(ε = 1) = r` and `P(ε = 0) = 1 - r`. It is a probability
law when `0 ≤ r ≤ 1`. -/
def genotypingErrorProb (r : ℝ) (ε : Bool) : ℝ := if ε then r else 1 - r

/-- The **true genotype given an array genotype and a genotyping-error indicator**: the
probability `P(g | ε; G)` that the true genotype is `g` given the array genotype `G` and the
genotyping-error indicator `ε` (`true` for an error), genotypes being the number of copies of the
alternative allele. Without a genotyping error the true genotype is `G`; on a genotyping error it
is each of the two genotypes other than `G` with probability `1/2`. -/
noncomputable def genotypeGivenArray (G : Fin 3) (ε : Bool) (g : Fin 3) : ℝ :=
  if ε then (if g = G then 0 else 1 / 2) else (if g = G then 1 else 0)

/-- The **genotype prior given an array genotype**: `P(g | G) = ∑_{ε ∈ {0, 1}} P(g | ε; G) P(ε)`
for the true genotype `g` (the number of copies of the alternative allele) of an individual whose
array genotype is `G`, marginalised over a binary genotyping-error indicator `ε` with
`P(ε = 1) = r` and `P(ε = 0) = 1 - r` (`genotypingErrorProb`). Without a genotyping error the true
genotype is `G`; on a genotyping error it is each of the two genotypes other than `G` with
probability `1/2` (`genotypeGivenArray`). For `0 ≤ r ≤ 1` it is a probability law on `g`
(`arrayGenotypeProb_nonneg`, `sum_arrayGenotypeProb`). -/
noncomputable def arrayGenotypeProb (G : Fin 3) (r : ℝ) (g : Fin 3) : ℝ :=
  ∑ ε : Bool, genotypeGivenArray G ε g * genotypingErrorProb r ε

/-- The **read-mixture likelihood with array genotypes of the target** (Jun et al. 2012,
Equation 1): the sequence-only likelihood `likelihood` with the prior of the target's genotype at
site `i` replaced by `arrayGenotypeProb (G i) (r i)`, its law given the array genotype `G i` and
the genotyping-error probability `r i`, where the model takes `0 ≤ r i ≤ 1`. The contaminant's
genotype keeps the Hardy–Weinberg law
`hwGenotype (pop i)`. `arrayLikelihood_eq` writes it with the sum over the genotyping-error
indicator inside the product over sites, as the source does. -/
noncomputable def arrayLikelihood (s : ι → Site) (pop : ι → PMF (Bool × Bool)) (G : ι → Fin 3)
    (r : ι → ℝ) (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) : ℝ :=
  likelihoodWithPriors s (fun i => arrayGenotypeProb (G i) (r i))
    (fun i g => (hwGenotype (pop i) g).toReal) b α

/-! ### Symmetry -/

/-- **Swapping the two individuals.** The read-mixture likelihood at `1 - α` with priors `π₁` for
the target and `π₂` for the contaminant equals the likelihood at `α` with the priors swapped. -/
theorem likelihoodWithPriors_one_sub (s : ι → Site) (π₁ π₂ : ι → Fin 3 → ℝ)
    (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) :
    likelihoodWithPriors s π₁ π₂ b (1 - α) = likelihoodWithPriors s π₂ π₁ b α := by
  unfold likelihoodWithPriors
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₁ _ => Finset.sum_congr rfl fun g₂ _ => ?_
  have h : ∀ x y : ℝ, (1 - (1 - α)) * x + (1 - α) * y = (1 - α) * y + α * x := fun _ _ => by
    ring
  simp only [h]
  ring

/-- **Reflection symmetry of the sequence-only likelihood**: `L(1 - α) = L(α)`, since the target
and the contaminant have the same genotype prior. -/
theorem likelihood_one_sub (s : ι → Site) (pop : ι → PMF (Bool × Bool))
    (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) :
    likelihood s pop b (1 - α) = likelihood s pop b α :=
  likelihoodWithPriors_one_sub _ _ _ _ _

/-! ### One read per site -/

private theorem prod_mix_of_subsingleton {J : Type*} [Fintype J] [Subsingleton J] (α : ℝ)
    (x y : J → ℝ) :
    ∏ j, ((1 - α) * x j + α * y j) = (1 - α) * ∏ j, x j + α * ∏ j, y j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp
  · obtain ⟨j₀⟩ := hJ
    simp only [Fintype.prod_subsingleton _ j₀]

-- With equal genotype priors that are probability vectors and at most one read per site, the
-- read-mixture likelihood does not depend on `α`: site `i` contributes `∑_g π i g P(bᵢ | g)`, where
-- `P(b | g) = ∑ₑ P(b | g, e) P(e)`.
theorem likelihoodWithPriors_self_eq_prod_of_depth_le_one (s : ι → Site) (π : ι → Fin 3 → ℝ)
    (hπ : ∀ i, ∑ g, π i g = 1) (b : ∀ i, Fin (s i).depth → Fin 4)
    (hs : ∀ i, (s i).depth ≤ 1) (α : ℝ) :
    likelihoodWithPriors s π π b α =
      ∏ i, ∑ g, π i g *
        ∏ j, ∑ e, callProb (s i) g e (b i j) * errorProb ((s i).quality j) e := by
  unfold likelihoodWithPriors
  refine Finset.prod_congr rfl fun i _ => ?_
  have : Subsingleton (Fin (s i).depth) := Fin.subsingleton_iff_le_one.2 (hs i)
  set P : Fin 3 → ℝ := fun g =>
    ∏ j, ∑ e, callProb (s i) g e (b i j) * errorProb ((s i).quality j) e with hP
  have hmix : ∀ g₁ g₂ : Fin 3,
      (∏ j, ∑ e : Bool,
        ((1 - α) * callProb (s i) g₁ e (b i j) + α * callProb (s i) g₂ e (b i j)) *
          errorProb ((s i).quality j) e) = (1 - α) * P g₁ + α * P g₂ := by
    intro g₁ g₂
    rw [hP, ← prod_mix_of_subsingleton]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp only [hmix]
  calc ∑ g₁, ∑ g₂, ((1 - α) * P g₁ + α * P g₂) * π i g₂ * π i g₁
      = (∑ g₁, (1 - α) * (π i g₁ * P g₁)) * ∑ g₂, π i g₂ +
          (∑ g₁, π i g₁) * ∑ g₂, α * (π i g₂ * P g₂) := by
        rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g₁ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g₂ _ => ?_
        ring
    _ = ∑ g, π i g * P g := by
        rw [hπ, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- **With one read per site every `α` has the same sequence-only likelihood**: if no site is
covered by more than one read, then `L(α) = ∏ᵢ ∑_g P(g) P(bᵢ | g)` with
`P(b | g) = ∑ₑ P(b | g, e) P(e)`, whatever `α`. -/
theorem likelihood_eq_prod_of_depth_le_one (s : ι → Site) (pop : ι → PMF (Bool × Bool))
    (b : ∀ i, Fin (s i).depth → Fin 4) (hs : ∀ i, (s i).depth ≤ 1) (α : ℝ) :
    likelihood s pop b α =
      ∏ i, ∑ g, (hwGenotype (pop i) g).toReal *
        ∏ j, ∑ e, callProb (s i) g e (b i j) * errorProb ((s i).quality j) e :=
  likelihoodWithPriors_self_eq_prod_of_depth_le_one s _ (fun _ => sum_toReal_hwGenotype _) b hs α

/-! ### A probability law on the base calls -/

/-- The read-mixture likelihood sums to one over all possible base calls of the reads, for every
`α`, when the genotype priors at each site sum to one. -/
theorem sum_likelihoodWithPriors [DecidableEq ι] (s : ι → Site) (π₁ π₂ : ι → Fin 3 → ℝ)
    (h₁ : ∀ i, ∑ g, π₁ i g = 1) (h₂ : ∀ i, ∑ g, π₂ i g = 1) (α : ℝ) :
    ∑ b : (∀ i, Fin (s i).depth → Fin 4), likelihoodWithPriors s π₁ π₂ b α = 1 := by
  unfold likelihoodWithPriors
  rw [← Fintype.prod_sum (fun i (c : Fin (s i).depth → Fin 4) => ∑ g₁ : Fin 3, ∑ g₂ : Fin 3,
    (∏ j, ∑ e : Bool,
      ((1 - α) * callProb (s i) g₁ e (c j) + α * callProb (s i) g₂ e (c j)) *
        errorProb ((s i).quality j) e) * π₂ i g₂ * π₁ i g₁)]
  refine Finset.prod_eq_one fun i _ => ?_
  have hreads : ∀ g₁ g₂ : Fin 3, ∑ c : Fin (s i).depth → Fin 4, ∏ j, ∑ e : Bool,
      ((1 - α) * callProb (s i) g₁ e (c j) + α * callProb (s i) g₂ e (c j)) *
        errorProb ((s i).quality j) e = 1 := by
    intro g₁ g₂
    rw [← Fintype.prod_sum (fun j (x : Fin 4) => ∑ e : Bool,
      ((1 - α) * callProb (s i) g₁ e x + α * callProb (s i) g₂ e x) *
        errorProb ((s i).quality j) e)]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, sum_callProb, mul_one,
      sub_add_cancel, one_mul, sum_errorProb]
  calc ∑ c : Fin (s i).depth → Fin 4, ∑ g₁ : Fin 3, ∑ g₂ : Fin 3,
        (∏ j, ∑ e : Bool,
          ((1 - α) * callProb (s i) g₁ e (c j) + α * callProb (s i) g₂ e (c j)) *
            errorProb ((s i).quality j) e) * π₂ i g₂ * π₁ i g₁
      = ∑ g₁ : Fin 3, ∑ g₂ : Fin 3, (∑ c : Fin (s i).depth → Fin 4, ∏ j, ∑ e : Bool,
          ((1 - α) * callProb (s i) g₁ e (c j) + α * callProb (s i) g₂ e (c j)) *
            errorProb ((s i).quality j) e) * π₂ i g₂ * π₁ i g₁ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g₂ _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = 1 := by
        simp only [hreads, one_mul, ← Finset.sum_mul, h₁, h₂]

/-- The read-mixture likelihood is nonnegative for `α ∈ [0, 1]` and nonnegative genotype priors.
With `sum_likelihoodWithPriors`, for genotype priors that are probability vectors it is then a
probability mass function of the base calls. -/
theorem likelihoodWithPriors_nonneg (s : ι → Site) (π₁ π₂ : ι → Fin 3 → ℝ)
    (h₁ : ∀ i g, 0 ≤ π₁ i g) (h₂ : ∀ i g, 0 ≤ π₂ i g) (b : ∀ i, Fin (s i).depth → Fin 4)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    0 ≤ likelihoodWithPriors s π₁ π₂ b α := by
  have hα : 0 ≤ 1 - α := sub_nonneg.2 hα₁
  refine Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun g₁ _ =>
    Finset.sum_nonneg fun g₂ _ => mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j _ =>
      Finset.sum_nonneg fun e _ => mul_nonneg ?_ (errorProb_nonneg _ _)) (h₂ i g₂)) (h₁ i g₁)
  exact add_nonneg (mul_nonneg hα (callProb_nonneg _ _ _ _))
    (mul_nonneg hα₀ (callProb_nonneg _ _ _ _))

theorem sum_likelihood [DecidableEq ι] (s : ι → Site) (pop : ι → PMF (Bool × Bool)) (α : ℝ) :
    ∑ b : (∀ i, Fin (s i).depth → Fin 4), likelihood s pop b α = 1 :=
  sum_likelihoodWithPriors s _ _ (fun _ => sum_toReal_hwGenotype _)
    (fun _ => sum_toReal_hwGenotype _) α

theorem likelihood_nonneg (s : ι → Site) (pop : ι → PMF (Bool × Bool))
    (b : ∀ i, Fin (s i).depth → Fin 4) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    0 ≤ likelihood s pop b α :=
  likelihoodWithPriors_nonneg s _ _ (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => ENNReal.toReal_nonneg) b hα₀ hα₁

/-! ### Array genotypes -/

theorem sum_arrayGenotypeProb (G : Fin 3) (r : ℝ) : ∑ g, arrayGenotypeProb G r g = 1 := by
  fin_cases G <;>
    simp [arrayGenotypeProb, genotypeGivenArray, genotypingErrorProb, Fin.sum_univ_three] <;>
    ring

theorem arrayGenotypeProb_nonneg (G : Fin 3) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (g : Fin 3) :
    0 ≤ arrayGenotypeProb G r g := by
  have : 0 ≤ 1 - r := sub_nonneg.2 hr₁
  simp only [arrayGenotypeProb, Fintype.sum_bool, genotypeGivenArray, genotypingErrorProb]
  split_ifs <;> positivity

/-- **Equation 1 as the source writes it**: the likelihood with array genotypes of the target
keeps the sum over the genotyping-error indicator `εᵢ` inside the product over sites, alongside the
sums over the two genotypes:

`L(α) = ∏ᵢ ∑_{εᵢ} ∑_{g₁} ∑_{g₂} {∏ⱼ ∑ₑ [(1 - α) P(bᵢⱼ | g₁, e) + α P(bᵢⱼ | g₂, e)] P(eᵢⱼ = e)}
P(g₂) P(g₁ | εᵢ; Gᵢ) P(εᵢ)`. -/
theorem arrayLikelihood_eq (s : ι → Site) (pop : ι → PMF (Bool × Bool)) (G : ι → Fin 3)
    (r : ι → ℝ) (b : ∀ i, Fin (s i).depth → Fin 4) (α : ℝ) :
    arrayLikelihood s pop G r b α =
      ∏ i, ∑ ε : Bool, ∑ g₁ : Fin 3, ∑ g₂ : Fin 3,
        (∏ j, ∑ e : Bool,
          ((1 - α) * callProb (s i) g₁ e (b i j) + α * callProb (s i) g₂ e (b i j)) *
            errorProb ((s i).quality j) e) * (hwGenotype (pop i) g₂).toReal *
          genotypeGivenArray (G i) ε g₁ * genotypingErrorProb (r i) ε := by
  unfold arrayLikelihood likelihoodWithPriors arrayGenotypeProb
  refine Finset.prod_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₁ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

end Domains.Biology.Bioinformatics.Contamination.ReadMixture
