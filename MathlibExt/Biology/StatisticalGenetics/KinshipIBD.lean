/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.Kinship
public import MathlibExt.Biology.StatisticalGenetics.Relatedness
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Pedigree gene dropping realizes Malécot's IBD model

Gene dropping on a pedigree (`MathlibExt.Biology.StatisticalGenetics.Kinship`) assigns every
non-founder gene copy a fair Mendelian coin, and the identity-by-descent probability
`Pedigree.ibd c d` is the fraction of the `4 ^ n` coin outcomes under which `c` and `d` descend
from the same founder copy. Dropping alleles as well, each of the `2 n` potential founder copies
carries an independent Bernoulli(`p`) reference-allele indicator, and every copy carries the
allele of its founder copy. On the finite sample space `Coins n × (Fin n × Fin 2 → Fin 2)`, with
uniform coins independent of iid Bernoulli(`p`) founder alleles, the allele indicators have the
first and second moments of Malécot's model (`Relatedness.IBDModel`) with `ibd = Pedigree.ibd`.
Every moment identity of `MathlibExt.Biology.StatisticalGenetics.Relatedness` (GRM, KING, GCTA
diagonal) therefore holds for pedigree gene dropping, with the gene-dropping kinship
`Pedigree.geneDropKinship`, equivalently the tabular kinship `Pedigree.kinship`.

## Main results

* `Pedigree.geneDropMeasure`: uniform Mendelian coins and iid Bernoulli(`p`) founder alleles.
* `Pedigree.integral_geneDropAllele`, `Pedigree.integral_geneDropAllele_mul`: `𝔼[a_c] = p` and
  `𝔼[a_c a_d] = p² + p (1 - p) ibd c d`.
* `Pedigree.ibdModel`: the resulting `IBDModel` with `ibd = P.ibd`.
* `Pedigree.ibdModel_kinship`, `Pedigree.ibdModel_inbreeding`,
  `Pedigree.ibdModel_kinship_eq_kinship`: the model's kinship and inbreeding are the
  gene-dropping (and tabular) ones.
* `Pedigree.integral_grm_ibdModel`: under gene dropping the GRM entry is unbiased for
  `2 φ_ij`.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Biology.StatisticalGenetics.Kinship

open Relatedness

namespace Pedigree

variable {n : ℕ}

/-- The gene-dropping sample space: Mendelian coins together with a reference-allele indicator
`A c ∈ {0, 1}` for every potential founder copy `c`. -/
abbrev GeneDropSpace (n : ℕ) : Type := Coins n × (Fin n × Fin 2 → Fin 2)

/-- The Bernoulli(`p`) weight of an allele indicator: `p` for `1`, `1 - p` for `0`. -/
noncomputable def alleleWeight (p : ℝ) (a : Fin 2) : ℝ := if a = 1 then p else 1 - p

/-- The probability of an outcome: uniform coins times iid Bernoulli(`p`) founder alleles. -/
noncomputable def geneDropWeight (p : ℝ) (x : GeneDropSpace n) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ * ∏ c, alleleWeight p (x.2 c)

private theorem card_coins' : Fintype.card (Coins n) = 4 ^ n := by
  simp [Coins]

private theorem sum_alleleWeight (p : ℝ) : ∑ a : Fin 2, alleleWeight p a = 1 := by
  simp [alleleWeight, Fin.sum_univ_two]

private theorem alleleWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : Fin 2) :
    0 ≤ alleleWeight p a := by
  unfold alleleWeight; split_ifs <;> linarith

private theorem geneDropWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : GeneDropSpace n) : 0 ≤ geneDropWeight p x :=
  mul_nonneg (by positivity) (Finset.prod_nonneg fun c _ => alleleWeight_nonneg hp0 hp1 _)

/-- The founder-allele weights sum to `1`. -/
private theorem sum_prod_alleleWeight (p : ℝ) :
    ∑ A : Fin n × Fin 2 → Fin 2, ∏ c, alleleWeight p (A c) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [sum_alleleWeight, Finset.prod_const_one]

private theorem sum_geneDropWeight (p : ℝ) : ∑ x : GeneDropSpace n, geneDropWeight p x = 1 := by
  simp only [geneDropWeight, Fintype.sum_prod_type, ← Finset.mul_sum, sum_prod_alleleWeight,
    mul_one, Finset.sum_const, Finset.card_univ, card_coins', nsmul_eq_mul]
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0))

/-- The gene-dropping probability mass function. -/
noncomputable def geneDropPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF (GeneDropSpace n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (geneDropWeight p x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => geneDropWeight_nonneg hp0 hp1 x,
      sum_geneDropWeight, ENNReal.ofReal_one])

/-- The gene-dropping law: uniform Mendelian coins, independent of iid Bernoulli(`p`)
reference-allele indicators on the founder copies. -/
noncomputable def geneDropMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (GeneDropSpace n) :=
  (geneDropPMF p hp0 hp1).toMeasure

instance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (geneDropMeasure (n := n) p hp0 hp1) := by
  unfold geneDropMeasure; infer_instance

/-- Integrals under the gene-dropping law are weighted finite sums: an average over the
coins of the Bernoulli-weighted sum over founder alleles. -/
theorem integral_geneDropMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Coins n → (Fin n × Fin 2 → Fin 2) → ℝ) :
    ∫ x, f x.1 x.2 ∂(geneDropMeasure p hp0 hp1) =
      ((4 : ℝ) ^ n)⁻¹ * ∑ ω, ∑ A, (∏ c, alleleWeight p (A c)) * f ω A := by
  rw [geneDropMeasure, PMF.integral_eq_sum, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [geneDropPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (geneDropWeight_nonneg hp0 hp1 _),
    smul_eq_mul, geneDropWeight, mul_assoc]

private theorem val_mul_self (a : Fin 2) : ((a : ℕ) : ℝ) * ((a : ℕ) : ℝ) = ((a : ℕ) : ℝ) := by
  fin_cases a <;> simp

/-- Factorization over the founder alleles: the probability that every founder copy in `S`
carries the reference allele is `p ^ #S`. -/
private theorem sum_prod_alleleWeight_mul_prod (p : ℝ) (S : Finset (Fin n × Fin 2)) :
    ∑ A : Fin n × Fin 2 → Fin 2, (∏ c, alleleWeight p (A c)) * ∏ c ∈ S, ((A c : ℕ) : ℝ) =
      p ^ S.card := by
  classical
  have h : ∀ A : Fin n × Fin 2 → Fin 2,
      (∏ c, alleleWeight p (A c)) * ∏ c ∈ S, ((A c : ℕ) : ℝ) =
        ∏ c, alleleWeight p (A c) * (if c ∈ S then ((A c : ℕ) : ℝ) else 1) := by
    intro A
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun c (a : Fin 2) =>
    alleleWeight p a * (if c ∈ S then ((a : ℕ) : ℝ) else 1))]
  have h2 : ∀ c, ∑ a : Fin 2, alleleWeight p a * (if c ∈ S then ((a : ℕ) : ℝ) else 1) =
      if c ∈ S then p else 1 := by
    intro c; split_ifs <;> simp [alleleWeight, Fin.sum_univ_two]
  simp_rw [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- The founder-allele average of `a_o a_{o'}`: `p` if `o = o'` and `p²` otherwise. -/
private theorem sum_prod_alleleWeight_mul_mul (p : ℝ) (o o' : Fin n × Fin 2) :
    ∑ A : Fin n × Fin 2 → Fin 2,
        (∏ c, alleleWeight p (A c)) * (((A o : ℕ) : ℝ) * ((A o' : ℕ) : ℝ)) =
      p ^ 2 + p * (1 - p) * (if o = o' then 1 else 0) := by
  by_cases h : o = o'
  · subst h
    have hsq : ∀ A : Fin n × Fin 2 → Fin 2,
        ((A o : ℕ) : ℝ) * ((A o : ℕ) : ℝ) = ∏ c ∈ {o}, ((A c : ℕ) : ℝ) := by
      intro A; rw [Finset.prod_singleton, val_mul_self]
    simp_rw [hsq, sum_prod_alleleWeight_mul_prod, Finset.card_singleton]
    simp only [↓reduceIte]; ring
  · have hpair : ∀ A : Fin n × Fin 2 → Fin 2,
        ((A o : ℕ) : ℝ) * ((A o' : ℕ) : ℝ) = ∏ c ∈ {o, o'}, ((A c : ℕ) : ℝ) :=
      fun A => (Finset.prod_pair (f := fun c => ((A c : ℕ) : ℝ)) h).symm
    simp_rw [hpair, sum_prod_alleleWeight_mul_prod, Finset.card_pair h]
    simp [h]

/-- The reference-allele indicator of the gene copy `c` under gene dropping: the allele of the
founder copy from which `c` descends. -/
noncomputable def geneDropAllele (P : Pedigree n) (c : Fin n × Fin 2) (x : GeneDropSpace n) :
    ℝ :=
  ((x.2 (P.origin x.1 c) : ℕ) : ℝ)

/-- Under gene dropping every copy carries the reference allele with probability `p`. -/
theorem integral_geneDropAllele (P : Pedigree n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Fin n × Fin 2) :
    ∫ x, P.geneDropAllele c x ∂(geneDropMeasure p hp0 hp1) = p := by
  refine (integral_geneDropMeasure hp0 hp1 fun ω A => ((A (P.origin ω c) : ℕ) : ℝ)).trans ?_
  have hA : ∀ ω : Coins n,
      ∑ A : Fin n × Fin 2 → Fin 2, (∏ c, alleleWeight p (A c)) * ((A (P.origin ω c) : ℕ) : ℝ)
        = p := by
    intro ω
    simpa using sum_prod_alleleWeight_mul_prod p {P.origin ω c}
  simp only [hA, Finset.sum_const, Finset.card_univ, card_coins', nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0)), one_mul]

/-- **Malécot's second moments under gene dropping**:
`𝔼[a_c a_d] = p² + p (1 - p) ibd c d`, with `ibd` the gene-dropping IBD probability. -/
theorem integral_geneDropAllele_mul (P : Pedigree n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c d : Fin n × Fin 2) :
    ∫ x, P.geneDropAllele c x * P.geneDropAllele d x ∂(geneDropMeasure p hp0 hp1) =
      p ^ 2 + p * (1 - p) * P.ibd c d := by
  refine (integral_geneDropMeasure hp0 hp1 fun ω A =>
    ((A (P.origin ω c) : ℕ) : ℝ) * ((A (P.origin ω d) : ℕ) : ℝ)).trans ?_
  simp only [sum_prod_alleleWeight_mul_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.sum_boole, Finset.card_univ, card_coins', nsmul_eq_mul, ibd]
  push_cast
  field_simp

/-- **Gene dropping realizes Malécot's IBD model**: for a pedigree `P` and a reference-allele
frequency `0 < p < 1`, the allele indicators under gene dropping form an `IBDModel` whose IBD
probabilities are the gene-dropping ones, `P.ibd`. -/
noncomputable def ibdModel (P : Pedigree n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IBDModel (geneDropMeasure (n := n) p hp0.le hp1.le) (Fin n) where
  p := p
  p_pos := hp0
  p_lt_one := hp1
  allele := P.geneDropAllele
  measurable_allele _ := .of_discrete
  allele_mem c x := by
    change ((x.2 (P.origin x.1 c) : ℕ) : ℝ) = 0 ∨ ((x.2 (P.origin x.1 c) : ℕ) : ℝ) = 1
    generalize x.2 (P.origin x.1 c) = a
    fin_cases a <;> simp
  ibd := P.ibd
  integral_allele := P.integral_geneDropAllele hp0.le hp1.le
  integral_allele_mul := P.integral_geneDropAllele_mul hp0.le hp1.le

variable (P : Pedigree n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)

/-- The IBD probabilities of the gene-dropping model are `P.ibd`. -/
theorem ibdModel_ibd : (P.ibdModel p hp0 hp1).ibd = P.ibd := rfl

/-- The kinship coefficient of the gene-dropping model is the gene-dropping kinship. -/
theorem ibdModel_kinship (i j : Fin n) :
    (P.ibdModel p hp0 hp1).kinship i j = P.geneDropKinship i j := rfl

/-- The inbreeding coefficient of the gene-dropping model is the gene-dropping one. -/
theorem ibdModel_inbreeding (i : Fin n) :
    (P.ibdModel p hp0 hp1).inbreeding i = P.inbreeding i := rfl

/-- The kinship coefficient of the gene-dropping model is the tabular kinship. -/
theorem ibdModel_kinship_eq_kinship (i j : Fin n) :
    (P.ibdModel p hp0 hp1).kinship i j = P.kinship i j :=
  P.geneDropKinship_eq_kinship i j

/-- **The GRM is unbiased under pedigree gene dropping**: `𝔼[A_ij] = 2 φ_ij` with `φ` the
gene-dropping kinship. -/
theorem integral_grm_ibdModel (i j : Fin n) :
    ∫ x, (P.ibdModel p hp0 hp1).grm i j x ∂(geneDropMeasure (n := n) p hp0.le hp1.le) =
      2 * P.geneDropKinship i j :=
  (P.ibdModel p hp0 hp1).integral_grm i j

/-- The GRM under pedigree gene dropping is unbiased for twice the tabular kinship. -/
theorem integral_grm_ibdModel_eq_kinship (i j : Fin n) :
    ∫ x, (P.ibdModel p hp0 hp1).grm i j x ∂(geneDropMeasure (n := n) p hp0.le hp1.le) =
      2 * P.kinship i j := by
  rw [integral_grm_ibdModel, geneDropKinship_eq_kinship]

end Pedigree

end MathlibExt.Biology.StatisticalGenetics.Kinship
