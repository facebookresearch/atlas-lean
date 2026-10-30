/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Basic.Real.Basic

/-!
# The Hardy–Weinberg law

Random mating at a single autosomal locus with alleles in a type `A`. A genotype is an ordered
pair `g : A × A` of a maternal and a paternal allele, and the parental generation has genotype
law `G : PMF (A × A)`. Mendel's law of segregation (`transmit`): a parent with genotype `g`
transmits each of its two alleles with probability `1/2`, i.e. `½ δ_{g.1} + ½ δ_{g.2}`. A random
gamete of the parental generation therefore has law `gamete G = G.bind transmit`, whose mass at
`a` is the allele frequency `½ ∑ b, G (a, b) + ½ ∑ b, G (b, a)` (`gamete_apply`). Under random
union of gametes the offspring genotype is a pair of independent gametes (`offspring`).

## Main results

* `offspring_apply`: Hardy–Weinberg proportions in one generation, the offspring genotype law
  is the product `p ⊗ p` of the parental allele frequencies `p = gamete G`.
* `gamete_offspring`: allele frequencies are conserved.
* `offspring_offspring`: Hardy–Weinberg proportions are an equilibrium.
* Two alleles (`A = Bool`, `true` = allele `A` with frequency `p`, `false` = allele `a` with
  frequency `q = 1 - p`): `freq_true_add_freq_false`, `offspring_true_true`
  (`P(AA) = p²`), `offspring_false_false` (`P(aa) = q²`), `offspring_heterozygote`
  (`P(Aa) = 2pq` for the unordered heterozygote), and `hwDeviation_offspring`: the deviation
  `D = P(AA) - p²` from Hardy–Weinberg proportions is `0` after one generation of random mating.

The model is the classical one: an infinite population, discrete generations, random mating,
and no selection, mutation, migration or drift. Sex-linked loci and unequal allele
frequencies in the two sexes are not covered.

## References

* G. H. Hardy, *Mendelian proportions in a mixed population*, Science 28 (1908), 49–50.
* W. Weinberg, *Über den Nachweis der Vererbung beim Menschen*, Jahreshefte des Vereins für
  vaterländische Naturkunde in Württemberg 64 (1908), 368–382.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer, 2004, Chapter 1.
-/

@[expose] public section

open scoped ENNReal

namespace MathlibExt.Biology.PopulationGenetics.HardyWeinberg

variable {A : Type*}

/-- Mendel's law of segregation: a parent with genotype `g` transmits its maternal allele `g.1`
or its paternal allele `g.2`, each with probability `1/2`. -/
noncomputable def transmit (g : A × A) : PMF A :=
  (PMF.uniformFintype Bool).map fun b => cond b g.1 g.2

/-- The law of a random gamete of a generation with genotype law `G`: pick a parent from `G`,
then one of its two alleles by `transmit`. Its mass at `a` is the frequency of allele `a`
(`gamete_apply`). -/
noncomputable def gamete (G : PMF (A × A)) : PMF A := G.bind transmit

/-- The offspring genotype law under random union of gametes: the maternal and paternal
alleles are independent gametes of the parental generation. -/
noncomputable def offspring (G : PMF (A × A)) : PMF (A × A) :=
  (gamete G).bind fun a => (gamete G).map (Prod.mk a)

/-- `transmit g` puts mass `1/2` on each of the two alleles of `g` (mass `1` on `a` for a
homozygote `g = (a, a)`). -/
theorem transmit_apply [DecidableEq A] (g : A × A) (a : A) :
    transmit g a = (if g.1 = a then 2⁻¹ else 0) + (if g.2 = a then 2⁻¹ else 0) := by
  simp only [transmit, PMF.map_apply, tsum_fintype, Fintype.sum_bool, Bool.cond_true,
    Bool.cond_false, PMF.uniformFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
  congr 1 <;> split_ifs <;> simp_all [eq_comm]

/-- The gamete law is the allele frequency: `gamete G a = ½ ∑ b, G (a, b) + ½ ∑ b, G (b, a)`,
half the expected number of copies of `a` in a parental genotype. -/
theorem gamete_apply [Fintype A] (G : PMF (A × A)) (a : A) :
    gamete G a = 2⁻¹ * ∑ b, G (a, b) + 2⁻¹ * ∑ b, G (b, a) := by
  classical
  simp only [gamete, PMF.bind_apply, tsum_fintype, transmit_apply, mul_add, mul_ite, mul_zero,
    Finset.sum_add_distrib, Fintype.sum_prod_type]
  rw [Finset.sum_comm (f := fun x y => if (x, y).2 = a then G (x, y) * 2⁻¹ else 0)]
  simp [Finset.mul_sum, mul_comm]

/-- **Hardy–Weinberg proportions** (Hardy 1908, Weinberg 1908): after one generation of random
mating the genotype law is the product `p ⊗ p` of the parental allele frequencies
`p = gamete G`. -/
theorem offspring_apply (G : PMF (A × A)) (a b : A) :
    offspring G (a, b) = gamete G a * gamete G b := by
  classical
  rw [offspring, PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro c hc
      simp [Ne.symm hc]
  · intro c hc
    rw [PMF.map_apply]
    simp [Ne.symm hc]

/-- **Allele frequencies are conserved** under random mating: the gamete law of the offspring
equals that of the parents. -/
theorem gamete_offspring (G : PMF (A × A)) : gamete (offspring G) = gamete G := by
  set p := gamete G
  have key : ∀ a b : A,
      transmit (a, b) = (PMF.uniformFintype Bool).bind fun c => PMF.pure (cond c a b) := by
    intro a b
    rfl
  have h1 : ∀ a : A, (p.bind fun b => (PMF.uniformFintype Bool).bind fun c =>
      PMF.pure (cond c a b)) = (PMF.uniformFintype Bool).bind fun c =>
        p.bind fun b => PMF.pure (cond c a b) := fun a => PMF.bind_comm _ _ _
  calc gamete (offspring G)
      = p.bind fun a => p.bind fun b => transmit (a, b) := by
        change (p.bind fun a => p.map (Prod.mk a)).bind transmit = _
        rw [PMF.bind_bind]
        congr 1
        funext a
        rw [PMF.bind_map]
        rfl
    _ = (PMF.uniformFintype Bool).bind fun c =>
          p.bind fun a => p.bind fun b => PMF.pure (cond c a b) := by
        simp only [key, h1]
        exact PMF.bind_comm _ _ _
    _ = (PMF.uniformFintype Bool).bind fun _ => p := by
        congr 1
        funext c
        cases c
        · simp [PMF.bind_const, PMF.bind_pure]
        · simp [PMF.bind_const, PMF.bind_pure]
    _ = p := PMF.bind_const _ _

/-- **Hardy–Weinberg equilibrium**: the Hardy–Weinberg proportions reached after one generation
of random mating are a fixed point of random mating. -/
theorem offspring_offspring (G : PMF (A × A)) : offspring (offspring G) = offspring G := by
  rw [offspring, gamete_offspring, ← offspring]

/-! ### Two alleles

Alleles are `Bool`: `true` is allele `A` with frequency `p = (gamete G true).toReal` and
`false` is allele `a` with frequency `q = (gamete G false).toReal`. -/

/-- The two allele frequencies sum to one: `p + q = 1`. -/
theorem freq_true_add_freq_false (G : PMF (Bool × Bool)) :
    (gamete G true).toReal + (gamete G false).toReal = 1 := by
  have h := (gamete G).tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at h
  rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), h, ENNReal.toReal_one]

/-- After one generation of random mating the homozygote `AA` has frequency `p²`. -/
theorem offspring_true_true (G : PMF (Bool × Bool)) :
    (offspring G (true, true)).toReal = (gamete G true).toReal ^ 2 := by
  rw [offspring_apply, ENNReal.toReal_mul, sq]

/-- After one generation of random mating the homozygote `aa` has frequency `q²`. -/
theorem offspring_false_false (G : PMF (Bool × Bool)) :
    (offspring G (false, false)).toReal = (gamete G false).toReal ^ 2 := by
  rw [offspring_apply, ENNReal.toReal_mul, sq]

/-- After one generation of random mating the (unordered) heterozygote `Aa`, i.e. the two
ordered genotypes `(A, a)` and `(a, A)`, has frequency `2pq`. -/
theorem offspring_heterozygote (G : PMF (Bool × Bool)) :
    (offspring G (true, false)).toReal + (offspring G (false, true)).toReal =
      2 * (gamete G true).toReal * (gamete G false).toReal := by
  rw [offspring_apply, offspring_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

/-- The deviation `D = P(AA) - p²` of a biallelic genotype law from Hardy–Weinberg
proportions, where `p` is the frequency of allele `A` (`true`). -/
noncomputable def hwDeviation (G : PMF (Bool × Bool)) : ℝ :=
  (G (true, true)).toReal - (gamete G true).toReal ^ 2

/-- The deviation from Hardy–Weinberg proportions vanishes after one generation of random
mating, whatever the parental genotype law. -/
theorem hwDeviation_offspring (G : PMF (Bool × Bool)) : hwDeviation (offspring G) = 0 := by
  rw [hwDeviation, gamete_offspring, offspring_true_true, sub_self]

end MathlibExt.Biology.PopulationGenetics.HardyWeinberg
