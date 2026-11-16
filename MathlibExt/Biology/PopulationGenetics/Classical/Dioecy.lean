/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import MathlibExt.Biology.PopulationGenetics.HardyWeinberg
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hardy–Weinberg proportions with unequal allele frequencies in the sexes

At an autosomal locus with separate sexes, let the female and male parental
genotype laws be `Gf` and `Gm`. Random mating pairs a random female gamete
with an independent random male gamete. Thus the offspring ordered-genotype
law is `(a, b) ↦ gamete Gf a * gamete Gm b`, and every offspring allele
frequency is the average of its female and male parental frequencies.

Offspring sex is independent of genotype, so this same genotype law applies
to sons and daughters. Random mating in the next generation therefore gives
ordinary Hardy–Weinberg proportions, and they persist thereafter.

At a biallelic locus, the first-generation heterozygote frequency exceeds
`2 p̄ (1 - p̄)`, where `p̄` is the offspring allele frequency, by
`(p_m - p_f)^2 / 2`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, Section I.8.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace MathlibExt.Biology.PopulationGenetics.Classical.Dioecy

/-- **Random union of a female and a male gamete.** If the female gametes have allele law `pf`
and the male gametes allele law `pm`, the offspring ordered genotype (maternal allele, paternal
allele) has law `pf.bind fun c => pm.map (Prod.mk c)`, whose mass at `(a, b)` is
`pf a * pm b`. -/
theorem bind_map_prodMk_apply {A : Type*} (pf pm : PMF A) (a b : A) :
    (pf.bind fun c => pm.map (Prod.mk c)) (a, b) = pf a * pm b := by
  classical
  rw [PMF.bind_apply]
  have h_inner : ∀ c : A, (pm.map (Prod.mk c)) (a, b) =
      if a = c then pm b else 0 := by
    intro c
    rw [PMF.map_apply]
    refine (tsum_eq_single b ?_).trans ?_
    · intro x hxb
      have hne : (a, b) ≠ Prod.mk c x := by
        intro hcon
        have hbx : b = x := congrArg Prod.snd hcon
        exact hxb hbx.symm
      simp [hne]
    · by_cases hac : a = c
      · subst hac
        simp
      · have hne : (a, b) ≠ (c, b) := by
          intro hcon
          exact hac (congrArg Prod.fst hcon)
        simp [hne, hac]
  simp only [h_inner]
  refine (tsum_eq_single a ?_).trans ?_
  · intro c hca
    have hne : ¬(a = c) := Ne.symm hca
    simp [hne]
  · simp

/-- **Averaging the two gamete laws, for arbitrary allele types.** Let
`coin : PMF Bool` be a fair coin. Form ordered offspring genotypes from
independent female and male gamete laws `pf` and `pm`, then transmit one of
the two coordinates of an ordered genotype using `coin`. For every allele
`a` in an arbitrary type `A` (no finiteness assumption), the resulting mass
at `a` is the average `2⁻¹ * pf a + 2⁻¹ * pm a`. This is the PMF-level form
of the two-sex allele-frequency average. -/
theorem gamete_average_apply {A : Type*} (coin : PMF Bool)
    (hcoin : ∀ b, coin b = 2⁻¹) (pf pm : PMF A) (a : A) :
    ((pf.bind fun x => pm.map (Prod.mk x)).bind
        fun g => coin.map fun c => cond c g.1 g.2) a =
      2⁻¹ * pf a + 2⁻¹ * pm a := by
  classical
  have hmap : ∀ (g : A × A) (x : A),
      (pm.map (Prod.mk x)) g = if g.1 = x then pm g.2 else 0 := by
    intro g x
    rw [PMF.map_apply]
    by_cases hx : g.1 = x
    · rw [ite_eq_left hx, tsum_eq_single g.2]
      · exact ite_eq_left (Prod.ext (x := g) (y := (x, g.2)) hx rfl)
      · intro y hy
        apply ite_eq_right
        intro h
        apply hy
        have h2 := congrArg Prod.snd h
        simpa using h2.symm
    · rw [ite_eq_right hx, ENNReal.tsum_eq_zero]
      intro y
      apply ite_eq_right
      intro h
      apply hx
      have h1 := congrArg Prod.fst h
      simpa using h1
  have hinner : ∀ g : A × A,
      (pf.bind fun x => pm.map (Prod.mk x)) g = pf g.1 * pm g.2 := by
    intro g
    rw [PMF.bind_apply]
    simp_rw [hmap, mul_ite, mul_zero]
    rw [tsum_eq_single g.1 (fun x hx => ite_eq_right (Ne.symm hx)), ite_eq_left rfl]
  have houter : ∀ g : A × A,
      (coin.map fun c => cond c g.1 g.2) a =
        (if a = g.1 then (2⁻¹ : ENNReal) else 0) + (if a = g.2 then 2⁻¹ else 0) := by
    intro g
    rw [PMF.map_apply]
    simp_rw [hcoin]
    rw [tsum_fintype, Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
  have hpf : (∑' (x : A) (y : A), (pf x * pm y) * (if a = x then (2⁻¹ : ENNReal) else 0)) =
      2⁻¹ * pf a := by
    have h1 : ∀ x : A, (∑' y : A, (pf x * pm y) * (if a = x then (2⁻¹ : ENNReal) else 0)) =
        pf x * (if a = x then (2⁻¹ : ENNReal) else 0) := by
      intro x
      have hcomm : ∀ y : A, (pf x * pm y) * (if a = x then (2⁻¹ : ENNReal) else 0) =
          (pf x * (if a = x then (2⁻¹ : ENNReal) else 0)) * pm y := by
        intro y
        rw [mul_right_comm]
      simp_rw [hcomm, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    simp_rw [h1, mul_ite, mul_zero]
    rw [tsum_eq_single a (fun x hx => ite_eq_right (Ne.symm hx)), ite_eq_left rfl]
    exact mul_comm _ _
  have hpm : (∑' (x : A) (y : A), (pf x * pm y) * (if a = y then (2⁻¹ : ENNReal) else 0)) =
      2⁻¹ * pm a := by
    have h1 : ∀ x : A, (∑' y : A, (pf x * pm y) * (if a = y then (2⁻¹ : ENNReal) else 0)) =
        pf x * (pm a * 2⁻¹) := by
      intro x
      have hfactor : ∀ y : A, (pf x * pm y) * (if a = y then (2⁻¹ : ENNReal) else 0) =
          pf x * (pm y * (if a = y then (2⁻¹ : ENNReal) else 0)) := by
        intro y
        rw [mul_assoc]
      simp_rw [hfactor, ENNReal.tsum_mul_left]
      congr 1
      simp_rw [mul_ite, mul_zero]
      rw [tsum_eq_single a (fun y hy => ite_eq_right (Ne.symm hy)), ite_eq_left rfl]
    simp_rw [h1, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    exact mul_comm _ _
  rw [PMF.bind_apply]
  simp_rw [hinner, houter, mul_add]
  rw [ENNReal.tsum_add]
  simp only [ENNReal.tsum_prod']
  rw [hpf, hpm]

/-- **First-generation heterozygote excess** at a biallelic autosomal locus. If allele `A` has
frequency `pf` in females and `pm` in males, the offspring heterozygote frequency
`pf * (1 - pm) + pm * (1 - pf)` exceeds the Hardy–Weinberg value `2 p̄ (1 - p̄)` at the
offspring allele frequency `p̄ = (pf + pm) / 2` by `(pm - pf) ^ 2 / 2`. -/
theorem heterozygote_excess_eq (pf pm : ℝ) :
    pf * (1 - pm) + pm * (1 - pf) - 2 * ((pf + pm) / 2) * (1 - (pf + pm) / 2) =
      (pm - pf) ^ 2 / 2 := by
  ring

/-- **The first-generation heterozygote excess is positive exactly when the sexes differ.** -/
theorem heterozygote_excess_pos_iff (pf pm : ℝ) :
    0 < pf * (1 - pm) + pm * (1 - pf) - 2 * ((pf + pm) / 2) * (1 - (pf + pm) / 2) ↔
      pm ≠ pf := by
  rw [heterozygote_excess_eq]
  constructor
  · intro h contra
    subst contra
    simp at h
  · intro h
    have hne : pm - pf ≠ 0 := sub_ne_zero.mpr h
    have hsq : 0 < (pm - pf) ^ 2 := sq_pos_of_ne_zero hne
    exact div_pos hsq (by positivity)

/-! ### Two-sex offspring law in the Hardy–Weinberg API -/

variable {A : Type*}

/-- The offspring ordered-genotype law when female and male parents have
genotype laws `Gf` and `Gm`: an independent female gamete followed by an
independent male gamete. The same law describes sons and daughters. -/
noncomputable def offspring (Gf Gm : PMF (A × A)) : PMF (A × A) :=
  (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf).bind fun c =>
    (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm).map (Prod.mk c)

/-- The two-sex offspring genotype law is the product of the female and male
gamete laws. -/
theorem offspring_apply (Gf Gm : PMF (A × A)) (a b : A) :
    offspring Gf Gm (a, b) =
      MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf a *
        MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm b :=
  bind_map_prodMk_apply _ _ a b

/-- Equal female and male genotype laws recover the ordinary
Hardy–Weinberg offspring law. -/
theorem offspring_self (G : PMF (A × A)) :
    offspring G G =
      MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring G := rfl

/-- The offspring allele frequency is the average of the female and male
parental allele frequencies, for arbitrary allele types. -/
theorem gamete_offspring (Gf Gm : PMF (A × A)) (a : A) :
    MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
        (offspring Gf Gm) a =
      2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf a +
        2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm a := by
  have hcoin : ∀ b, PMF.uniformFintype Bool b = 2⁻¹ := by
    intro b
    simp
  exact gamete_average_apply (PMF.uniformFintype Bool) hcoin _ _ a

/-- In the second generation the genotype law is the Hardy–Weinberg product
of the averaged allele frequencies. -/
theorem offspring_offspring_apply (Gf Gm : PMF (A × A)) (a b : A) :
    MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring
        (offspring Gf Gm) (a, b) =
      (2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf a +
        2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm a) *
        (2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf b +
          2⁻¹ * MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm b) := by
  rw [MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring_apply,
    gamete_offspring, gamete_offspring]

/-- Once Hardy–Weinberg proportions are reached in the second generation,
they persist under further random mating. -/
theorem offspring_offspring_offspring (Gf Gm : PMF (A × A)) :
    MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring
        (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring
          (offspring Gf Gm)) =
      MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring
        (offspring Gf Gm) :=
  MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring_offspring _

/-- The real offspring frequency of allele `A` is the average of the female
and male frequencies. -/
theorem gamete_offspring_true_toReal (Gf Gm : PMF (Bool × Bool)) :
    (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
        (offspring Gf Gm) true).toReal =
      ((MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal +
        (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal) / 2 := by
  have hfin_f : (2⁻¹ : ℝ≥0∞) *
      MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  have hfin_m : (2⁻¹ : ℝ≥0∞) *
      MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  rw [gamete_offspring, ENNReal.toReal_add hfin_f hfin_m, ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  norm_num
  ring

/-- The first-generation heterozygote excess over `2 p̄ (1 - p̄)`, in terms of
the female and male frequencies of allele `A`. -/
theorem offspring_heterozygote_excess (Gf Gm : PMF (Bool × Bool)) :
    (offspring Gf Gm (true, false)).toReal +
        (offspring Gf Gm (false, true)).toReal -
      2 * (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
          (offspring Gf Gm) true).toReal *
        (1 - (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
          (offspring Gf Gm) true).toReal) =
      ((MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal -
        (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal) ^ 2 / 2 := by
  have hf := MathlibExt.Biology.PopulationGenetics.HardyWeinberg.freq_true_add_freq_false Gf
  have hm := MathlibExt.Biology.PopulationGenetics.HardyWeinberg.freq_true_add_freq_false Gm
  have hqf :
      (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf false).toReal =
        1 - (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal := by
    linarith
  have hqm :
      (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm false).toReal =
        1 - (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal := by
    linarith
  have hscalar := heterozygote_excess_eq
    (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal
    (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal
  rw [offspring_apply, offspring_apply, ENNReal.toReal_mul, ENNReal.toReal_mul,
    hqf, hqm, gamete_offspring_true_toReal]
  linear_combination hscalar

/-- The first-generation heterozygote excess is positive exactly when allele
`A` has different frequencies in females and males. -/
theorem offspring_heterozygote_excess_pos_iff (Gf Gm : PMF (Bool × Bool)) :
    0 < (offspring Gf Gm (true, false)).toReal +
        (offspring Gf Gm (false, true)).toReal -
      2 * (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
          (offspring Gf Gm) true).toReal *
        (1 - (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete
          (offspring Gf Gm) true).toReal) ↔
      (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal ≠
        (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal := by
  rw [offspring_heterozygote_excess]
  constructor
  · intro h hcontra
    rw [hcontra] at h
    simp at h
  · intro h
    have hne :
        (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gm true).toReal -
            (MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete Gf true).toReal ≠ 0 :=
      sub_ne_zero.mpr h
    exact div_pos (sq_pos_of_ne_zero hne) (by positivity)

end MathlibExt.Biology.PopulationGenetics.Classical.Dioecy
