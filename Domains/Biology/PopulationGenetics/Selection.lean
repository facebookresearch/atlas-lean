/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Viability selection, Fisher's fundamental theorem, and the Price equation

Discrete-generation selection models on a finite set of types.

* Haploid selection: types `i : ι` with frequencies `p i` (nonnegative, summing to `1`) and
  fitnesses `w i > 0` (expected number of offspring). The next generation has frequencies
  `select p w i = p i * w i / w̄` with mean fitness `w̄ = meanFitness p w = ∑ i, p i * w i`.
* Diploid viability selection under random mating (Hardy–Weinberg proportions at birth): allele
  frequencies `p i` and fitnesses `w i j` of the ordered genotypes `(i, j)` (first and second
  allele). Each survivor transmits each of its two alleles with probability `1/2`, so the next
  generation has allele frequencies
  `diploidSelect p w i = p i * (∑ j, (w i j + w j i) / 2 * p j) / w̄` with
  `w̄ = diploidMeanFitness p w = ∑ i, ∑ j, p i * p j * w i j`; for symmetric fitnesses
  (`w i j = w j i`, the usual unordered genotypes) the marginal fitness is `∑ j, w i j * p j`
  (`marginalFitness_of_symm`).
* The Price equation for a finite population of individuals `i : ι`, each with fitness `w i`
  (number of offspring), trait value `z i`, and mean offspring trait value `z' i`.

## Main results

* `meanFitness_select_sub`: the exact haploid, discrete-generation form of Fisher's
  fundamental theorem of natural selection: `w̄(p') - w̄(p) = Var_p(w) / w̄(p)`. In a haploid
  model all fitness variance is additive. Fisher's diploid statement in terms of the additive
  genetic variance is not covered here.
* `meanFitness_le_meanFitness_select`: mean fitness never decreases under selection.
* `select_nonneg`, `sum_select`, `diploidSelect_nonneg`, `sum_diploidSelect`: both recursions
  map the probability simplex to itself.
* `price`: the Price equation `w̄ (z̄' - z̄) = Cov(w, z) + E[w (z' - z)]`, with population
  (not sample) means and covariance and `z̄' = ∑ w_i z'_i / ∑ w_i`.

## References

* R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon Press, Oxford, 1930.
* G. R. Price, *Selection and covariance*, Nature 227 (1970), 520–521.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Selection

variable {ι : Type*} [Fintype ι]

/-! ### Haploid selection -/

/-- The mean fitness `w̄ = ∑ i, p i * w i` of a population with type frequencies `p` and
fitnesses `w`. -/
def meanFitness (p w : ι → ℝ) : ℝ := ∑ i, p i * w i

/-- The variance of fitness `Var_p(w) = ∑ i, p i * (w i - w̄) ^ 2` under the type frequencies
`p`. -/
def fitnessVariance (p w : ι → ℝ) : ℝ := ∑ i, p i * (w i - meanFitness p w) ^ 2

/-- One generation of haploid selection: `select p w i = p i * w i / w̄`. -/
noncomputable def select (p w : ι → ℝ) (i : ι) : ℝ := p i * w i / meanFitness p w

/-- Fisher's fundamental theorem of natural selection in its exact haploid, discrete-generation
form: the change in mean fitness over one generation of selection is the variance of fitness
divided by the mean fitness, `w̄(p') - w̄(p) = Var_p(w) / w̄(p)` (cf. Fisher 1930, who states the
theorem for the additive genetic variance). The identity needs only `∑ p = 1` and `w̄ ≠ 0`; the
model domain is the simplex with `w > 0` (`meanFitness_pos`). -/
theorem meanFitness_select_sub {p w : ι → ℝ} (hp : ∑ i, p i = 1) (hw : meanFitness p w ≠ 0) :
    meanFitness (select p w) w - meanFitness p w = fitnessVariance p w / meanFitness p w := by
  classical
  have hvar : fitnessVariance p w = (∑ i, p i * w i ^ 2) - meanFitness p w ^ 2 := by
    unfold fitnessVariance
    calc
      (∑ i, p i * (w i - meanFitness p w) ^ 2) =
          ∑ i, (p i * w i ^ 2 - 2 * meanFitness p w * (p i * w i) +
            meanFitness p w ^ 2 * p i) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i * w i ^ 2) - meanFitness p w ^ 2 := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hp]
        change (∑ i, p i * w i ^ 2) - 2 * meanFitness p w * meanFitness p w +
          meanFitness p w ^ 2 * 1 = _
        ring
  have hsel : meanFitness (select p w) w =
      (∑ i, p i * w i ^ 2) / meanFitness p w := by
    change (∑ i, (p i * w i / meanFitness p w) * w i) = _
    rw [sum_div]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsel, hvar]
  field_simp [hw]

/-- Mean fitness is positive on the simplex when every fitness is positive. -/
theorem meanFitness_pos {p w : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (hw : ∀ i, 0 < w i) : 0 < meanFitness p w := by
  classical
  have hpne : (∑ i, p i) ≠ 0 := by rw [hp]; exact one_ne_zero
  obtain ⟨i, hi, hpi⟩ := exists_ne_zero_of_sum_ne_zero hpne
  exact sum_pos' (fun j _ => mul_nonneg (hp0 j) (hw j).le)
    ⟨i, hi, mul_pos (lt_of_le_of_ne (hp0 i) hpi.symm) (hw i)⟩

/-- Mean fitness never decreases under haploid selection (corollary of Fisher's theorem). -/
theorem meanFitness_le_meanFitness_select {p w : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (hw : ∀ i, 0 < w i) : meanFitness p w ≤ meanFitness (select p w) w := by
  have hm := meanFitness_pos hp0 hp hw
  have hv : 0 ≤ fitnessVariance p w :=
    sum_nonneg fun i _ => mul_nonneg (hp0 i) (sq_nonneg _)
  apply le_of_sub_nonneg
  rw [meanFitness_select_sub hp hm.ne']
  exact div_nonneg hv hm.le

/-- Haploid selection keeps frequencies nonnegative. -/
theorem select_nonneg {p w : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (hw : ∀ i, 0 < w i) (i : ι) : 0 ≤ select p w i :=
  div_nonneg (mul_nonneg (hp0 i) (hw i).le) (meanFitness_pos hp0 hp hw).le

/-- Haploid selection keeps the frequencies summing to `1` whenever `w̄ ≠ 0` (for `w̄ = 0`
the division by zero would give `0`). -/
theorem sum_select {p w : ι → ℝ} (hw : meanFitness p w ≠ 0) : ∑ i, select p w i = 1 := by
  simp only [select]
  rw [← Finset.sum_div, ← meanFitness, div_self hw]

/-! ### Diploid viability selection under Hardy–Weinberg proportions -/

/-- The marginal fitness `∑ j, (w i j + w j i) / 2 * p j` of allele `i`: the mean fitness of a
genotype carrying `i` whose other allele is drawn from the frequencies `p`, averaging the two
positions at which `i` can sit in the ordered genotype. -/
noncomputable def marginalFitness (p : ι → ℝ) (w : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, (w i j + w j i) / 2 * p j

/-- For symmetric genotype fitnesses the marginal fitness is the row marginal
`∑ j, w i j * p j`. -/
theorem marginalFitness_of_symm {p : ι → ℝ} {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i)
    (i : ι) : marginalFitness p w i = ∑ j, w i j * p j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hw j i]
  ring

/-- The mean fitness `w̄ = ∑ i, ∑ j, p i * p j * w i j` of a population in Hardy–Weinberg
proportions with allele frequencies `p` and genotype fitnesses `w`. -/
def diploidMeanFitness (p : ι → ℝ) (w : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, p i * p j * w i j

/-- One generation of diploid viability selection under random mating, followed by Mendelian
transmission of either allele of each survivor:
`diploidSelect p w i = p i * (∑ j, (w i j + w j i) / 2 * p j) / w̄`. -/
noncomputable def diploidSelect (p : ι → ℝ) (w : ι → ι → ℝ) (i : ι) : ℝ :=
  p i * marginalFitness p w i / diploidMeanFitness p w

/-- Diploid mean fitness is positive on the simplex when every genotype fitness is positive. -/
theorem diploidMeanFitness_pos {p : ι → ℝ} {w : ι → ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (hw : ∀ i j, 0 < w i j) : 0 < diploidMeanFitness p w := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hp.trans_ne one_ne_zero)
  have hi' : 0 < p i := (hp0 i).lt_of_ne' hi
  have hle : p i * p i * w i i ≤ diploidMeanFitness p w :=
    (Finset.single_le_sum (f := fun j => p i * p j * w i j)
      (fun j _ => mul_nonneg (mul_nonneg (hp0 i) (hp0 j)) (hw i j).le) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, p k * p j * w k j)
        (fun k _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hp0 k) (hp0 j)) (hw k j).le) (Finset.mem_univ i))
  exact (mul_pos (mul_pos hi' hi') (hw i i)).trans_le hle

/-- Diploid viability selection keeps allele frequencies nonnegative. -/
theorem diploidSelect_nonneg {p : ι → ℝ} {w : ι → ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (hw : ∀ i j, 0 < w i j) (i : ι) : 0 ≤ diploidSelect p w i :=
  div_nonneg (mul_nonneg (hp0 i) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (add_nonneg (hw i j).le (hw j i).le) zero_le_two) (hp0 j)))
    (diploidMeanFitness_pos hp0 hp hw).le

/-- Diploid viability selection keeps allele frequencies summing to `1`. -/
theorem sum_diploidSelect {p : ι → ℝ} {w : ι → ι → ℝ} (hw : diploidMeanFitness p w ≠ 0) :
    ∑ i, diploidSelect p w i = 1 := by
  have hs : ∑ i, ∑ j, p i * p j * w j i = diploidMeanFitness p w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h : ∑ i, p i * marginalFitness p w i = diploidMeanFitness p w := by
    have he : ∑ i, p i * marginalFitness p w i =
        (diploidMeanFitness p w + ∑ i, ∑ j, p i * p j * w j i) / 2 := by
      simp only [marginalFitness, diploidMeanFitness, Finset.mul_sum, ← Finset.sum_add_distrib,
        Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [he, hs]
    ring
  simp only [diploidSelect]
  rw [← Finset.sum_div, h, div_self hw]

/-! ### The Price equation -/

/-- The Price equation (exact, finite population). Individual `i` has fitness `w i` (number of
offspring), trait value `z i`, and mean offspring trait value `z' i`. With population means
`w̄ = 𝔼 i, w i`, `z̄ = 𝔼 i, z i` and offspring mean trait `z̄' = ∑ i, w i * z' i / ∑ i, w i`,
`w̄ (z̄' - z̄) = Cov(w, z) + E[w (z' - z)]`, where `Cov` is the population covariance
(Price 1970). Nonnegativity of `w` is not needed; only a nonzero total offspring number. -/
theorem price (w z z' : ι → ℝ) (hw : ∑ i, w i ≠ 0) :
    (𝔼 i, w i) * ((∑ i, w i * z' i) / ∑ i, w i - 𝔼 i, z i) =
      (𝔼 i, (w i - 𝔼 j, w j) * (z i - 𝔼 j, z j)) + 𝔼 i, w i * (z' i - z i) := by
  classical
  obtain ⟨i, _, _⟩ := exists_ne_zero_of_sum_ne_zero hw
  let : Nonempty ι := ⟨i⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Fintype.expect_eq_sum_div_card]
  simp only [sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, card_univ, nsmul_eq_mul]
  field_simp [hw, hn]
  ring

end MathlibExt.Biology.PopulationGenetics.Selection
