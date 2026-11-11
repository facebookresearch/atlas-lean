/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fisher's decomposition of the genetic variance (Fisher 1918)

A single autosomal locus with a finite set `A` of alleles of frequencies `p i` (`0 ≤ p i`,
`∑ p i = 1`) in a randomly mating population in Hardy–Weinberg proportions: the ordered genotype
`(i, j)` (the gene from the sire and the gene from the dam) has frequency `p i * p j`, and its
genotypic value is `G i j`, with `G i j = G j i` (the value of an unordered genotype). We write

* `μ = ∑ p i p j G i j` (`meanValue`), the population mean;
* `α i = ∑ j p j G i j - μ` (`avgEffect`), the average excess of allele `i`, which under
  Hardy–Weinberg proportions is Fisher's average effect: the coefficient of the least-squares
  fit below;
* `δ i j = G i j - μ - α i - α j` (`domDev`), the dominance deviation.

Then `G i j = μ + α i + α j + δ i j`; the additive fitted genotypic value
`μ + α i + α j` is the least-squares fit of the genotypic value by a function additive over
the two genes
(`domVar_le_sum_sq`), the dominance deviations are orthogonal to every additive function, and
the genetic variance splits as

  `V_G = V_A + V_D`, with `V_A = 2 ∑ p i α i ²` and `V_D = ∑ p i p j δ i j ²`.

Covariances between relatives follow from Mendelian transmission under random mating in
Hardy–Weinberg proportions, with unrelated, non-inbred mates: a parent of genotype `(i, j)`
transmits `i` or `j` with probability `1/2` each, independently to each offspring. Then

* parent and offspring: `Cov = V_A / 2`;
* half sibs (one common parent, two unrelated mates): `Cov = V_A / 4`;
* full sibs (two common parents): `Cov = V_A / 2 + V_D / 4`.

The statements are for a single locus. Fisher's extension to many loci, in which the variance
components and the covariances of relatives are sums over loci, requires linkage equilibrium
and no epistasis (no interaction between loci in the genotypic value); it is not formalized
here. Environmental variation is not modeled: the covariances are covariances of genotypic
values.

## Main results

* `genotypicValue_eq`: `G i j = μ + α i + α j + δ i j`.
* `sum_mul_avgEffect`, `sum_mul_domDev_right`, `sum_mul_domDev_left`: orthogonality.
* `domVar_le_sum_sq`: least-squares characterization of the additive fitted genotypic value.
* `genVar_eq_addVar_add_domVar`: `V_G = V_A + V_D`.
* `covParentOffspring_eq`, `covHalfSibs_eq`, `covFullSibs_eq`: covariances of relatives.
* `addVar_biallelic`, `domVar_biallelic`: `V_A = 2pq(a + d(q - p))²` and `V_D = (2pqd)²` for
  two alleles with genotypic values `a, d, -a` (Falconer & Mackay, ch. 7–8).

## References

* R. A. Fisher, *The correlation between relatives on the supposition of Mendelian
  inheritance*, Trans. R. Soc. Edinb. 52 (1918), 399–433.
* D. S. Falconer, T. F. C. Mackay, *Introduction to Quantitative Genetics*, 4th ed., Longman,
  1996, ch. 7–9.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.StatisticalGenetics.FisherDecomposition

variable {A : Type*} [Fintype A]

/-- The mean genotypic value `μ = ∑ i ∑ j p i p j G i j` under Hardy–Weinberg proportions. -/
noncomputable def meanValue (p : A → ℝ) (G : A → A → ℝ) : ℝ := ∑ i, ∑ j, p i * p j * G i j

/-- The average effect of allele `i`, `α i = ∑ j p j G i j - μ`: the mean value of the genotypes
carrying `i` (the other gene drawn from the population) minus the population mean. This is the
average excess; under Hardy–Weinberg proportions it is Fisher's average effect, the coefficient
of the least-squares additive fit (`domVar_le_sum_sq`). -/
noncomputable def avgEffect (p : A → ℝ) (G : A → A → ℝ) (i : A) : ℝ :=
  ∑ j, p j * G i j - meanValue p G

/-- The dominance deviation `δ i j = G i j - μ - α i - α j`. -/
noncomputable def domDev (p : A → ℝ) (G : A → A → ℝ) (i j : A) : ℝ :=
  G i j - meanValue p G - avgEffect p G i - avgEffect p G j

/-- The genetic variance `V_G = ∑ i ∑ j p i p j (G i j - μ) ²`. -/
noncomputable def genVar (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * p j * (G i j - meanValue p G) ^ 2

/-- The additive genetic variance `V_A = 2 ∑ i p i α i ²`, the variance of the breeding value
`α i + α j`. -/
noncomputable def addVar (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  2 * ∑ i, p i * avgEffect p G i ^ 2

/-- The dominance variance `V_D = ∑ i ∑ j p i p j δ i j ²`. -/
noncomputable def domVar (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * p j * domDev p G i j ^ 2

/-- The decomposition `G i j = μ + α i + α j + δ i j` (an identity by definition of `δ`). -/
theorem genotypicValue_eq (p : A → ℝ) (G : A → A → ℝ) (i j : A) :
    G i j = meanValue p G + avgEffect p G i + avgEffect p G j + domDev p G i j := by
  unfold domDev; ring

/-- The average effects have mean zero: `∑ i p i α i = 0`. -/
theorem sum_mul_avgEffect {p : A → ℝ} (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    ∑ i, p i * avgEffect p G i = 0 := by
  have h1 : ∑ i, p i * ∑ j, p j * G i j = meanValue p G := by
    simp only [meanValue, Finset.mul_sum, mul_assoc]
  simp only [avgEffect, mul_sub, Finset.sum_sub_distrib, h1]
  rw [← Finset.sum_mul, hp, one_mul, sub_self]

/-- Summing out one gene: `∑ j p j (G i j - μ) = α i`. -/
private theorem sum_mul_sub_meanValue {p : A → ℝ} (hp : ∑ i, p i = 1) (G : A → A → ℝ) (i : A) :
    ∑ j, p j * (G i j - meanValue p G) = avgEffect p G i := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, avgEffect]

/-- Orthogonality of the dominance deviations: `∑ j p j δ i j = 0` for every `i`. -/
theorem sum_mul_domDev_right {p : A → ℝ} (hp : ∑ i, p i = 1) (G : A → A → ℝ) (i : A) :
    ∑ j, p j * domDev p G i j = 0 := by
  have h := sum_mul_avgEffect hp G
  simp only [domDev, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, h]
  simp only [avgEffect]
  ring

/-- Orthogonality of the dominance deviations for a symmetric genotypic value:
`∑ i p i δ i j = 0` for every `j`. -/
theorem sum_mul_domDev_left {p : A → ℝ} (hp : ∑ i, p i = 1) {G : A → A → ℝ}
    (hG : ∀ i j, G i j = G j i) (j : A) : ∑ i, p i * domDev p G i j = 0 := by
  have h : ∀ i, domDev p G i j = domDev p G j i := fun i => by
    simp only [domDev, hG i j]; ring
  simp only [h]
  exact sum_mul_domDev_right hp G j

/-- **Least squares (Fisher 1918).** Among all fits `c + a i + a j` of the genotypic value by
a function additive over the two genes, the additive fitted genotypic value `μ + α i + α j`
minimizes the weighted squared error `∑ p i p j (G i j - c - a i - a j) ²`; its error is `V_D`. -/
theorem domVar_le_sum_sq {p : A → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    {G : A → A → ℝ} (hG : ∀ i j, G i j = G j i) (c : ℝ) (a : A → ℝ) :
    domVar p G ≤ ∑ i, ∑ j, p i * p j * (G i j - c - a i - a j) ^ 2 := by
  unfold domVar
  set δ := domDev p G
  set e : A → ℝ := fun i => avgEffect p G i - a i
  set k := meanValue p G - c
  have hδr : ∀ i, ∑ j, p j * δ i j = 0 := sum_mul_domDev_right hp G
  have hδl : ∀ j, ∑ i, p i * δ i j = 0 := sum_mul_domDev_left hp hG
  have expand : ∀ i j, p i * p j * (G i j - c - a i - a j) ^ 2 =
      p i * p j * δ i j ^ 2 + 2 * ((p i * e i) * (p j * δ i j)) +
        2 * ((p j * e j) * (p i * δ i j)) + 2 * k * (p i * (p j * δ i j)) +
          p i * p j * (e i + e j + k) ^ 2 := by
    intro i j
    have : G i j - c - a i - a j = δ i j + (e i + e j + k) := by
      simp only [δ, e, k, domDev]; ring
    rw [this]; ring
  have t1 : ∑ i, ∑ j, 2 * ((p i * e i) * (p j * δ i j)) = 0 := by
    simp only [← Finset.mul_sum, hδr, mul_zero, Finset.sum_const_zero]
  have t2 : ∑ i, ∑ j, 2 * ((p j * e j) * (p i * δ i j)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hδl, mul_zero, Finset.sum_const_zero]
  have t3 : ∑ i, ∑ j, 2 * k * (p i * (p j * δ i j)) = 0 := by
    simp only [← Finset.mul_sum, hδr, mul_zero, Finset.sum_const_zero]
  have t4 : 0 ≤ ∑ i, ∑ j, p i * p j * (e i + e j + k) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp0 i) (hp0 j)) (sq_nonneg _)
  simp only [expand, Finset.sum_add_distrib, t1, t2, t3]
  linarith

/-- **Fisher's variance decomposition.** `V_G = V_A + V_D`. -/
theorem genVar_eq_addVar_add_domVar {p : A → ℝ} (hp : ∑ i, p i = 1) {G : A → A → ℝ}
    (hG : ∀ i j, G i j = G j i) : genVar p G = addVar p G + domVar p G := by
  unfold genVar addVar domVar
  set μ := meanValue p G
  set α := avgEffect p G
  set δ := domDev p G
  have hα : ∑ i, p i * α i = 0 := sum_mul_avgEffect hp G
  have hδr : ∀ i, ∑ j, p j * δ i j = 0 := sum_mul_domDev_right hp G
  have hδl : ∀ j, ∑ i, p i * δ i j = 0 := sum_mul_domDev_left hp hG
  have e : ∀ i j, p i * p j * (G i j - μ) ^ 2 =
      p i * (p j * α i ^ 2) + p j * (p i * α j ^ 2) + 2 * ((p i * α i) * (p j * α j)) +
        2 * ((p i * α i) * (p j * δ i j)) + 2 * ((p j * α j) * (p i * δ i j)) +
          p i * p j * δ i j ^ 2 := by
    intro i j
    have : G i j - μ = α i + α j + δ i j := by simp only [μ, α, δ, domDev]; ring
    rw [this]; ring
  have t1 : ∑ i, ∑ j, p i * (p j * α i ^ 2) = ∑ i, p i * α i ^ 2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hp, one_mul]
  have t2 : ∑ i, ∑ j, p j * (p i * α j ^ 2) = ∑ i, p i * α i ^ 2 := by
    rw [Finset.sum_comm]; exact t1
  have t3 : ∑ i, ∑ j, 2 * ((p i * α i) * (p j * α j)) = 0 := by
    simp only [← Finset.mul_sum, hα, mul_zero, Finset.sum_const_zero]
  have t4 : ∑ i, ∑ j, 2 * ((p i * α i) * (p j * δ i j)) = 0 := by
    simp only [← Finset.mul_sum, hδr, mul_zero, Finset.sum_const_zero]
  have t5 : ∑ i, ∑ j, 2 * ((p j * α j) * (p i * δ i j)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hδl, mul_zero, Finset.sum_const_zero]
  simp only [e, Finset.sum_add_distrib, t1, t2, t3, t4, t5]
  ring

/-! ### Covariances between relatives -/

/-- The covariance of the genotypic values of a parent and its offspring: the parent has
genotype `(i, j)` (frequency `p i p j`) and transmits `cond b i j` (each with probability
`1/2`), and the offspring's other gene `k` comes from an unrelated mate (frequency `p k`). -/
noncomputable def covParentOffspring (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ b : Bool, p i * p j * p k / 2 *
    ((G i j - meanValue p G) * (G (cond b i j) k - meanValue p G))

/-- The covariance of the genotypic values of half sibs: the common parent has genotype
`(i, j)` and transmits `cond b i j` to one offspring and, independently, `cond b' i j` to the
other; the second genes `k`, `l` come from two unrelated mates. -/
noncomputable def covHalfSibs (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ b : Bool, ∑ b' : Bool, p i * p j * p k * p l / 4 *
    ((G (cond b i j) k - meanValue p G) * (G (cond b' i j) l - meanValue p G))

/-- The covariance of the genotypic values of full sibs: the sire `(i, j)` and the dam
`(k, l)` are unrelated; the first offspring receives `cond b i j` and `cond e k l`, the second,
independently, `cond b' i j` and `cond e' k l`. -/
noncomputable def covFullSibs (p : A → ℝ) (G : A → A → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ b : Bool, ∑ b' : Bool, ∑ e : Bool, ∑ e' : Bool,
    p i * p j * p k * p l / 16 *
      ((G (cond b i j) (cond e k l) - meanValue p G) *
        (G (cond b' i j) (cond e' k l) - meanValue p G))

/-- **Parent and offspring (Fisher 1918).** `Cov(P, O) = V_A / 2`. -/
theorem covParentOffspring_eq {p : A → ℝ} (hp : ∑ i, p i = 1) {G : A → A → ℝ}
    (hG : ∀ i j, G i j = G j i) : covParentOffspring p G = addVar p G / 2 := by
  unfold covParentOffspring addVar
  set μ := meanValue p G
  set α := avgEffect p G
  have hrow : ∀ i, ∑ j, p j * (G i j - μ) = α i := sum_mul_sub_meanValue hp G
  have hcol : ∀ j, ∑ i, p i * (G i j - μ) = α j := fun j => by
    simp only [hG _ j]; exact hrow j
  have hk : ∀ i j, ∑ k, ∑ b : Bool, p i * p j * p k / 2 *
      ((G i j - μ) * (G (cond b i j) k - μ)) =
        p i * α i / 2 * (p j * (G i j - μ)) + p j * α j / 2 * (p i * (G i j - μ)) := by
    intro i j
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    rw [← hrow i, ← hrow j]
    simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have t1 : ∑ i, ∑ j, p i * α i / 2 * (p j * (G i j - μ)) = ∑ i, p i * α i ^ 2 / 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hrow]; ring
  have t2 : ∑ i, ∑ j, p j * α j / 2 * (p i * (G i j - μ)) = ∑ i, p i * α i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hcol]; ring
  simp only [hk, Finset.sum_add_distrib, t1, t2, ← Finset.sum_div]
  ring

/-- **Half sibs (Fisher 1918).** `Cov(HS) = V_A / 4`. -/
theorem covHalfSibs_eq {p : A → ℝ} (hp : ∑ i, p i = 1) (G : A → A → ℝ) :
    covHalfSibs p G = addVar p G / 4 := by
  unfold covHalfSibs addVar
  set μ := meanValue p G
  set α := avgEffect p G
  have hrow : ∀ i, ∑ j, p j * (G i j - μ) = α i := sum_mul_sub_meanValue hp G
  have hα : ∑ i, p i * α i = 0 := sum_mul_avgEffect hp G
  have hkl : ∀ i j, ∑ k, ∑ l, ∑ b : Bool, ∑ b' : Bool, p i * p j * p k * p l / 4 *
      ((G (cond b i j) k - μ) * (G (cond b' i j) l - μ)) =
        p i * (p j * α i ^ 2) / 4 + p j * (p i * α j ^ 2) / 4 +
          2 * ((p i * α i) * (p j * α j)) / 4 := by
    intro i j
    have e : p i * (p j * α i ^ 2) / 4 + p j * (p i * α j ^ 2) / 4 +
        2 * ((p i * α i) * (p j * α j)) / 4 = p i * p j / 4 * ((α i + α j) * (α i + α j)) := by
      ring
    rw [e, ← hrow i, ← hrow j, ← Finset.sum_add_distrib, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    ring
  have t1 : ∑ i, ∑ j, p i * (p j * α i ^ 2) / 4 = ∑ i, p i * α i ^ 2 / 4 := by
    simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hp, one_mul]
  have t2 : ∑ i, ∑ j, p j * (p i * α j ^ 2) / 4 = ∑ i, p i * α i ^ 2 / 4 := by
    rw [Finset.sum_comm]; exact t1
  have t3 : ∑ i, ∑ j, 2 * ((p i * α i) * (p j * α j)) / 4 = 0 := by
    simp only [← Finset.sum_div, ← Finset.mul_sum, hα, mul_zero, zero_div,
      Finset.sum_const_zero]
  simp only [hkl, Finset.sum_add_distrib]
  rw [t1, t2, t3, ← Finset.sum_div]
  ring

/-- **Full sibs (Fisher 1918).** `Cov(FS) = V_A / 2 + V_D / 4`. -/
theorem covFullSibs_eq {p : A → ℝ} (hp : ∑ i, p i = 1) {G : A → A → ℝ}
    (hG : ∀ i j, G i j = G j i) : covFullSibs p G = addVar p G / 2 + domVar p G / 4 := by
  have hVG := genVar_eq_addVar_add_domVar hp hG
  unfold covFullSibs
  unfold addVar at hVG ⊢
  unfold genVar at hVG
  set μ := meanValue p G
  set α := avgEffect p G
  set X : A → A → ℝ := fun x y => G x y - μ
  have hrow : ∀ i, ∑ j, p j * X i j = α i := sum_mul_sub_meanValue hp G
  have hcol : ∀ j, ∑ i, p i * X i j = α j := fun j => by
    simp only [X, hG _ j]; exact hrow j
  have hα : ∑ i, p i * α i = 0 := sum_mul_avgEffect hp G
  -- summing out the transmitted genes
  have hbool : ∀ i j k l, ∑ b : Bool, ∑ b' : Bool, ∑ e : Bool, ∑ e' : Bool,
      p i * p j * p k * p l / 16 *
        ((G (cond b i j) (cond e k l) - μ) * (G (cond b' i j) (cond e' k l) - μ)) =
      p i * p j * p k * p l / 16 * (X i k + X j k + X i l + X j l) ^ 2 := by
    intro i j k l
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, X]
    ring
  -- summing out the dam's genes `k, l` for a fixed sire `(i, j)`
  have hkl : ∀ i j, ∑ k, ∑ l, p i * p j * p k * p l / 16 * (X i k + X j k + X i l + X j l) ^ 2 =
      p i * p j / 16 * (2 * ∑ k, p k * (X i k + X j k) ^ 2 + 2 * (α i + α j) ^ 2) := by
    intro i j
    have hu : ∑ k, p k * (X i k + X j k) = α i + α j := by
      simp only [mul_add, Finset.sum_add_distrib, hrow]
    have e : ∀ k l, p i * p j * p k * p l / 16 * (X i k + X j k + X i l + X j l) ^ 2 =
        p i * p j / 16 * (p l * (p k * (X i k + X j k) ^ 2) + p k * (p l * (X i l + X j l) ^ 2) +
          2 * ((p k * (X i k + X j k)) * (p l * (X i l + X j l)))) := fun k l => by ring
    simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
    rw [hu]
    ring
  have e2 : ∀ i j,
      p i * p j / 16 * (2 * ∑ k, p k * (X i k + X j k) ^ 2 + 2 * (α i + α j) ^ 2) =
        (p j * ∑ k, p i * p k * X i k ^ 2 + p i * ∑ k, p j * p k * X j k ^ 2 +
          2 * ∑ k, p k * ((p i * X i k) * (p j * X j k)) + p j * (p i * α i ^ 2) +
            p i * (p j * α j ^ 2) + 2 * ((p i * α i) * (p j * α j))) / 8 := by
    intro i j
    have h1 : ∑ k, p k * (X i k + X j k) ^ 2 = ∑ k, p k * X i k ^ 2 + ∑ k, p k * X j k ^ 2 +
        2 * ∑ k, p k * (X i k * X j k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∀ x, ∑ k, p x * p k * X x k ^ 2 = p x * ∑ k, p k * X x k ^ 2 := fun x => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have h4 : ∑ k, p k * ((p i * X i k) * (p j * X j k)) =
        p i * p j * ∑ k, p k * (X i k * X j k) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, h2, h4]
    ring
  have A1 : ∑ i, ∑ j, p j * ∑ k, p i * p k * X i k ^ 2 = ∑ i, ∑ k, p i * p k * X i k ^ 2 := by
    simp only [← Finset.sum_mul, hp, one_mul]
  have A2 : ∑ i, ∑ j, p i * ∑ k, p j * p k * X j k ^ 2 = ∑ i, ∑ k, p i * p k * X i k ^ 2 := by
    rw [Finset.sum_comm]; exact A1
  have A3 : ∑ i, ∑ j, 2 * ∑ k, p k * ((p i * X i k) * (p j * X j k)) =
      2 * ∑ k, p k * α k ^ 2 := by
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcol k, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have A4 : ∑ i, ∑ j, p j * (p i * α i ^ 2) = ∑ i, p i * α i ^ 2 := by
    simp only [← Finset.sum_mul, hp, one_mul]
  have A5 : ∑ i, ∑ j, p i * (p j * α j ^ 2) = ∑ i, p i * α i ^ 2 := by
    rw [Finset.sum_comm]; exact A4
  have A6 : ∑ i, ∑ j, 2 * ((p i * α i) * (p j * α j)) = 0 := by
    simp only [← Finset.mul_sum, hα, mul_zero, Finset.sum_const_zero]
  have hVG' : ∑ i, ∑ k, p i * p k * X i k ^ 2 = 2 * ∑ i, p i * α i ^ 2 + domVar p G := hVG
  simp only [hbool, hkl, e2, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [A1, A2, A3, A4, A5, A6, hVG']
  ring


/-! ### Two alleles -/

/-- Allele frequencies at a biallelic locus: `A₁` (`true`) has frequency `q₁` and `A₂`
(`false`) has frequency `1 - q₁`. -/
def biallelicFreq (q₁ : ℝ) : Bool → ℝ := fun b => if b then q₁ else 1 - q₁

/-- Genotypic values at a biallelic locus on Falconer's scale: `A₁A₁ ↦ a`, `A₁A₂ ↦ d`,
`A₂A₂ ↦ -a` (the origin is the midpoint of the homozygotes). -/
def biallelicValue (a d : ℝ) : Bool → Bool → ℝ := fun b c =>
  if b then (if c then a else d) else (if c then d else -a)

/-- **Additive variance at a biallelic locus (Falconer & Mackay 1996, ch. 8).** With
`p = q₁` and `q = 1 - q₁`, `V_A = 2pq (a + d (q - p)) ²`. An algebraic identity, valid for every
real `q₁`; it is a variance for `0 ≤ q₁ ≤ 1`. -/
theorem addVar_biallelic (q₁ a d : ℝ) :
    addVar (biallelicFreq q₁) (biallelicValue a d) =
      2 * q₁ * (1 - q₁) * (a + d * ((1 - q₁) - q₁)) ^ 2 := by
  simp only [addVar, avgEffect, meanValue, biallelicFreq, biallelicValue, Fintype.sum_bool,
    ite_true, Bool.false_eq_true, ite_false]
  ring

/-- **Dominance variance at a biallelic locus (Falconer & Mackay 1996, ch. 8).**
`V_D = (2pqd) ²`, for every real `q₁`. -/
theorem domVar_biallelic (q₁ a d : ℝ) :
    domVar (biallelicFreq q₁) (biallelicValue a d) = (2 * q₁ * (1 - q₁) * d) ^ 2 := by
  simp only [domVar, domDev, avgEffect, meanValue, biallelicFreq, biallelicValue,
    Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  ring

end MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
