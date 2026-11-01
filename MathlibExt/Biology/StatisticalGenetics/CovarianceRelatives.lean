/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Fisher's decomposition, the covariance between relatives, and phantom heritability

**One locus (proved).** A locus with a finite set of alleles `A`, allele frequencies `p`, and
symmetric genotypic values `g a b`, under random union of gametes (Hardy–Weinberg). Fisher's
average effects `α a = E[g(a, B)] - μ` and dominance deviations
`δ a b = g a b - μ - α a - α b` give the orthogonal decomposition `V_G = V_A + V_D` with
`V_A = 2 E α²` and `V_D = E δ²`, and the additive part is the least-squares additive fit.
The one-locus Fisher identities below (centring, orthogonality, V_G = V_A + V_D,
least squares) are the bundled-model specializations of FisherDecomposition;
this file proves only the genuinely new IBD and phantom-heritability results on top.

Two relatives that share `0`, `1`, or `2` alleles identical by descent with probabilities
`k₀, k₁, k₂` (non-inbred, `k₀ + k₁ + k₂ = 1`) have genetic covariance
`(k₁ / 2 + k₂) V_A + k₂ V_D = 2φ V_A + Δ V_D`.

**Many loci (algebra on a stated representation).** Cockerham's and Kempthorne's extension
writes the covariance between non-inbred relatives in a random-mating population at linkage
equilibrium as `∑_{i + j ≥ 1} (2φ)^i Δ^j V_{A^i D^j}` with nonnegative components. This file
does **not** prove that representation for many loci; it takes the representation itself as an
explicit hypothesis, bundled in `CockerhamComponents`: finitely supported components
(`V_supported`: components above order `n` vanish, so the `cov` sum over `i, j ≤ n` is the
whole representation), nonnegativity, and no `(0, 0)` component. The downstream API is
qualified accordingly: every many-locus statement is a statement about a
`CockerhamComponents` witness, i.e. conditional on that representation holding. It proves
what follows from it: Falconer's twin estimator
`2 (r_MZ - r_DZ)` (the ACE-model population heritability of Zuk et al.) is at least the
narrow-sense heritability `V_A / V_P`, with equality iff every non-additive component
vanishes. The coefficient `2 (1 - 2^{-i} 4^{-j})` of each component in that estimator is
derived here from Cockerham's formula (it is not printed in the cited sources). For one locus
the representation is proved (`relCov_eq`), so the one-locus phantom statement
(`falconer_eq_of_locus`) is unconditional.

## Main results

* `LocusModel.varG_eq`: **Fisher's decomposition** `V_G = V_A + V_D`.
* `LocusModel.sum_p_alpha`, `LocusModel.sum_p_delta`: average effects are centred and
  dominance deviations are orthogonal to every allele.
* `LocusModel.varD_le`: the additive fit `μ + α a + α b` minimizes the mean squared error among
  all additive fits `c + h a + h b`.
* `LocusModel.relCov_eq`: **covariance between relatives**
  `Cov = (k₁ / 2 + k₂) V_A + k₂ V_D`.
* `CockerhamComponents.falconer_eq`, `CockerhamComponents.varA_le_falconer`,
  `CockerhamComponents.falconer_eq_varA_iff`: `2 (Cov_MZ - Cov_DZ)` equals `V_A` plus a
  positive combination of the non-additive components; it is `≥ V_A`, with equality iff they
  all vanish; a shared environment common to both twin types cancels.
* `CockerhamComponents.narrow_le_falconerHeritability`: the phantom-heritability inequality
  `h² ≤ 2 (r_MZ - r_DZ)` on the correlation scale.

## References

* R. A. Fisher, *The correlation between relatives on the supposition of Mendelian
  inheritance*, Trans. Roy. Soc. Edinburgh 52 (1918), 399–433.
* C. C. Cockerham, *An extension of the concept of partitioning hereditary variance for
  analysis of covariances among relatives when epistasis is present*, Genetics 39 (1954),
  859–882.
* O. Kempthorne, *The correlation between relatives in a random mating population*,
  Proc. Roy. Soc. B 143 (1954), 103–113.
* D. S. Falconer, T. F. C. Mackay, *Introduction to Quantitative Genetics*, 4th ed., Longman
  (1996), ch. 7–9.
* O. Zuk, E. Hechter, S. R. Sunyaev, E. S. Lander, *The mystery of missing heritability:
  Genetic interactions create phantom heritability*, PNAS 109 (2012), 1193–1198.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.StatisticalGenetics.CovarianceRelatives

/-- A single locus under random union of gametes: allele frequencies `p` on a finite allele
set and symmetric genotypic values `g a b` (the mean phenotype of genotype `{a, b}`). -/
structure LocusModel (A : Type*) [Fintype A] where
  /-- Allele frequencies. -/
  p : A → ℝ
  p_nonneg : ∀ a, 0 ≤ p a
  sum_p : ∑ a, p a = 1
  /-- Genotypic values. -/
  g : A → A → ℝ
  g_symm : ∀ a b, g a b = g b a

namespace LocusModel

variable {A : Type*} [Fintype A] (m : LocusModel A)

/-- The population mean genotypic value `μ = ∑ p_a p_b g(a, b)`. -/
def mean : ℝ := ∑ a, ∑ b, m.p a * m.p b * m.g a b

/-- Fisher's average effect of allele `a`: `α a = ∑_b p_b g(a, b) - μ`. -/
def alpha (a : A) : ℝ := ∑ b, m.p b * m.g a b - m.mean

/-- The dominance deviation `δ a b = g(a, b) - μ - α a - α b`. -/
def delta (a b : A) : ℝ := m.g a b - m.mean - m.alpha a - m.alpha b

/-- The genetic variance `V_G = ∑ p_a p_b (g(a, b) - μ)²`. -/
def varG : ℝ := ∑ a, ∑ b, m.p a * m.p b * (m.g a b - m.mean) ^ 2

/-- The additive variance `V_A = 2 ∑ p_a α_a²`. -/
def varA : ℝ := 2 * ∑ a, m.p a * m.alpha a ^ 2

/-- The dominance variance `V_D = ∑ p_a p_b δ_{ab}²`. -/
def varD : ℝ := ∑ a, ∑ b, m.p a * m.p b * m.delta a b ^ 2

/-- Average effects are centred: `∑ p_a α_a = 0`. -/
theorem sum_p_alpha : ∑ a, m.p a * m.alpha a = 0 := by
  simpa only [alpha, mean, FisherDecomposition.avgEffect, FisherDecomposition.meanValue]
    using FisherDecomposition.sum_mul_avgEffect m.sum_p m.g

/-- Dominance deviations are orthogonal to every allele: `∑_b p_b δ_{ab} = 0`. -/
theorem sum_p_delta (a : A) : ∑ b, m.p b * m.delta a b = 0 := by
  simpa only [delta, alpha, mean, FisherDecomposition.domDev, FisherDecomposition.avgEffect,
    FisherDecomposition.meanValue]
    using FisherDecomposition.sum_mul_domDev_right m.sum_p m.g a

private def expect {A : Type*} [Fintype A] (m : LocusModel A)
    (f : A → A → ℝ) : ℝ := ∑ a, ∑ b, m.p a * m.p b * f a b

private theorem expect_add {A : Type*} [Fintype A] (m : LocusModel A)
    (f h : A → A → ℝ) :
    expect m (fun a b ↦ f a b + h a b) = expect m f + expect m h := by
  simp only [expect, mul_add, sum_add_distrib]

private theorem expect_mul {A : Type*} [Fintype A] (m : LocusModel A)
    (r : ℝ) (f : A → A → ℝ) :
    expect m (fun a b ↦ r * f a b) = r * expect m f := by
  simp only [expect, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

private theorem expect_product {A : Type*} [Fintype A] (m : LocusModel A)
    (f h : A → ℝ) :
    expect m (fun a b ↦ f a * h b) = (∑ a, m.p a * f a) * ∑ b, m.p b * h b := by
  unfold expect
  rw [sum_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

private theorem expect_left {A : Type*} [Fintype A] (m : LocusModel A)
    (f : A → ℝ) : expect m (fun a _ ↦ f a) = ∑ a, m.p a * f a := by
  have := expect_product m f (fun _ ↦ 1)
  simpa [m.sum_p] using this

private theorem expect_right {A : Type*} [Fintype A] (m : LocusModel A)
    (f : A → ℝ) : expect m (fun _ b ↦ f b) = ∑ b, m.p b * f b := by
  have := expect_product m (fun _ ↦ 1) f
  simpa [m.sum_p] using this

private theorem expect_const {A : Type*} [Fintype A] (m : LocusModel A)
    (r : ℝ) : expect m (fun _ _ ↦ r) = r := by
  rw [expect_left]
  simp only [← sum_mul, m.sum_p, one_mul]

/-- **Fisher decomposition** of the genetic variance: `V_G = V_A + V_D`. -/
theorem varG_eq : m.varG = m.varA + m.varD := by
  simpa only [varG, varA, varD, mean, alpha, delta, FisherDecomposition.genVar,
    FisherDecomposition.addVar, FisherDecomposition.domVar, FisherDecomposition.meanValue,
    FisherDecomposition.avgEffect, FisherDecomposition.domDev]
    using FisherDecomposition.genVar_eq_addVar_add_domVar m.sum_p m.g_symm

/-- The additive variance is nonnegative. -/
theorem varA_nonneg : 0 ≤ m.varA := by
  exact mul_nonneg (by norm_num) (sum_nonneg fun a _ ↦
    mul_nonneg (m.p_nonneg a) (sq_nonneg _))

/-- The dominance variance is nonnegative. -/
theorem varD_nonneg : 0 ≤ m.varD := by
  exact sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦
    mul_nonneg (mul_nonneg (m.p_nonneg a) (m.p_nonneg b)) (sq_nonneg _)

/-- **The additive fit is least squares** (Fisher definition of average effects): every
additive fit `c + h a + h b` has mean squared error at least `V_D`, the error of
`μ + α a + α b`. -/
theorem varD_le (c : ℝ) (h : A → ℝ) :
    m.varD ≤ ∑ a, ∑ b, m.p a * m.p b * (m.g a b - c - h a - h b) ^ 2 := by
  simpa only [varD, delta, alpha, mean, FisherDecomposition.domVar,
    FisherDecomposition.domDev, FisherDecomposition.avgEffect, FisherDecomposition.meanValue]
    using FisherDecomposition.domVar_le_sum_sq m.p_nonneg m.sum_p m.g_symm c h

/-- The mean product of genotypic values of two non-inbred relatives that share `0`, `1`, `2`
alleles identical by descent with probabilities `k₀, k₁, k₂`: given the IBD state, the
non-shared alleles are independent draws from `p`. -/
def relProd (k₀ k₁ k₂ : ℝ) : ℝ :=
  k₀ * (∑ a, ∑ b, ∑ c, ∑ d, m.p a * m.p b * m.p c * m.p d * (m.g a b * m.g c d)) +
  k₁ * (∑ a, ∑ b, ∑ c, m.p a * m.p b * m.p c * (m.g a b * m.g a c)) +
  k₂ * (∑ a, ∑ b, m.p a * m.p b * (m.g a b * m.g a b))

private theorem product_zero_ibd {A : Type*} [Fintype A] (m : LocusModel A) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      m.p a * m.p b * m.p c * m.p d * (m.g a b * m.g c d)) = m.mean ^ 2 := by
  unfold mean
  rw [pow_two, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [sum_mul]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro c _
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  ring

private theorem product_one_ibd {A : Type*} [Fintype A] (m : LocusModel A) :
    (∑ a, ∑ b, ∑ c, m.p a * m.p b * m.p c * (m.g a b * m.g a c)) =
      m.mean ^ 2 + m.varA / 2 := by
  have factor :
      (∑ a, ∑ b, ∑ c, m.p a * m.p b * m.p c * (m.g a b * m.g a c)) =
      ∑ a, m.p a * (m.mean + m.alpha a) ^ 2 := by
    unfold alpha
    simp only [add_sub_cancel]
    apply sum_congr rfl
    intro a _
    rw [pow_two, sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro c _
    ring
  rw [factor]
  calc
    (∑ a, m.p a * (m.mean + m.alpha a) ^ 2) =
        ∑ a, (m.mean ^ 2 * m.p a + 2 * m.mean * (m.p a * m.alpha a) +
          m.p a * m.alpha a ^ 2) := by
      apply sum_congr rfl
      intro a _
      ring
    _ = m.mean ^ 2 + m.varA / 2 := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
        m.sum_p, m.sum_p_alpha]
      unfold varA
      ring

private theorem product_two_ibd {A : Type*} [Fintype A] (m : LocusModel A) :
    (∑ a, ∑ b, m.p a * m.p b * (m.g a b * m.g a b)) =
      m.mean ^ 2 + m.varG := by
  have expansion : m.varG = expect m (fun a b ↦ m.g a b * m.g a b) +
      (-2 * m.mean) * expect m m.g + expect m (fun _ _ ↦ m.mean ^ 2) := by
    rw [← expect_mul, ← expect_add, ← expect_add]
    unfold varG expect
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  rw [expect_const] at expansion
  change m.varG = _ + (-2 * m.mean) * m.mean + _ at expansion
  change expect m (fun a b ↦ m.g a b * m.g a b) = _
  linarith

/-- **Covariance between relatives** at one locus (Fisher 1918; in the IBD form of Falconer and
Mackay ch. 9): for IBD probabilities summing to one,
`E[G_X G_Y] - μ² = (k₁ / 2 + k₂) V_A + k₂ V_D`, i.e. `2φ V_A + Δ V_D` with kinship
`φ = k₁ / 4 + k₂ / 2` and `Δ = k₂`. -/
theorem relCov_eq {k₀ k₁ k₂ : ℝ} (hk : k₀ + k₁ + k₂ = 1) :
    m.relProd k₀ k₁ k₂ - m.mean ^ 2 = (k₁ / 2 + k₂) * m.varA + k₂ * m.varD := by
  unfold relProd
  rw [product_zero_ibd, product_one_ibd, product_two_ibd, m.varG_eq]
  nlinarith [congrArg (fun r : ℝ ↦ r * m.mean ^ 2) hk]

end LocusModel

/-- Cockerham–Kempthorne variance components up to order `n`: `V i j = V_{A^i D^j}` is the
component of `i` additive and `j` dominance factors (`V 1 0 = V_A`, `V 0 1 = V_D`,
`V 2 0 = V_AA`, …). They are nonnegative, there is no `(0, 0)` component, and the genetic
covariance of relatives with `2φ` and `Δ` is `∑_{i, j ≤ n} (2φ)^i Δ^j V i j`. This structure
is the stated representation; it is proved for one locus by `LocusModel.relCov_eq`. -/
structure CockerhamComponents where
  /-- Highest order kept. -/
  n : ℕ
  /-- The components `V_{A^i D^j}`. -/
  V : ℕ → ℕ → ℝ
  V_nonneg : ∀ i j, 0 ≤ V i j
  V_zero_zero : V 0 0 = 0
  /-- Finite support: components above order `n` vanish. `V` is total only as a function;
  there are no unconstrained ignored components outside the summation range of `cov`, which
  sums exactly over `i, j ≤ n`. -/
  V_supported : ∀ i j, n < i ∨ n < j → V i j = 0

namespace CockerhamComponents

variable (c : CockerhamComponents)

/-- The genetic covariance of relatives with coefficients `2φ = twoPhi` and `Δ = Δ`. -/
def cov (twoPhi Δ : ℝ) : ℝ :=
  ∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1), twoPhi ^ i * Δ ^ j * c.V i j

/-- The additive variance `V_A = V 1 0` (zero if `n = 0`). -/
def varA : ℝ := if 1 ≤ c.n then c.V 1 0 else 0

/-- **Falconer's estimator** under the ACE model, in covariance form: monozygotic twins have
`2φ = Δ = 1`, dizygotic twins (full sibs) `2φ = 1/2`, `Δ = 1/4`, and both share the same
common-environment covariance `C`; the estimator is `2 (Cov_MZ - Cov_DZ)`. -/
noncomputable def falconer (C : ℝ) : ℝ := 2 * ((c.cov 1 1 + C) - (c.cov (1 / 2) (1 / 4) + C))

/-- Falconer's estimator is `V_A` plus the non-additive components weighted by
`2 (1 - 2^{-i} 4^{-j})` (derived from Cockerham's coefficients). -/
theorem falconer_eq (C : ℝ) :
    c.falconer C = c.varA + ∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1),
      (if (i, j) = (1, 0) then 0 else 2 * (1 - (1 / 2) ^ i * (1 / 4) ^ j) * c.V i j) := by
  classical
  have full : c.falconer C = ∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1),
      2 * (1 - (1 / 2) ^ i * (1 / 4) ^ j) * c.V i j := by
    unfold falconer cov
    simp only [one_pow, one_mul]
    rw [show (∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1), c.V i j) + C -
        ((∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1),
          (1 / 2) ^ i * (1 / 4) ^ j * c.V i j) + C) =
        (∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1), c.V i j) -
        (∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1),
          (1 / 2) ^ i * (1 / 4) ^ j * c.V i j) by ring]
    rw [← sum_sub_distrib]
    simp only [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have extracted :
      (∑ i ∈ range (c.n + 1), ∑ j ∈ range (c.n + 1),
        if (i, j) = (1, 0) then c.V i j else 0) = c.varA := by
    simp only [Prod.mk.injEq]
    simp_rw [ite_and]
    simp [sum_ite_irrel, varA, Nat.succ_le_iff]
  rw [full, ← extracted, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h : (i, j) = (1, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    norm_num
  · simp [h]

private theorem coefficient_nonneg (i j : ℕ) :
    0 ≤ 2 * (1 - (1 / 2 : ℝ) ^ i * (1 / 4 : ℝ) ^ j) := by
  have hi : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hj : (1 / 4 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h : (1 / 2 : ℝ) ^ i * (1 / 4 : ℝ) ^ j ≤ 1 :=
    (mul_le_mul_of_nonneg_right hi (pow_nonneg (by norm_num) j)).trans
      (by simpa only [one_mul] using hj)
  linarith

private theorem coefficient_bound (i j : ℕ) (h00 : (i, j) ≠ (0, 0))
    (h10 : (i, j) ≠ (1, 0)) :
    3 / 2 ≤ 2 * (1 - (1 / 2 : ℝ) ^ i * (1 / 4 : ℝ) ^ j) := by
  have hi : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  cases j with
  | zero =>
    cases i with
    | zero => exact (h00 rfl).elim
    | succ i =>
      cases i with
      | zero => exact (h10 rfl).elim
      | succ i =>
        have h : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        simp only [pow_zero, mul_one, pow_succ]
        nlinarith
  | succ j =>
    have h : (1 / 2 : ℝ) ^ i * (1 / 4 : ℝ) ^ j ≤ 1 :=
      (mul_le_mul_of_nonneg_right hi (pow_nonneg (by norm_num) j)).trans
        (by simpa only [one_mul] using
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) :
            (1 / 4 : ℝ) ^ j ≤ 1))
    rw [pow_succ]
    nlinarith

private theorem remainder_nonneg (c : CockerhamComponents) (i j : ℕ) :
    0 ≤ (if (i, j) = (1, 0) then 0 else
      2 * (1 - (1 / 2) ^ i * (1 / 4) ^ j) * c.V i j) := by
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (coefficient_nonneg i j) (c.V_nonneg i j)

/-- The phantom-heritability inequality in covariance form: `V_A ≤ 2 (Cov_MZ - Cov_DZ)`. -/
theorem varA_le_falconer (C : ℝ) : c.varA ≤ c.falconer C := by
  rw [c.falconer_eq]
  exact le_add_of_nonneg_right (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦
    remainder_nonneg c i j)

/-- Equality holds iff every non-additive component of order `≤ n` vanishes. -/
theorem falconer_eq_varA_iff (C : ℝ) :
    c.falconer C = c.varA ↔
      ∀ i ∈ range (c.n + 1), ∀ j ∈ range (c.n + 1), (i, j) ≠ (1, 0) → c.V i j = 0 := by
  classical
  rw [c.falconer_eq, add_eq_left]
  constructor
  · intro hz i hi j hj h10
    have row := (sum_eq_zero_iff_of_nonneg (fun i _ ↦
      sum_nonneg fun j _ ↦ remainder_nonneg c i j)).mp hz i hi
    have term := (sum_eq_zero_iff_of_nonneg (fun j _ ↦
      remainder_nonneg c i j)).mp row j hj
    rw [ite_eq_right h10] at term
    by_cases h00 : (i, j) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h00
      exact c.V_zero_zero
    · have hp : 0 < 2 * (1 - (1 / 2 : ℝ) ^ i * (1 / 4 : ℝ) ^ j) :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (coefficient_bound i j h00 h10)
      exact (mul_eq_zero.mp term).resolve_left (ne_of_gt hp)
  · intro h
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    by_cases h10 : (i, j) = (1, 0)
    · rw [ite_eq_left h10]
    · rw [ite_eq_right h10, h i hi j hj h10, mul_zero]

/-- **Phantom heritability** on the correlation scale (Zuk et al. 2012): with phenotypic
variance `V_P > 0`, the narrow-sense heritability `V_A / V_P` is at most the ACE estimate
`2 (r_MZ - r_DZ)`, where `r = Cov / V_P`. -/
theorem narrow_le_falconerHeritability (C : ℝ) {VP : ℝ} (hVP : 0 < VP) :
    c.varA / VP ≤ 2 * ((c.cov 1 1 + C) / VP - (c.cov (1 / 2) (1 / 4) + C) / VP) := by
  have h := div_le_div_of_nonneg_right (c.varA_le_falconer C) hVP.le
  simpa only [falconer, sub_div, mul_div_assoc] using h

end CockerhamComponents

namespace LocusModel

variable {A : Type*} [Fintype A] (m : LocusModel A)

/-- The one-locus model as Cockerham components of order `1`: `V 1 0 = V_A`, `V 0 1 = V_D`,
`V 1 1 = 0`. -/
def toComponents : CockerhamComponents where
  n := 1
  V i j := if (i, j) = (1, 0) then m.varA else if (i, j) = (0, 1) then m.varD else 0
  V_nonneg i j := by
    split_ifs
    · exact m.varA_nonneg
    · exact m.varD_nonneg
    · exact le_refl 0
  V_zero_zero := by simp
  V_supported i j h := by
    rcases h with hi | hj <;> split_ifs with h1 h2 <;>
      (first
        | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1; omega)
        | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; omega)
        | rfl)

/-- The one-locus covariance between relatives is the Cockerham form of `toComponents`. -/
theorem relCov_eq_cov {k₀ k₁ k₂ : ℝ} (hk : k₀ + k₁ + k₂ = 1) :
    m.relProd k₀ k₁ k₂ - m.mean ^ 2 = m.toComponents.cov (k₁ / 2 + k₂) k₂ := by
  rw [m.relCov_eq hk]
  simp [CockerhamComponents.cov, toComponents, sum_range_succ, add_comm]

/-- **One-locus phantom heritability, unconditional**: with monozygotic twins
(`k₂ = 1`), dizygotic twins (`k = (1/4, 1/2, 1/4)`) and a common environment `C`,
`2 (Cov_MZ - Cov_DZ) = V_A + (3/2) V_D`. -/
theorem falconer_eq_of_locus (C : ℝ) :
    2 * ((m.relProd 0 0 1 - m.mean ^ 2 + C) - (m.relProd (1 / 4) (1 / 2) (1 / 4) -
      m.mean ^ 2 + C)) = m.varA + 3 / 2 * m.varD := by
  rw [m.relCov_eq (show (0 : ℝ) + 0 + 1 = 1 by norm_num),
    m.relCov_eq (show (1 / 4 : ℝ) + 1 / 2 + 1 / 4 = 1 by norm_num)]
  ring

end LocusModel

end MathlibExt.Biology.StatisticalGenetics.CovarianceRelatives
