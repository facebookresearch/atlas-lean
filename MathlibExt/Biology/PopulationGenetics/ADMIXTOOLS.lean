/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import MathlibExt.Probability.Distributions.BinomialMoments
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# The estimators of ADMIXTOOLS: ABBA–BABA, qpAdm, qpWave, unbiased f-statistics

`FStatistics.lean` defines the population f-statistics `f2`, `f3`, `f4` as expectations over
the allele frequencies `p X` of populations `X`. This file proves the identities behind the
statistics that ADMIXTOOLS computes from data.

## Site patterns and the D-statistic

Sample one haplotype from each of four populations `P1, P2, P3, O` (in this order) and record
whether it carries the derived allele (`x : Fin 4 → Bool`). The unpolarized site patterns are
`ABBA` (`P1` agrees with `O`, `P2` with `P3`, `P1 ≠ P2`; this includes `BAAB`) and `BABA`
(`P1` agrees with `P3`, `P2` with `O`, `P1 ≠ P2`; this includes `ABAB`). With `1/0` indicators
(`Bool.toNat`), `1[BABA] - 1[ABBA] = (x₁ - x₂) (x₃ - x₄)` for every configuration
(`baba_sub_abba`), so under independent sampling at frequencies `q` the expected difference is
`(q₁ - q₂) (q₃ - q₄)` (`sampleExpect_baba_sub_abba`) and, averaged over the frequencies,
`f4 P1 P2 P3 O`.

Sign conventions. Patterson et al. (2012) define `D(W, X; Y, Z)` with numerator
`(w - x) (y - z)`, i.e. `BABA - ABBA` for `(W, X, Y, Z) = (P1, P2, P3, O)`; Green et al. (2010)
and Durand et al. (2011) write `D = (ABBA - BABA) / (ABBA + BABA)`, positive when `P2` and `P3`
share more derived alleles. When `O` is fixed for the ancestral allele, the two numerators differ
only in sign. For a polymorphic outgroup, the unpolarized patterns additionally fold the
complementary allele orientations, so the numerators need not be sign reversals. On the tree
`((P1, P2), P3), O`, the unpolarized numerator vanishes in expectation by the `f4` result below;
no corresponding polarized tree claim is made.

## Main results

* `integral_eq_sampleExpect`: `sampleExpect g q` is the expectation of `g` for independent
  derived-allele indicators with `P(X i = true) = q i`.
* `sampleExpect_baba_sub_abba`: `E[BABA - ABBA] = (q₁ - q₂) (q₃ - q₄)` at fixed frequencies;
  `sampleExpect_babaPol_sub_abbaPol`: the polarized form `(q₁ - q₂) q₃ (1 - q₄)` of Durand
  et al., which equals the previous one when the outgroup is fixed for the ancestral allele.
* `integral_sampleExpect_baba_sub_abba`: averaged over the frequencies, `E[BABA - ABBA]` is
  `f4 P1 P2 P3 O`; `DriftModel.integral_sampleExpect_abba_eq_baba`: when the paths `P1–P2` and
  `P3–O` share no edge (the tree `((P1, P2), P3), O`), `E[ABBA] = E[BABA]`.
* `f4_eq_sum_of_sub_eq_sum`: `f4` is linear in its first pair; `f4_affine_combination`: the
  qpAdm model equation `f4 T X Y Z = ∑ k, w k * f4 (S k) X Y Z` when `p T = ∑ k, w k * p (S k)`
  with `∑ k, w k = 1` (weights of any sign); `DriftModel.f4_affine_combination`: the same for
  admixture-graph weights.
* `rank_f4Matrix_le`: qpWave. If every left population is an affine combination of `k + 1`
  sources, the matrix `f4 (L i) (L 0) (R j) (R 0)` (`i, j ≠ 0`) has rank at most `k`.
* `integral_hetHat`, `integral_f2Hat`, `integral_f3Hat`, `integral_f4Hat`: unbiased
  estimators under binomial sampling of `m` gene copies per population, independent across
  populations (`m ≥ 2` where a heterozygosity correction is made).
* `integral_hudsonDenHat`, `integral_sum_f2Hat`, `integral_sum_hudsonDenHat`,
  `integral_sum_div_integral_sum`: Hudson's `F_ST` in the ratio-of-averages form; numerator and
  denominator are unbiased separately, so the ratio of their expectations is the population
  value. The ratio of the estimated sums is not claimed to be unbiased.

## References

* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck,
  T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093
  (the D-statistic; Appendix: unbiased f-statistic estimators).
* R. E. Green et al., *A draft sequence of the Neandertal genome*, Science 328 (2010),
  710–722.
* E. Y. Durand, N. Patterson, D. Reich, M. Slatkin, *Testing for ancient admixture between
  closely related populations*, Mol. Biol. Evol. 28 (2011), 2239–2252.
* W. Haak et al., *Massive migration from the steppe was a source for Indo-European languages
  in Europe*, Nature 522 (2015), 207–211, Supplementary Information (qpAdm).
* D. Reich et al., *Reconstructing Native American population history*, Nature 488 (2012),
  370–374, Supplementary Information (qpWave rank test).
* R. R. Hudson, M. Slatkin, W. P. Maddison, *Estimation of levels of gene flow from DNA
  sequence data*, Genetics 132 (1992), 583–589.
* G. Bhatia, N. Patterson, S. Sankararaman, A. L. Price, *Estimating and interpreting F_ST:
  the impact of rare variants*, Genome Res. 23 (2013), 1514–1521.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped unitInterval

namespace MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

/-! ### Site patterns -/

section Patterns

/-- Probability of the derived/ancestral configuration `x` when haplotype `i` is sampled
independently and carries the derived allele with probability `q i`. -/
def configProb {n : ℕ} (q : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then q i else 1 - q i

/-- Expectation of a function `g` of the configuration under independent sampling of one
haplotype per population at derived-allele frequencies `q`. -/
def sampleExpect {n : ℕ} (g : (Fin n → Bool) → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ x, g x * configProb q x

/-- Unpolarized `ABBA` indicator for populations `(P1, P2, P3, O)`: `P1` agrees with `O`, `P2`
with `P3`, and `P1` differs from `P2` (the patterns `ABBA` and `BAAB`). -/
def abba (x : Fin 4 → Bool) : ℝ := if x 0 = x 3 ∧ x 1 = x 2 ∧ x 0 ≠ x 1 then 1 else 0

/-- Unpolarized `BABA` indicator for populations `(P1, P2, P3, O)`: `P1` agrees with `P3`, `P2`
with `O`, and `P1` differs from `P2` (the patterns `BABA` and `ABAB`). -/
def baba (x : Fin 4 → Bool) : ℝ := if x 0 = x 2 ∧ x 1 = x 3 ∧ x 0 ≠ x 1 then 1 else 0

/-- Polarized `ABBA` indicator (Durand et al. 2011): `P1` and `O` ancestral, `P2` and `P3`
derived. -/
def abbaPol (x : Fin 4 → Bool) : ℝ :=
  if x 0 = false ∧ x 1 = true ∧ x 2 = true ∧ x 3 = false then 1 else 0

/-- Polarized `BABA` indicator (Durand et al. 2011): `P1` and `P3` derived, `P2` and `O`
ancestral. -/
def babaPol (x : Fin 4 → Bool) : ℝ :=
  if x 0 = true ∧ x 1 = false ∧ x 2 = true ∧ x 3 = false then 1 else 0

/-- The configuration probabilities sum to `1`. -/
theorem sum_configProb {n : ℕ} (q : Fin n → ℝ) : ∑ x, configProb q x = 1 := by
  unfold configProb
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then q i else 1 - q i)]
  simp

/-- `sampleExpect` of a product of functions of single coordinates factorizes:
`E[∏ i, g i (x i)] = ∏ i, (g i true * q i + g i false * (1 - q i))`. -/
theorem sampleExpect_prod {n : ℕ} (g : Fin n → Bool → ℝ) (q : Fin n → ℝ) :
    sampleExpect (fun x => ∏ i, g i (x i)) q =
      ∏ i, (g i true * q i + g i false * (1 - q i)) := by
  unfold sampleExpect configProb
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => g i b * if b then q i else 1 - q i)]
  simp

/-- `sampleExpect` is additive in the function. -/
theorem sampleExpect_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) (q : Fin n → ℝ) :
    sampleExpect (fun x => f x + g x) q = sampleExpect f q + sampleExpect g q := by
  simp [sampleExpect, add_mul, Finset.sum_add_distrib]

/-- `sampleExpect` commutes with subtraction of functions. -/
theorem sampleExpect_sub {n : ℕ} (f g : (Fin n → Bool) → ℝ) (q : Fin n → ℝ) :
    sampleExpect (fun x => f x - g x) q = sampleExpect f q - sampleExpect g q := by
  simp [sampleExpect, sub_mul, Finset.sum_sub_distrib]

/-- `sampleExpect` is the expectation under independent sampling: if the derived-allele
indicators `X i` are independent random variables with `P(X i = true) = q i`, then
`E[g (X 0, …, X (n - 1))] = sampleExpect g q`. -/
theorem integral_eq_sampleExpect {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → Bool} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X ν) {q : Fin n → ℝ} (hq : ∀ i, ν.real {ω | X i ω = true} = q i)
    (g : (Fin n → Bool) → ℝ) :
    ∫ ω, g (fun i => X i ω) ∂ν = sampleExpect g q := by
  have hXv : Measurable fun ω i => X i ω := measurable_pi_iff.2 hX
  rw [← integral_map hXv.aemeasurable (Measurable.of_discrete (f := g)).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  unfold sampleExpect
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_eq_mul, mul_comm, map_measureReal_apply hXv (measurableSet_singleton y)]
  congr 1
  have hpre : (fun ω i => X i ω) ⁻¹' {y} = ⋂ i, X i ⁻¹' {y i} := by
    ext ω
    simp [funext_iff]
  rw [hpre, measureReal_def, hind.meas_iInter fun i => ⟨{y i}, measurableSet_singleton _, rfl⟩,
    ENNReal.toReal_prod]
  unfold configProb
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← measureReal_def]
  cases hy : y i
  · have : X i ⁻¹' {false} = {ω | X i ω = true}ᶜ := by
      ext ω
      simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_eq_fun (hX i) measurable_const), hq]
    simp
  · simp only [ite_true]
    exact hq i

/-- The site-pattern identity: `1[BABA] - 1[ABBA] = (x₁ - x₂) (x₃ - x₄)` for every
configuration of derived-allele indicators. -/
theorem baba_sub_abba (x : Fin 4 → Bool) :
    baba x - abba x =
      (((x 0).toNat : ℝ) - (x 1).toNat) * (((x 2).toNat : ℝ) - (x 3).toNat) := by
  rcases h0 : x 0 <;> rcases h1 : x 1 <;> rcases h2 : x 2 <;> rcases h3 : x 3 <;>
    simp [baba, abba, h0, h1, h2, h3]

/-- The indicator `b ↦ b.toNat` as a real function (proof-only abbreviation). -/
private def tn (b : Bool) : ℝ := b.toNat

/-- The complementary indicator `b ↦ 1 - b.toNat` (proof-only abbreviation). -/
private def tc (b : Bool) : ℝ := 1 - b.toNat

/-- **ABBA–BABA identity** (Patterson et al. 2012; Durand et al. 2011): under independent
sampling of one haplotype per population at derived-allele frequencies `q` (any reals;
frequencies in `[0, 1]` in the biological model), `E[BABA - ABBA] = (q₁ - q₂) (q₃ - q₄)`. -/
theorem sampleExpect_baba_sub_abba (q : Fin 4 → ℝ) :
    sampleExpect (fun x => baba x - abba x) q = (q 0 - q 1) * (q 2 - q 3) := by
  have h : (fun x => baba x - abba x) = fun x =>
      (∏ i, (![tn, fun _ => 1, tn, fun _ => 1] : Fin 4 → Bool → ℝ) i (x i)
        + ∏ i, (![fun _ => 1, tn, fun _ => 1, tn] : Fin 4 → Bool → ℝ) i (x i))
      - (∏ i, (![tn, fun _ => 1, fun _ => 1, tn] : Fin 4 → Bool → ℝ) i (x i)
        + ∏ i, (![fun _ => 1, tn, tn, fun _ => 1] : Fin 4 → Bool → ℝ) i (x i)) := by
    funext x
    rw [baba_sub_abba]
    simp [Fin.prod_univ_four, tn]
    ring
  rw [h, sampleExpect_sub, sampleExpect_add, sampleExpect_add, sampleExpect_prod,
    sampleExpect_prod, sampleExpect_prod, sampleExpect_prod]
  simp only [Fin.prod_univ_four]
  simp [tn]
  ring

/-- Polarized form (Durand et al. 2011, with `q 3` the derived-allele frequency in the
outgroup): `E[BABA_pol - ABBA_pol] = (q₁ - q₂) q₃ (1 - q₄)`. When the outgroup is fixed for the
ancestral allele (`q 3 = 0`) this is `(q₁ - q₂) (q₃ - q₄)`, as in the unpolarized identity. -/
theorem sampleExpect_babaPol_sub_abbaPol (q : Fin 4 → ℝ) :
    sampleExpect (fun x => babaPol x - abbaPol x) q = (q 0 - q 1) * q 2 * (1 - q 3) := by
  have h : (fun x => babaPol x - abbaPol x) = fun x =>
      ∏ i, (![tn, tc, tn, tc] : Fin 4 → Bool → ℝ) i (x i)
        - ∏ i, (![tc, tn, tn, tc] : Fin 4 → Bool → ℝ) i (x i) := by
    funext x
    simp only [Fin.prod_univ_four]
    rcases h0 : x 0 <;> rcases h1 : x 1 <;> rcases h2 : x 2 <;> rcases h3 : x 3 <;>
      simp [babaPol, abbaPol, tn, tc, h0, h1, h2, h3]
  rw [h, sampleExpect_sub, sampleExpect_prod, sampleExpect_prod]
  simp only [Fin.prod_univ_four]
  simp [tn, tc]
  ring

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

/-- **ABBA–BABA equals `f4`**: when the frequencies `p X ω` are themselves random (drift, and
the choice of locus) and one haplotype is sampled from each population independently given the
frequencies, the expected `BABA - ABBA` difference is `f4 P1 P2 P3 O`. -/
theorem integral_sampleExpect_baba_sub_abba (P1 P2 P3 O : P) :
    ∫ ω, sampleExpect (fun x => baba x - abba x) ![p P1 ω, p P2 ω, p P3 ω, p O ω] ∂μ =
      f4 μ p P1 P2 P3 O := by
  simp_rw [sampleExpect_baba_sub_abba]
  simp [f4]

end Patterns

/-! ### The qpAdm model equation -/

section QpAdm

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

/-- Linearity of `f4` in its first pair: if `p A - p B = ∑ l, c l * (p (C l) - p (D l))`
pointwise, then `f4 A B Y Z = ∑ l, c l * f4 (C l) (D l) Y Z`. -/
theorem f4_eq_sum_of_sub_eq_sum (hp : ∀ X, MemLp (p X) 2 μ) {ι : Type*} [Fintype ι]
    {A B Y Z : P} (C D : ι → P) (c : ι → ℝ)
    (h : ∀ ω, p A ω - p B ω = ∑ l, c l * (p (C l) ω - p (D l) ω)) :
    f4 μ p A B Y Z = ∑ l, c l * f4 μ p (C l) (D l) Y Z := by
  unfold f4
  have hint : ∀ l, Integrable (fun ω => c l * ((p (C l) ω - p (D l) ω) * (p Y ω - p Z ω))) μ :=
    fun l => (((hp (C l)).sub (hp (D l))).integrable_mul ((hp Y).sub (hp Z))).const_mul _
  simp_rw [h, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun l _ => hint l]
  simp_rw [integral_const_mul]

/-- **qpAdm model equation** (Haak et al. 2015, Supplementary Information): if the target `T`
is an admixture of sources `S k` with weights `w k` summing to `1` (`p T = ∑ k, w k * p (S k)`
pointwise; the weights may be negative, as in fitted qpAdm models), then for all `X`, `Y`, `Z`,
`f4 T X Y Z = ∑ k, w k * f4 (S k) X Y Z`. The merged `DriftModel.f4_admixture_right` is a
two-source drift-model instance (mixture in the second pair, one source as fourth argument). -/
theorem f4_affine_combination (hp : ∀ X, MemLp (p X) 2 μ) {ι : Type*} [Fintype ι]
    {T X Y Z : P} (S : ι → P) (w : ι → ℝ) (hw : ∑ k, w k = 1)
    (hT : ∀ ω, p T ω = ∑ k, w k * p (S k) ω) :
    f4 μ p T X Y Z = ∑ k, w k * f4 μ p (S k) X Y Z := by
  refine f4_eq_sum_of_sub_eq_sum hp S (fun _ => X) w fun ω => ?_
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul, hT ω]

/-! ### The qpWave rank bound -/

variable (μ p) in
/-- The qpWave matrix of left populations `L 0, …, L n` and right populations
`R 0, …, R r`: entry `(i, j)` is `f4 (L (i + 1)) (L 0) (R (j + 1)) (R 0)`. -/
noncomputable def f4Matrix {n r : ℕ} (L : Fin (n + 1) → P) (R : Fin (r + 1) → P) :
    Matrix (Fin n) (Fin r) ℝ :=
  Matrix.of fun i j => f4 μ p (L i.succ) (L 0) (R j.succ) (R 0)

/-- **qpWave rank bound** (Reich et al. 2012, Supplementary Information; Patterson et al.
2012): if the frequency of every left population `L i` is an affine combination
`∑ l, a i l * p (S l)` (`∑ l, a i l = 1`, coefficients of any sign) of the frequencies of
`k + 1` source populations, then the matrix `f4 (L i) (L 0) (R j) (R 0)` (`i, j ≥ 1`) has rank
at most `k`; with `k` sources, at most `k - 1`. The right populations are arbitrary. The
converse (rank `k` forces `k + 1` streams) and the statistical rank test are not covered. -/
theorem rank_f4Matrix_le (hp : ∀ X, MemLp (p X) 2 μ) {n r k : ℕ} (L : Fin (n + 1) → P)
    (R : Fin (r + 1) → P) (S : Fin (k + 1) → P) (a : Fin (n + 1) → Fin (k + 1) → ℝ)
    (ha : ∀ i, ∑ l, a i l = 1) (hL : ∀ i ω, p (L i) ω = ∑ l, a i l * p (S l) ω) :
    (f4Matrix μ p L R).rank ≤ k := by
  let A : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun i l => a i.succ l.succ - a 0 l.succ
  let F : Matrix (Fin k) (Fin r) ℝ :=
    Matrix.of fun l j => f4 μ p (S l.succ) (S 0) (R j.succ) (R 0)
  have hM : f4Matrix μ p L R = A * F := by
    ext i j
    simp only [f4Matrix, Matrix.of_apply, Matrix.mul_apply, A, F]
    refine f4_eq_sum_of_sub_eq_sum hp (fun l : Fin k => S l.succ) (fun _ => S 0) _ fun ω => ?_
    have hi := ha i.succ
    have h0 := ha 0
    rw [Fin.sum_univ_succ] at hi h0
    rw [hL, hL, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    linear_combination (p (S 0) ω) * (hi - h0)
  rw [hM]
  exact (Matrix.rank_mul_le_left A F).trans (Matrix.rank_le_width A)

end QpAdm

/-! ### Unbiased estimators under binomial sampling -/

section Estimators

/-- Unbiased estimator of `p (1 - p)` from `x` derived copies among `m` sampled copies:
`x (m - x) / (m (m - 1))` (meaningful for `m ≥ 2`). -/
noncomputable def hetHat (m : ℕ) (x : ℝ) : ℝ := x * (m - x) / (m * (m - 1))

/-- The unbiased `f2` estimator of Patterson et al. (2012), Appendix:
`(â - b̂)² - â (1 - â) / (m_A - 1) - b̂ (1 - b̂) / (m_B - 1)` with `â = x_A / m_A`,
written as `(x_A / m_A - x_B / m_B)² - x_A (m_A - x_A) / (m_A² (m_A - 1)) - …`. -/
noncomputable def f2Hat (mA mB : ℕ) (xA xB : ℝ) : ℝ :=
  (xA / mA - xB / mB) ^ 2 - hetHat mA xA / mA - hetHat mB xB / mB

/-- The unbiased `f3` estimator of Patterson et al. (2012), Appendix:
`(ĉ - â) (ĉ - b̂) - ĉ (1 - ĉ) / (m_C - 1)`. -/
noncomputable def f3Hat (mC mA mB : ℕ) (xC xA xB : ℝ) : ℝ :=
  (xC / mC - xA / mA) * (xC / mC - xB / mB) - hetHat mC xC / mC

/-- The `f4` estimator `(â - b̂) (ĉ - d̂)`; it needs no correction for four distinct
populations. -/
noncomputable def f4Hat (mA mB mC mD : ℕ) (xA xB xC xD : ℝ) : ℝ :=
  (xA / mA - xB / mB) * (xC / mC - xD / mD)

/-- Hudson's `F_ST` denominator estimator `â (1 - b̂) + b̂ (1 - â)` (Bhatia et al. 2013); the
numerator estimator is `f2Hat`. -/
noncomputable def hudsonDenHat (mA mB : ℕ) (xA xB : ℝ) : ℝ :=
  xA / mA * (1 - xB / mB) + xB / mB * (1 - xA / mA)

/-- Hudson's `F_ST` denominator at one site: `p_A (1 - p_B) + p_B (1 - p_A)`, the probability
that two copies, one from each population, differ. The numerator is `(p_A - p_B) ^ 2`. -/
def hudsonDen (pA pB : ℝ) : ℝ := pA * (1 - pB) + pB * (1 - pA)

/-- Hudson's `F_ST` over sites `s` in the ratio-of-averages form of Bhatia et al. (2013):
`∑ s, (p_A s - p_B s) ^ 2 / ∑ s, hudsonDen (p_A s) (p_B s)`. It is defined when the denominator
is positive (it vanishes only if every site is fixed for the same allele in both populations);
otherwise Lean's value `0` is a junk value. -/
noncomputable def hudsonFst {ι : Type*} (s : Finset ι) (pA pB : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (pA i - pB i) ^ 2) / ∑ i ∈ s, hudsonDen (pA i) (pB i)

/-- At each site Hudson's numerator is at most the denominator for frequencies in `[0, 1]`: the
difference is `p_A (1 - p_A) + p_B (1 - p_B) ≥ 0`. -/
theorem sq_sub_le_hudsonDen {pA pB : ℝ} (hA0 : 0 ≤ pA) (hA1 : pA ≤ 1) (hB0 : 0 ≤ pB)
    (hB1 : pB ≤ 1) : (pA - pB) ^ 2 ≤ hudsonDen pA pB := by
  unfold hudsonDen
  nlinarith [mul_nonneg hA0 (sub_nonneg.2 hA1), mul_nonneg hB0 (sub_nonneg.2 hB1)]

/-- Hudson's `F_ST` lies in `[0, 1]` for frequencies in `[0, 1]`. (When the denominator vanishes
the junk value `0` also lies in `[0, 1]`, so no positivity hypothesis is needed.) -/
theorem hudsonFst_mem_Icc {ι : Type*} (s : Finset ι) (pA pB : ι → ℝ)
    (hA : ∀ i ∈ s, pA i ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ i ∈ s, pB i ∈ Set.Icc (0 : ℝ) 1) :
    hudsonFst s pA pB ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : ∑ i ∈ s, (pA i - pB i) ^ 2 ≤ ∑ i ∈ s, hudsonDen (pA i) (pB i) :=
    Finset.sum_le_sum fun i hi =>
      sq_sub_le_hudsonDen (hA i hi).1 (hA i hi).2 (hB i hi).1 (hB i hi).2
  have h0 : 0 ≤ ∑ i ∈ s, (pA i - pB i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact ⟨div_nonneg h0 (h0.trans hle), div_le_one_of_le₀ hle (h0.trans hle)⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

private lemma integrable_comp_bin {X : Ω → ℝ} {m : ℕ} {q : I} (hX : HasLaw X Bin(ℝ, m, q) μ)
    (g : ℝ → ℝ) :
    Integrable (fun ω => g (X ω)) μ :=
  hX.integrable_comp (integrable_map_cast_binomial g)

/-- The sample frequency is unbiased: for `X ~ Bin(m, p)` with `m ≥ 1`, `E[X / m] = p`. (For
`m = 0`, `X / 0 = 0` is a junk value, hence `m ≥ 1`.) -/
theorem integral_div_of_hasLaw_binomial {X : Ω → ℝ} {m : ℕ} {q : I}
    (hX : HasLaw X Bin(ℝ, m, q) μ) (hm : 1 ≤ m) : μ[fun ω => X ω / m] = (q : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [integral_div, integral_of_hasLaw_binomial hX]
  field_simp

private lemma cast_sub_one_ne_zero {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) - 1 ≠ 0 := by
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

private lemma integral_mul_sub_one_div {X : Ω → ℝ} {m : ℕ} {q : I}
    (hX : HasLaw X Bin(ℝ, m, q) μ) (hm : 2 ≤ m) :
    μ[fun ω => X ω * (X ω - 1) / (m * (m - 1))] = (q : ℝ) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm1 := cast_sub_one_ne_zero hm
  rw [integral_div, integral_mul_sub_one_of_hasLaw_binomial hX]
  field_simp

/-- **Unbiased heterozygosity**: for `X ~ Bin(m, p)` with `m ≥ 2`,
`E[X (m - X) / (m (m - 1))] = p (1 - p)`. -/
theorem integral_hetHat {X : Ω → ℝ} {m : ℕ} {q : I} (hX : HasLaw X Bin(ℝ, m, q) μ)
    (hm : 2 ≤ m) : μ[fun ω => hetHat m (X ω)] = q * (1 - (q : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm1 := cast_sub_one_ne_zero hm
  have h : ∀ ω, hetHat m (X ω) = X ω / m - X ω * (X ω - 1) / (m * (m - 1)) := fun ω => by
    unfold hetHat
    field_simp
    ring
  simp_rw [h]
  rw [integral_sub (integrable_comp_bin hX (fun x => x / m))
    (integrable_comp_bin hX (fun x => x * (x - 1) / (m * (m - 1)))),
    integral_div_of_hasLaw_binomial hX (by omega), integral_mul_sub_one_div hX hm]
  ring

private lemma indepFun_div {X Y : Ω → ℝ} {mX mY : ℕ} (hXY : IndepFun X Y μ) :
    IndepFun (fun ω => X ω / mX) (fun ω => Y ω / mY) μ :=
  hXY.comp (φ := fun x => x / (mX : ℝ)) (ψ := fun x => x / (mY : ℝ))
    (measurable_id.div_const _) (measurable_id.div_const _)

private lemma integral_mul_freq {X Y : Ω → ℝ} {mX mY : ℕ} {qX qY : I}
    (hX : HasLaw X Bin(ℝ, mX, qX) μ)
    (hY : HasLaw Y Bin(ℝ, mY, qY) μ) (hXY : IndepFun X Y μ) (hmX : 1 ≤ mX) (hmY : 1 ≤ mY) :
    μ[fun ω => X ω / mX * (Y ω / mY)] = qX * (qY : ℝ) := by
  rw [IndepFun.integral_fun_mul_eq_mul_integral (indepFun_div hXY)
    (integrable_comp_bin hX (fun x => x / (mX : ℝ))).aestronglyMeasurable
    (integrable_comp_bin hY (fun x => x / (mY : ℝ))).aestronglyMeasurable,
    integral_div_of_hasLaw_binomial hX hmX, integral_div_of_hasLaw_binomial hY hmY]

private lemma integrable_mul_freq {X Y : Ω → ℝ} {mX mY : ℕ} {qX qY : I}
    (hX : HasLaw X Bin(ℝ, mX, qX) μ)
    (hY : HasLaw Y Bin(ℝ, mY, qY) μ) (hXY : IndepFun X Y μ) :
    Integrable (fun ω => X ω / mX * (Y ω / mY)) μ :=
  IndepFun.integrable_mul (indepFun_div hXY) (integrable_comp_bin hX (fun x => x / (mX : ℝ)))
    (integrable_comp_bin hY (fun x => x / (mY : ℝ)))

private lemma integrable_f2Hat {XA XB : Ω → ℝ} {mA mB : ℕ} {qA qB : I}
    (hA : HasLaw XA Bin(ℝ, mA, qA) μ) (hB : HasLaw XB Bin(ℝ, mB, qB) μ)
    (hAB : IndepFun XA XB μ) : Integrable (fun ω => f2Hat mA mB (XA ω) (XB ω)) μ := by
  have h : (fun ω => f2Hat mA mB (XA ω) (XB ω)) = fun ω =>
      (XA ω / mA) ^ 2 - hetHat mA (XA ω) / mA + ((XB ω / mB) ^ 2 - hetHat mB (XB ω) / mB) -
        2 * (XA ω / mA * (XB ω / mB)) := by
    funext ω
    unfold f2Hat
    ring
  rw [h]
  exact ((integrable_comp_bin hA (fun x => (x / mA) ^ 2 - hetHat mA x / mA)).add
    (integrable_comp_bin hB (fun x => (x / mB) ^ 2 - hetHat mB x / mB))).sub
    ((integrable_mul_freq hA hB hAB).const_mul 2)

private lemma integrable_hudsonDenHat {XA XB : Ω → ℝ} {mA mB : ℕ} {qA qB : I}
    (hA : HasLaw XA Bin(ℝ, mA, qA) μ) (hB : HasLaw XB Bin(ℝ, mB, qB) μ)
    (hAB : IndepFun XA XB μ) : Integrable (fun ω => hudsonDenHat mA mB (XA ω) (XB ω)) μ := by
  have h : (fun ω => hudsonDenHat mA mB (XA ω) (XB ω)) = fun ω =>
      XA ω / mA + XB ω / mB - 2 * (XA ω / mA * (XB ω / mB)) := by
    funext ω
    unfold hudsonDenHat
    ring
  rw [h]
  exact ((integrable_comp_bin hA (fun x => x / (mA : ℝ))).add
    (integrable_comp_bin hB (fun x => x / (mB : ℝ)))).sub
    ((integrable_mul_freq hA hB hAB).const_mul 2)

/-- **Unbiased `f2`** (Patterson et al. 2012, Appendix): with independent binomial samples
`X_A ~ Bin(m_A, p_A)`, `X_B ~ Bin(m_B, p_B)`, `m_A, m_B ≥ 2`,
`E[f2Hat] = (p_A - p_B) ^ 2`, the population `f2` at the site. -/
theorem integral_f2Hat {XA XB : Ω → ℝ} {mA mB : ℕ} {qA qB : I}
    (hA : HasLaw XA Bin(ℝ, mA, qA) μ) (hB : HasLaw XB Bin(ℝ, mB, qB) μ) (hAB : IndepFun XA XB μ)
    (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    μ[fun ω => f2Hat mA mB (XA ω) (XB ω)] = ((qA : ℝ) - qB) ^ 2 := by
  have hA0 : (mA : ℝ) ≠ 0 := by positivity
  have hA1 := cast_sub_one_ne_zero hmA
  have hB0 : (mB : ℝ) ≠ 0 := by positivity
  have hB1 := cast_sub_one_ne_zero hmB
  have h : ∀ ω, f2Hat mA mB (XA ω) (XB ω) =
      XA ω * (XA ω - 1) / (mA * (mA - 1)) + XB ω * (XB ω - 1) / (mB * (mB - 1)) -
        2 * (XA ω / mA * (XB ω / mB)) := fun ω => by
    unfold f2Hat hetHat
    field_simp
    ring
  simp_rw [h]
  rw [integral_sub ?_ ?_, integral_add ?_ ?_, integral_const_mul, integral_mul_sub_one_div hA hmA,
    integral_mul_sub_one_div hB hmB,
    integral_mul_freq hA hB hAB (by omega) (by omega)]
  · ring
  · exact integrable_comp_bin hA (fun x => x * (x - 1) / (mA * (mA - 1)))
  · exact integrable_comp_bin hB (fun x => x * (x - 1) / (mB * (mB - 1)))
  · exact (integrable_comp_bin hA (fun x => x * (x - 1) / (mA * (mA - 1)))).add
      (integrable_comp_bin hB (fun x => x * (x - 1) / (mB * (mB - 1))))
  · exact (integrable_mul_freq hA hB hAB).const_mul _

/-- **Unbiased `f3`** (Patterson et al. 2012, Appendix): with pairwise independent binomial
samples, `m_C ≥ 2` and `m_A, m_B ≥ 1`, `E[f3Hat] = (p_C - p_A) (p_C - p_B)`. -/
theorem integral_f3Hat {XC XA XB : Ω → ℝ} {mC mA mB : ℕ} {qC qA qB : I}
    (hC : HasLaw XC Bin(ℝ, mC, qC) μ) (hA : HasLaw XA Bin(ℝ, mA, qA) μ)
    (hB : HasLaw XB Bin(ℝ, mB, qB) μ) (hCA : IndepFun XC XA μ) (hCB : IndepFun XC XB μ)
    (hAB : IndepFun XA XB μ) (hmC : 2 ≤ mC) (hmA : 1 ≤ mA) (hmB : 1 ≤ mB) :
    μ[fun ω => f3Hat mC mA mB (XC ω) (XA ω) (XB ω)] = ((qC : ℝ) - qA) * ((qC : ℝ) - qB) := by
  have hC0 : (mC : ℝ) ≠ 0 := by positivity
  have hC1 := cast_sub_one_ne_zero hmC
  have h : ∀ ω, f3Hat mC mA mB (XC ω) (XA ω) (XB ω) =
      XC ω * (XC ω - 1) / (mC * (mC - 1)) - XC ω / mC * (XA ω / mA) -
        XC ω / mC * (XB ω / mB) + XA ω / mA * (XB ω / mB) := fun ω => by
    unfold f3Hat hetHat
    field_simp
    ring
  simp_rw [h]
  have iC := integrable_comp_bin hC (fun x => x * (x - 1) / (mC * (mC - 1)))
  have iCA := integrable_mul_freq hC hA hCA
  have iCB := integrable_mul_freq hC hB hCB
  have iAB := integrable_mul_freq hA hB hAB
  rw [integral_add ?_ iAB, integral_sub ?_ iCB, integral_sub iC iCA,
    integral_mul_sub_one_div hC hmC, integral_mul_freq hC hA hCA (by omega) hmA,
    integral_mul_freq hC hB hCB (by omega) hmB, integral_mul_freq hA hB hAB hmA hmB]
  · ring
  · exact iC.sub iCA
  · exact (iC.sub iCA).sub iCB

/-- **Unbiased `f4`**: for four populations sampled independently across the two pairs
(`m ≥ 1` each), `E[f4Hat] = (p_A - p_B) (p_C - p_D)`; no correction is needed. -/
theorem integral_f4Hat {XA XB XC XD : Ω → ℝ} {mA mB mC mD : ℕ} {qA qB qC qD : I}
    (hA : HasLaw XA Bin(ℝ, mA, qA) μ) (hB : HasLaw XB Bin(ℝ, mB, qB) μ)
    (hC : HasLaw XC Bin(ℝ, mC, qC) μ) (hD : HasLaw XD Bin(ℝ, mD, qD) μ)
    (hAC : IndepFun XA XC μ) (hAD : IndepFun XA XD μ) (hBC : IndepFun XB XC μ)
    (hBD : IndepFun XB XD μ) (hmA : 1 ≤ mA) (hmB : 1 ≤ mB) (hmC : 1 ≤ mC) (hmD : 1 ≤ mD) :
    μ[fun ω => f4Hat mA mB mC mD (XA ω) (XB ω) (XC ω) (XD ω)] =
      ((qA : ℝ) - qB) * ((qC : ℝ) - qD) := by
  have h : ∀ ω, f4Hat mA mB mC mD (XA ω) (XB ω) (XC ω) (XD ω) =
      XA ω / mA * (XC ω / mC) - XA ω / mA * (XD ω / mD) - XB ω / mB * (XC ω / mC) +
        XB ω / mB * (XD ω / mD) := fun ω => by
    unfold f4Hat
    ring
  simp_rw [h]
  have iAC := integrable_mul_freq hA hC hAC
  have iAD := integrable_mul_freq hA hD hAD
  have iBC := integrable_mul_freq hB hC hBC
  have iBD := integrable_mul_freq hB hD hBD
  rw [integral_add ?_ iBD, integral_sub ?_ iBC, integral_sub iAC iAD,
    integral_mul_freq hA hC hAC hmA hmC, integral_mul_freq hA hD hAD hmA hmD,
    integral_mul_freq hB hC hBC hmB hmC, integral_mul_freq hB hD hBD hmB hmD]
  · ring
  · exact iAC.sub iAD
  · exact (iAC.sub iAD).sub iBC

/-- **Hudson's denominator is unbiased** (Bhatia et al. 2013): with independent binomial samples
(`m ≥ 1` each), `E[hudsonDenHat] = hudsonDen p_A p_B`. -/
theorem integral_hudsonDenHat {XA XB : Ω → ℝ} {mA mB : ℕ} {qA qB : I}
    (hA : HasLaw XA Bin(ℝ, mA, qA) μ) (hB : HasLaw XB Bin(ℝ, mB, qB) μ) (hAB : IndepFun XA XB μ)
    (hmA : 1 ≤ mA) (hmB : 1 ≤ mB) :
    μ[fun ω => hudsonDenHat mA mB (XA ω) (XB ω)] = hudsonDen qA qB := by
  have h : ∀ ω, hudsonDenHat mA mB (XA ω) (XB ω) =
      XA ω / mA + XB ω / mB - 2 * (XA ω / mA * (XB ω / mB)) := fun ω => by
    unfold hudsonDenHat
    ring
  simp_rw [h]
  have iA := integrable_comp_bin hA (fun x => x / (mA : ℝ))
  have iB := integrable_comp_bin hB (fun x => x / (mB : ℝ))
  rw [integral_sub ?_ ((integrable_mul_freq hA hB hAB).const_mul _), integral_add iA iB,
    integral_const_mul, integral_div_of_hasLaw_binomial hA hmA,
    integral_div_of_hasLaw_binomial hB hmB, integral_mul_freq hA hB hAB hmA hmB]
  · unfold hudsonDen
    ring
  · exact iA.add iB

variable {ι : Type*} (s : Finset ι) {XA XB : ι → Ω → ℝ} {mA mB : ι → ℕ} {qA qB : ι → I}

/-- Summed over sites, Hudson's numerator estimator `∑ s, f2Hat` is unbiased for
`∑ s, (p_A s - p_B s) ^ 2` (independence is needed only within each site). -/
theorem integral_sum_f2Hat (hA : ∀ i ∈ s, HasLaw (XA i) Bin(ℝ, mA i, qA i) μ)
    (hB : ∀ i ∈ s, HasLaw (XB i) Bin(ℝ, mB i, qB i) μ)
    (hAB : ∀ i ∈ s, IndepFun (XA i) (XB i) μ) (hmA : ∀ i ∈ s, 2 ≤ mA i)
    (hmB : ∀ i ∈ s, 2 ≤ mB i) :
    μ[fun ω => ∑ i ∈ s, f2Hat (mA i) (mB i) (XA i ω) (XB i ω)] =
      ∑ i ∈ s, ((qA i : ℝ) - qB i) ^ 2 := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i hi =>
      integral_f2Hat (hA i hi) (hB i hi) (hAB i hi) (hmA i hi) (hmB i hi)
  · exact fun i hi => integrable_f2Hat (hA i hi) (hB i hi) (hAB i hi)

/-- Summed over sites, Hudson's denominator estimator is unbiased for
`∑ s, hudsonDen (p_A s) (p_B s)`. -/
theorem integral_sum_hudsonDenHat (hA : ∀ i ∈ s, HasLaw (XA i) Bin(ℝ, mA i, qA i) μ)
    (hB : ∀ i ∈ s, HasLaw (XB i) Bin(ℝ, mB i, qB i) μ)
    (hAB : ∀ i ∈ s, IndepFun (XA i) (XB i) μ) (hmA : ∀ i ∈ s, 1 ≤ mA i)
    (hmB : ∀ i ∈ s, 1 ≤ mB i) :
    μ[fun ω => ∑ i ∈ s, hudsonDenHat (mA i) (mB i) (XA i ω) (XB i ω)] =
      ∑ i ∈ s, hudsonDen (qA i) (qB i) := by
  rw [integral_finsetSum _ fun i hi => integrable_hudsonDenHat (hA i hi) (hB i hi) (hAB i hi)]
  exact Finset.sum_congr rfl fun i hi =>
    integral_hudsonDenHat (hA i hi) (hB i hi) (hAB i hi) (hmA i hi) (hmB i hi)

/-- **Hudson's `F_ST`, ratio of averages** (Bhatia et al. 2013): the ratio of the expected
summed numerator and denominator estimators is the population `hudsonFst`. This is a statement
about the ratio of expectations; the expectation of the ratio of the estimated sums is in
general not `hudsonFst`. -/
theorem integral_sum_div_integral_sum (hA : ∀ i ∈ s, HasLaw (XA i) Bin(ℝ, mA i, qA i) μ)
    (hB : ∀ i ∈ s, HasLaw (XB i) Bin(ℝ, mB i, qB i) μ)
    (hAB : ∀ i ∈ s, IndepFun (XA i) (XB i) μ) (hmA : ∀ i ∈ s, 2 ≤ mA i)
    (hmB : ∀ i ∈ s, 2 ≤ mB i) :
    μ[fun ω => ∑ i ∈ s, f2Hat (mA i) (mB i) (XA i ω) (XB i ω)] /
        μ[fun ω => ∑ i ∈ s, hudsonDenHat (mA i) (mB i) (XA i ω) (XB i ω)] =
      hudsonFst s (fun i => qA i) (fun i => qB i) := by
  rw [integral_sum_f2Hat s hA hB hAB hmA hmB,
    integral_sum_hudsonDenHat s hA hB hAB (fun i hi => by have := hmA i hi; omega)
      (fun i hi => by have := hmB i hi; omega)]
  rfl

end Estimators

end MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

/-! ### Drift-model corollaries -/

namespace MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

open MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
  (M : DriftModel μ E P)

/-- **The unpolarized D-statistic numerator vanishes on a tree.** In the drift model, if no edge
lies on both the `P1–P2` and the `P3–O` path (as on the tree `((P1, P2), P3), O`), then the
expected unpolarized `ABBA` and `BABA` counts are equal. Thus `BABA - ABBA` and its sign reversal
have expectation `0`. The integrability hypotheses make both expectations meaningful. -/
theorem integral_sampleExpect_abba_eq_baba {P1 P2 P3 O : P}
    (h : ∀ e, (M.weight P1 e - M.weight P2 e) * (M.weight P3 e - M.weight O e) = 0)
    (habba : Integrable
      (fun ω => sampleExpect abba ![M.freq P1 ω, M.freq P2 ω, M.freq P3 ω, M.freq O ω]) μ)
    (hbaba : Integrable
      (fun ω => sampleExpect baba ![M.freq P1 ω, M.freq P2 ω, M.freq P3 ω, M.freq O ω]) μ) :
    ∫ ω, sampleExpect abba ![M.freq P1 ω, M.freq P2 ω, M.freq P3 ω, M.freq O ω] ∂μ =
      ∫ ω, sampleExpect baba ![M.freq P1 ω, M.freq P2 ω, M.freq P3 ω, M.freq O ω] ∂μ := by
  have h0 := integral_sampleExpect_baba_sub_abba (μ := μ) (p := M.freq) P1 P2 P3 O
  rw [M.f4_eq_zero_of_disjoint h] at h0
  simp_rw [sampleExpect_sub] at h0
  rw [integral_sub hbaba habba] at h0
  linarith

/-- **qpAdm model equation in the drift model**: if the lineage weights of `T` are an affine
combination `∑ k, w k • weight (S k)` of those of the sources (`∑ k, w k = 1`, weights of any
sign), then `f4 T X Y Z = ∑ k, w k * f4 (S k) X Y Z`. -/
theorem f4_affine_combination {ι : Type*} [Fintype ι] {T X Y Z : P} (S : ι → P) (w : ι → ℝ)
    (hT : M.weight T = ∑ k, w k • M.weight (S k)) (hw : ∑ k, w k = 1) :
    f4 μ M.freq T X Y Z = ∑ k, w k * f4 μ M.freq (S k) X Y Z := by
  simp_rw [M.f4_freq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have : M.weight T e - M.weight X e = ∑ k, w k * (M.weight (S k) e - M.weight X e) := by
    rw [hT]
    simp [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

end MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel
