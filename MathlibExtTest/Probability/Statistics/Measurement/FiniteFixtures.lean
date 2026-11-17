/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCube
public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement.FiniteFixtures

open BooleanCube

open BooleanCube MathlibExt.Probability.Statistics.Measurement

/-!
# Finite independent-coordinate fixtures (test library only)

Finite Boolean cube `BoolCube n` with the uniform (fair-coin) law, realized
Rademacher coordinates `coord n i` via production `cubeVal`, and their actual
moments.  A weighted product law via production `localIndepPMF` is provided
for later coefficient examples.

Computation route for uniform proofs: `integral_fintype`
(`∫ x, f x ∂μ = ∑ x, μ.real {x} • f x`, needs `Integrable f μ`, supplied on a
finite type by `Integrable.of_finite`), then `μUnif_real_singleton`, then
`Finset.sum` / `decide` / `norm_num` over the cube.  Weighted moments use
`localIndepPMF_coordinate_moments` with `cubeVal b = 2 * (if b then 1 else 0) - 1`.
-/

/-- Uniform probability law on the finite Boolean cube. -/
noncomputable def μUnif (n : ℕ) : Measure (BoolCube n) :=
  MeasureTheory.Measure.uniformOfFinset Finset.univ

/-- Fair-coin law on one Bool coordinate. -/
noncomputable abbrev coinMeasure : Measure Bool :=
  MeasureTheory.Measure.uniformOfFinset Finset.univ

/-- Realized `i`-th Rademacher coordinate via production cube value. -/
def coord (n : ℕ) (i : Fin n) (ω : BoolCube n) : ℝ := cubeVal (ω i)

/-- The same realized coordinate used twice (perfectly correlated pair). -/
def sharedCoords (n : ℕ) (i : Fin n) (ω : BoolCube n) : ℝ × ℝ :=
  (coord n i ω, coord n i ω)

/-- Two realized coordinates as a pair; distinctness is a hypothesis
at the use sites, not part of the pair. -/
def coordPair (n : ℕ) (i j : Fin n) (ω : BoolCube n) : ℝ × ℝ :=
  (coord n i ω, coord n j ω)

/-! ## Helpers for half A: finite sums of measures -/

/-! ## Bit-flip pairing via production flip -/

theorem coord_flip_neg (n : ℕ) (i : Fin n) (ω : BoolCube n) :
    coord n i (flipCoord ω i) = -coord n i ω := by
  show coord n i (flipCoord ω i) = -coord n i ω
  show cubeVal (flipCoord ω i i) = -cubeVal (ω i)
  rw [flipCoord_apply_self]
  exact BooleanCube.cubeVal_not _

theorem coord_flip_fixed (n : ℕ) (i j : Fin n) (hji : j ≠ i) (ω : BoolCube n) :
    coord n j (flipCoord ω i) = coord n j ω := by
  show coord n j (flipCoord ω i) = coord n j ω
  show cubeVal (flipCoord ω i j) = cubeVal (ω j)
  rw [flipCoord_apply_of_ne ω hji]

/-- A sum over all outcomes of a function negated by the bit-flip is zero. -/
theorem sum_eq_zero_of_flip_neg (n : ℕ) (i : Fin n) (g : BoolCube n → ℝ)
    (hg : ∀ ω, g (flipCoord ω i) = -g ω) : ∑ ω, g ω = 0 := by
  have hcomp := BooleanCube.sum_comp_flipCoord g i
  simp only [hg] at hcomp
  have h2 : (∑ ω : BoolCube n, g ω) + (∑ ω : BoolCube n, -g ω) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp [add_neg_cancel]
  rw [hcomp] at h2
  linarith

instance (n : ℕ) : IsProbabilityMeasure (μUnif n) := by
  refine ⟨?_⟩
  have hcard0 : (Fintype.card (BoolCube n) : ℝ≥0∞) ≠ 0 := by
    rw [card_boolCube]
    have hpos : (0 : ℝ≥0∞) < (((2 ^ n : ℕ)) : ℝ≥0∞) := by positivity
    exact ne_of_gt hpos
  have hcardTop : (Fintype.card (BoolCube n) : ℝ≥0∞) ≠ ⊤ := by
    rw [card_boolCube]
    simp
  have hdirac : ∀ a : BoolCube n, MeasureTheory.Measure.dirac a Set.univ = 1 :=
    fun a => MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ a)
  simp only [μUnif, MeasureTheory.Measure.uniformOfFinset, MeasureTheory.Measure.finsetSum_apply,
    MeasureTheory.Measure.smul_apply, hdirac, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, mul_one]
  exact ENNReal.mul_inv_cancel hcard0 hcardTop

/-! ## Uniform law: masses and the integral-to-sum bridge -/

theorem μUnif_apply_singleton (n : ℕ) (ω : BoolCube n) :
    μUnif n {ω} = (Fintype.card (BoolCube n) : ℝ≥0∞)⁻¹ := by
  simp [μUnif, Finset.card_univ]

theorem μUnif_apply_singleton_pow (n : ℕ) (ω : BoolCube n) :
    μUnif n {ω} = (2 ^ n : ℝ≥0∞)⁻¹ := by
  simp [μUnif_apply_singleton]

theorem μUnif_real_singleton (n : ℕ) (ω : BoolCube n) :
    (μUnif n).real {ω} = 1 / 2 ^ n := by
  show ((μUnif n {ω}).toReal) = 1 / 2 ^ n
  rw [μUnif_apply_singleton_pow, ENNReal.toReal_inv, ENNReal.toReal_pow]
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [h2, ← one_div]

theorem coinMeasure_isProbability : IsProbabilityMeasure coinMeasure := by
  refine ⟨?_⟩
  have hdirac : ∀ b : Bool, MeasureTheory.Measure.dirac b Set.univ = 1 :=
    fun b => MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ b)
  simp only [coinMeasure, MeasureTheory.Measure.uniformOfFinset,
    MeasureTheory.Measure.finsetSum_apply, MeasureTheory.Measure.smul_apply, hdirac, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, smul_eq_mul,
    mul_one]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem μUnif_eq_pi (n : ℕ) :
    μUnif n = Measure.pi (fun _ : Fin n => coinMeasure) := by
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro ω
  rw [μUnif_apply_singleton_pow]
  have hpi : ({ω} : Set (BoolCube n)) = Set.pi Set.univ (fun i => {ω i}) := by
    ext η
    constructor
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      intro i _
      exact Set.mem_singleton _
    · intro h
      rw [Set.mem_singleton_iff]
      funext i
      have hi := h i (Set.mem_univ i)
      rwa [Set.mem_singleton_iff] at hi
  have hcoin : ∀ b : Bool, coinMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
    intro b
    simp [coinMeasure]
  have hpi_apply : Measure.pi (fun _ : Fin n => coinMeasure) (Set.pi Set.univ (fun i => {ω i}))
      = ∏ i, coinMeasure {ω i} := by
    haveI hcoin_prob : IsProbabilityMeasure coinMeasure := coinMeasure_isProbability
    exact MeasureTheory.Measure.pi_pi _ _
  rw [hpi, hpi_apply]
  simp only [hcoin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_pow

theorem integral_unif_eq_sum (n : ℕ) (f : BoolCube n → ℝ) :
    ∫ ω, f ω ∂μUnif n = ∑ ω, (1 / 2 ^ n : ℝ) * f ω := by
  have h_int : Integrable f (μUnif n) := Integrable.of_finite
  rw [integral_fintype h_int]
  apply Finset.sum_congr rfl
  intro ω _
  have hr : (μUnif n).real {ω} = (1 / 2 ^ n : ℝ) := μUnif_real_singleton n ω
  rw [hr, smul_eq_mul]

/-- The constant-one integral (helper for even moments). -/
theorem integral_unif_one (n : ℕ) : ∫ _ : BoolCube n, (1 : ℝ) ∂μUnif n = 1 := by
  simp only [integral_unif_eq_sum, ← Finset.mul_sum]
  have hsum : (∑ _ω : BoolCube n, (1 : ℝ)) = 2 ^ n := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum]
  exact one_div_mul_cancel (pow_ne_zero _ two_ne_zero)

theorem integrable_coord (n : ℕ) (i : Fin n) :
    Integrable (coord n i) (μUnif n) :=
  Integrable.of_finite

theorem coord_measurable (n : ℕ) (i : Fin n) :
    Measurable (coord n i) :=
  measurable_of_finite _

theorem coord_indepFun {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    IndepFun (coord n i) (coord n j) (μUnif n) := by
  rw [μUnif_eq_pi]
  haveI hcoin_prob : IsProbabilityMeasure coinMeasure := coinMeasure_isProbability
  have hX : ∀ k : Fin n, AEMeasurable (fun b : Bool => cubeVal b) coinMeasure :=
    fun _ => (measurable_of_finite _).aemeasurable
  have hindep := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin n => coinMeasure)
    (X := fun _ : Fin n => fun b : Bool => cubeVal b) hX
  exact hindep.indepFun hij

/-! ## (a) General uniform coordinate moments -/

theorem coord_mean (n : ℕ) (i : Fin n) :
    ∫ ω, coord n i ω ∂μUnif n = 0 := by
  simp only [integral_unif_eq_sum, ← Finset.mul_sum]
  rw [sum_eq_zero_of_flip_neg n i (coord n i) (coord_flip_neg n i), mul_zero]

theorem coord_sq (n : ℕ) (i : Fin n) (ω : BoolCube n) :
    (coord n i ω) ^ 2 = 1 := by
  unfold coord cubeVal
  split <;> norm_num

theorem coord_abs (n : ℕ) (i : Fin n) (ω : BoolCube n) :
    |coord n i ω| = 1 := by
  unfold coord cubeVal
  split <;> norm_num

theorem coord_second_moment (n : ℕ) (i : Fin n) :
    ∫ ω, (coord n i ω) ^ 2 ∂μUnif n = 1 := by
  simp only [coord_sq n i]
  exact integral_unif_one n

theorem coord_third_moment (n : ℕ) (i : Fin n) :
    ∫ ω, (coord n i ω) ^ 3 ∂μUnif n = 0 := by
  have h3 : ∀ ω : BoolCube n, (coord n i ω) ^ 3 = coord n i ω := by
    intro ω
    calc (coord n i ω) ^ 3 = (coord n i ω) ^ 2 * coord n i ω := by ring
    _ = coord n i ω := by rw [coord_sq, one_mul]
  simp only [h3]
  exact coord_mean n i

theorem coord_fourth_moment (n : ℕ) (i : Fin n) :
    ∫ ω, (coord n i ω) ^ 4 ∂μUnif n = 1 := by
  have h4 : ∀ ω : BoolCube n, (coord n i ω) ^ 4 = 1 := by
    intro ω
    calc (coord n i ω) ^ 4 = ((coord n i ω) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [coord_sq, one_pow]
  simp only [h4]
  exact integral_unif_one n

theorem coord_variance (n : ℕ) (i : Fin n) :
    ProbabilityTheory.variance (coord n i) (μUnif n) = 1 := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (measurable_of_finite _).aemeasurable (coord_mean n i)]
  exact coord_second_moment n i

theorem coord_cross_moment {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∫ ω, coord n i ω * coord n j ω ∂μUnif n = 0 := by
  simp only [integral_unif_eq_sum, ← Finset.mul_sum]
  have hsum : (∑ ω : BoolCube n, coord n i ω * coord n j ω) = 0 := by
    apply sum_eq_zero_of_flip_neg n i
    intro ω
    show coord n i (flipCoord ω i) * coord n j (flipCoord ω i)
      = -(coord n i ω * coord n j ω)
    rw [coord_flip_neg, coord_flip_fixed n i j (fun h => hij h.symm)]
    ring
  rw [hsum, mul_zero]

theorem coord_self_moment (n : ℕ) (i : Fin n) :
    ∫ ω, coord n i ω * coord n i ω ∂μUnif n = 1 := by
  have h : ∀ ω : BoolCube n, coord n i ω * coord n i ω = (coord n i ω) ^ 2 :=
    fun ω => (pow_two _).symm
  simp only [h]
  exact coord_second_moment n i

theorem coord_covariance_distinct {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∫ ω, (coord n i ω - 0) * (coord n j ω - 0) ∂μUnif n = 0 := by
  have h : ∀ ω : BoolCube n, (coord n i ω - 0) * (coord n j ω - 0)
      = coord n i ω * coord n j ω := by
    intro ω; rw [sub_zero, sub_zero]
  simp only [h]
  exact coord_cross_moment hij

/-! ## Scaling and coordinate-projection fixtures -/

theorem integral_smul_coord (n : ℕ) (i : Fin n) (a : ℝ) :
    ∫ ω, a * coord n i ω ∂μUnif n = 0 := by
  simp only [integral_unif_eq_sum]
  have h0 : (∑ ω : BoolCube n, coord n i ω) = 0 :=
    sum_eq_zero_of_flip_neg n i (coord n i) (coord_flip_neg n i)
  have hcongr : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (a * coord n i ω)
      = a * ((1 / 2 ^ n : ℝ) * coord n i ω) := fun ω => by ring
  simp only [hcongr, ← Finset.mul_sum, h0, mul_zero]

theorem integral_smul_coord_sq (n : ℕ) (i : Fin n) (a : ℝ) :
    ∫ ω, (a * coord n i ω) ^ 2 ∂μUnif n = a ^ 2 := by
  simp only [integral_unif_eq_sum]
  have hrearr : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (a * coord n i ω) ^ 2
      = (a ^ 2) * ((1 / 2 ^ n : ℝ) * (coord n i ω) ^ 2) := fun ω => by ring
  have h1 : (1 / 2 ^ n : ℝ) * (∑ ω : BoolCube n, (coord n i ω) ^ 2) = 1 := by
    rw [Finset.mul_sum, ← integral_unif_eq_sum]
    exact coord_second_moment n i
  simp only [hrearr, ← Finset.mul_sum, h1, mul_one]

theorem integral_smul_coord_mul_smul_coord_distinct
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a b : ℝ) :
    ∫ ω, (a * coord n i ω) * (b * coord n j ω) ∂μUnif n = 0 := by
  simp only [integral_unif_eq_sum]
  have hrearr : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * ((a * coord n i ω) * (b * coord n j ω))
      = (a * b) * ((1 / 2 ^ n : ℝ) * (coord n i ω * coord n j ω)) := fun ω => by ring
  have h0 : (1 / 2 ^ n : ℝ) * (∑ ω : BoolCube n, (coord n i ω * coord n j ω)) = 0 := by
    rw [Finset.mul_sum, ← integral_unif_eq_sum]
    exact coord_cross_moment hij
  simp only [hrearr, ← Finset.mul_sum, h0, mul_zero]

theorem integral_smul_coord_mul_smul_coord_self (n : ℕ) (i : Fin n) (a b : ℝ) :
    ∫ ω, (a * coord n i ω) * (b * coord n i ω) ∂μUnif n = a * b := by
  simp only [integral_unif_eq_sum]
  have hrearr : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * ((a * coord n i ω) * (b * coord n i ω))
      = (a * b) * ((1 / 2 ^ n : ℝ) * (coord n i ω * coord n i ω)) := fun ω => by ring
  have h1 : (1 / 2 ^ n : ℝ) * (∑ ω : BoolCube n, (coord n i ω * coord n i ω)) = 1 := by
    rw [Finset.mul_sum, ← integral_unif_eq_sum]
    exact coord_self_moment n i
  simp only [hrearr, ← Finset.mul_sum, h1, mul_one]

theorem integral_lincomb (n : ℕ) (s : Finset (Fin n)) (c : Fin n → ℝ) :
    ∫ ω, ∑ i ∈ s, c i * coord n i ω ∂μUnif n = 0 := by
  simp only [integral_unif_eq_sum]
  have hfactor : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (∑ i ∈ s, c i * coord n i ω)
      = ∑ i ∈ s, (1 / 2 ^ n : ℝ) * (c i * coord n i ω) := by
    intro ω; rw [Finset.mul_sum]
  simp only [hfactor]
  rw [Finset.sum_comm]
  have hrearr : ∀ (i : Fin n) (ω : BoolCube n), (1 / 2 ^ n : ℝ) * (c i * coord n i ω)
      = c i * ((1 / 2 ^ n : ℝ) * coord n i ω) := fun i ω => by ring
  simp only [hrearr, ← Finset.mul_sum]
  have h0 : ∀ i : Fin n, (1 / 2 ^ n : ℝ) * (∑ ω : BoolCube n, coord n i ω) = 0 := by
    intro i; rw [Finset.mul_sum, ← integral_unif_eq_sum]; exact coord_mean n i
  simp only [h0, mul_zero, Finset.sum_const_zero]

theorem integral_lincomb_sq (n : ℕ) (s : Finset (Fin n)) (c : Fin n → ℝ) :
    ∫ ω, (∑ i ∈ s, c i * coord n i ω) ^ 2 ∂μUnif n
      = ∑ i ∈ s, (c i) ^ 2 := by
  have hexpand : ∀ ω : BoolCube n, (∑ i ∈ s, c i * coord n i ω) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, (c i * coord n i ω) * (c j * coord n j ω) := by
    intro ω
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [hexpand, integral_unif_eq_sum]
  have hfactor : ∀ ω : BoolCube n,
      (1 / 2 ^ n : ℝ) * (∑ i ∈ s, ∑ j ∈ s, (c i * coord n i ω) * (c j * coord n j ω))
        = ∑ i ∈ s, ∑ j ∈ s, (1 / 2 ^ n : ℝ) * ((c i * coord n i ω) * (c j * coord n j ω)) := by
    intro ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [hfactor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin n,
      (∑ ω : BoolCube n, (1 / 2 ^ n : ℝ) * ((c i * coord n i ω) * (c j * coord n j ω)))
        = (if i = j then c i * c j else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ← integral_unif_eq_sum]
      exact integral_smul_coord_mul_smul_coord_self n _ _ _
    · rw [ite_eq_right hij, ← integral_unif_eq_sum]
      exact integral_smul_coord_mul_smul_coord_distinct hij _ _
  simp only [hinner]
  simp [Finset.sum_ite_eq, hi, pow_two]

theorem integral_coord_mul_lincomb (n : ℕ) (s : Finset (Fin n))
    (c : Fin n → ℝ) (i : Fin n) :
    ∫ ω, coord n i ω * (∑ j ∈ s, c j * coord n j ω) ∂μUnif n
      = if i ∈ s then c i else 0 := by
  have hexpand : ∀ ω : BoolCube n, coord n i ω * (∑ j ∈ s, c j * coord n j ω)
      = ∑ j ∈ s, coord n i ω * (c j * coord n j ω) := by
    intro ω; rw [Finset.mul_sum]
  simp only [hexpand, integral_unif_eq_sum]
  have hfactor : ∀ ω : BoolCube n,
      (1 / 2 ^ n : ℝ) * (∑ j ∈ s, coord n i ω * (c j * coord n j ω))
        = ∑ j ∈ s, (1 / 2 ^ n : ℝ) * (coord n i ω * (c j * coord n j ω)) := by
    intro ω; rw [Finset.mul_sum]
  simp only [hfactor]
  rw [Finset.sum_comm]
  have hrearr : ∀ (j : Fin n) (ω : BoolCube n),
      (1 / 2 ^ n : ℝ) * (coord n i ω * (c j * coord n j ω))
        = (1 / 2 ^ n : ℝ) * (c j * (coord n i ω * coord n j ω)) := fun j ω => by ring
  simp only [hrearr]
  have hfactor2 : ∀ j : Fin n,
      (∑ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (c j * (coord n i ω * coord n j ω)))
        = c j * (∑ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (coord n i ω * coord n j ω)) := by
    intro j
    have hc : ∀ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (c j * (coord n i ω * coord n j ω))
        = c j * ((1 / 2 ^ n : ℝ) * (coord n i ω * coord n j ω)) := fun ω => by ring
    simp only [hc, ← Finset.mul_sum]
  simp only [hfactor2]
  have hinner : ∀ j : Fin n, (∑ ω : BoolCube n, (1 / 2 ^ n : ℝ) * (coord n i ω * coord n j ω))
      = (if i = j then 1 else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ← integral_unif_eq_sum]
      exact coord_self_moment n _
    · rw [ite_eq_right hij, ← integral_unif_eq_sum]
      exact coord_cross_moment hij
  simp only [hinner]
  have hif : ∀ j : Fin n, c j * (if i = j then (1 : ℝ) else 0)
      = (if i = j then c j else 0) := by
    intro j; by_cases hij : i = j <;> simp [hij]
  simp only [hif, Finset.sum_ite_eq]

theorem integral_sum_coord_sq (n : ℕ) (s : Finset (Fin n)) :
    ∫ ω, (∑ i ∈ s, coord n i ω) ^ 2 ∂μUnif n = s.card := by
  have h := integral_lincomb_sq n s (fun _ => 1)
  simp only [one_mul, one_pow] at h
  rw [h]
  simp [Finset.sum_const]

theorem integral_coord_mul_sum_coord (n : ℕ) (s : Finset (Fin n)) (i : Fin n) :
    ∫ ω, coord n i ω * (∑ j ∈ s, coord n j ω) ∂μUnif n
      = if i ∈ s then 1 else 0 := by
  have h := integral_coord_mul_lincomb n s (fun _ => 1) i
  simp only [one_mul] at h
  exact h

/-! ## (c) Shared-coordinate (perfectly correlated) contrast -/

theorem shared_product_moment (n : ℕ) (i : Fin n) :
    ∫ ω, (sharedCoords n i ω).1 * (sharedCoords n i ω).2 ∂μUnif n = 1 := by
  have h : ∀ ω : BoolCube n, (sharedCoords n i ω).1 * (sharedCoords n i ω).2
      = coord n i ω * coord n i ω := fun ω => rfl
  simp only [h]
  exact coord_self_moment n i

theorem indep_product_moment {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∫ ω, (coordPair n i j ω).1 * (coordPair n i j ω).2 ∂μUnif n = 0 := by
  have h : ∀ ω : BoolCube n, (coordPair n i j ω).1 * (coordPair n i j ω).2
      = coord n i ω * coord n j ω := fun ω => rfl
  simp only [h]
  exact coord_cross_moment hij

theorem shared_vs_indep_contrast {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (∫ ω, coord n i ω * coord n i ω ∂μUnif n = 1)
      ∧ (∫ ω, coord n i ω * coord n j ω ∂μUnif n = 0) :=
  ⟨coord_self_moment n i, coord_cross_moment hij⟩

theorem shared_product_ne_zero (n : ℕ) (i : Fin n) :
    ∫ ω, coord n i ω * coord n i ω ∂μUnif n ≠ 0 := by
  rw [coord_self_moment]
  norm_num

/-! ## Weighted product law via production independent PMF

`p i` is `P(coord i = +1)`.  Rademacher moments follow from
`cubeVal b = 2 * (if b then 1 else 0) - 1` with
`localIndepPMF_coordinate_moments`.
-/

/-- Weighted product law, as the production independent PMF. -/
noncomputable abbrev μWeighted {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : Measure (BoolCube n) :=
  (localIndepPMF p (fun i => (hp i).1) (fun i => (hp i).2)).toMeasure

theorem μWeighted_isProbability {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    IsProbabilityMeasure (μWeighted p hp) := by
  unfold μWeighted
  exact PMF.toMeasure.isProbabilityMeasure _

/-- Rademacher value as affine function of the 0/1 indicator. -/
theorem cubeVal_eq_two_mul_indicator (b : Bool) :
    cubeVal b = 2 * (if b then (1:ℝ) else 0) - 1 := by
  cases b <;> norm_num [cubeVal]

theorem weighted_coord_mean {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) :
    ∫ ω, coord n i ω ∂μWeighted p hp = 2 * p i - 1 := by
  have h_eq : ∀ ω : BoolCube n, coord n i ω
      = 2 * (if ω i then (1:ℝ) else 0) - 1 := by
    intro ω
    simp [coord, cubeVal_eq_two_mul_indicator]
  simp_rw [h_eq]
  have h_moments := localIndepPMF_coordinate_moments p
    (fun i => (hp i).1) (fun i => (hp i).2)
  have h_ind : ∫ ω, (if ω i then (1:ℝ) else 0) ∂μWeighted p hp = p i :=
    h_moments.1 i
  have h_one : ∫ _ : BoolCube n, (1:ℝ) ∂μWeighted p hp = 1 := by
    haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
    simp
  have h_int_two : Integrable (fun ω : BoolCube n => 2 * (if ω i then (1:ℝ) else 0))
      (μWeighted p hp) := by
    haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
    exact Integrable.of_finite
  have h_int_one : Integrable (fun _ : BoolCube n => (1:ℝ)) (μWeighted p hp) := by
    haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
    exact Integrable.of_finite
  rw [integral_sub h_int_two h_int_one, integral_const_mul, h_ind, h_one]

theorem weighted_coord_second_moment {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) :
    ∫ ω, (coord n i ω) ^ 2 ∂μWeighted p hp = 1 := by
  have h1 : ∀ ω : BoolCube n, (coord n i ω) ^ 2 = 1 := fun ω => coord_sq n i ω
  simp_rw [h1]
  haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
  simp

theorem weighted_coord_cross_moment {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {i j : Fin n} (hij : i ≠ j) :
    ∫ ω, coord n i ω * coord n j ω ∂μWeighted p hp
      = (2 * p i - 1) * (2 * p j - 1) := by
  have h_eq : ∀ ω : BoolCube n, coord n i ω * coord n j ω
      = (2 * (if ω i then (1:ℝ) else 0) - 1) * (2 * (if ω j then (1:ℝ) else 0) - 1) := by
    intro ω
    simp [coord, cubeVal_eq_two_mul_indicator]
  simp_rw [h_eq]
  have h_moments := localIndepPMF_coordinate_moments p
    (fun i => (hp i).1) (fun i => (hp i).2)
  have h_a : ∫ ω, (if ω i then (1:ℝ) else 0) ∂μWeighted p hp = p i := h_moments.1 i
  have h_b : ∫ ω, (if ω j then (1:ℝ) else 0) ∂μWeighted p hp = p j := h_moments.1 j
  have h_ab : ∫ ω, (if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0)
      ∂μWeighted p hp = p i * p j := h_moments.2 i j hij
  have h_one : ∫ _ : BoolCube n, (1:ℝ) ∂μWeighted p hp = 1 := by
    haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
    simp
  haveI hprob : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
  have h_expand : ∀ ω : BoolCube n,
      (2 * (if ω i then (1:ℝ) else 0) - 1) * (2 * (if ω j then (1:ℝ) else 0) - 1)
      = 4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0) - 2 * (if ω j then (1:ℝ) else 0) + 1 := by
    intro ω; ring
  simp_rw [h_expand]
  have h_add : ∫ ω, (4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0) - 2 * (if ω j then (1:ℝ) else 0) + 1)
      ∂μWeighted p hp
      = (∫ ω, (4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0) - 2 * (if ω j then (1:ℝ) else 0))
        ∂μWeighted p hp) + ∫ _ : BoolCube n, (1:ℝ) ∂μWeighted p hp := by
    apply integral_add Integrable.of_finite Integrable.of_finite
  rw [h_add, h_one]
  have h_sub1 : ∫ ω, (4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0) - 2 * (if ω j then (1:ℝ) else 0))
      ∂μWeighted p hp
      = (∫ ω, (4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0)) ∂μWeighted p hp)
        - ∫ ω, 2 * (if ω j then (1:ℝ) else 0) ∂μWeighted p hp := by
    apply integral_sub Integrable.of_finite Integrable.of_finite
  rw [h_sub1, integral_const_mul, h_b]
  have h_sub2 : ∫ ω, (4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        - 2 * (if ω i then (1:ℝ) else 0)) ∂μWeighted p hp
      = (∫ ω, 4 * ((if ω i then (1:ℝ) else 0) * (if ω j then (1:ℝ) else 0))
        ∂μWeighted p hp) - ∫ ω, 2 * (if ω i then (1:ℝ) else 0) ∂μWeighted p hp := by
    apply integral_sub Integrable.of_finite Integrable.of_finite
  rw [h_sub2, integral_const_mul, integral_const_mul, h_ab, h_a]
  ring

theorem weighted_coord_smul_sq {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) (a : ℝ) :
    ∫ ω, (a * coord n i ω) ^ 2 ∂μWeighted p hp = a ^ 2 := by
  have h1 : ∀ ω : BoolCube n, (a * coord n i ω) ^ 2 = a ^ 2 := by
    intro ω
    rw [mul_pow, coord_sq n i ω, mul_one]
  simp_rw [h1]
  haveI : IsProbabilityMeasure (μWeighted p hp) := μWeighted_isProbability hp
  simp

theorem μWeighted_uniform {n : ℕ}
    (hp : ∀ i, 0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1) :
    μWeighted (fun _ : Fin n => (1/2 : ℝ)) hp = μUnif n := by
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro ω
  rw [μUnif_apply_singleton_pow]
  have h_toReal := localIndepPMF_toReal_apply (fun _ : Fin n => (1/2 : ℝ))
    (fun i => (hp i).1) (fun i => (hp i).2) ω
  have h_prod : ∏ i : Fin n, (if ω i then (1/2 : ℝ) else 1 - 1/2) = (1/2) ^ n := by
    have h_each : ∀ i : Fin n, (if ω i then (1/2 : ℝ) else 1 - 1/2) = 1/2 := by
      intro i
      cases h : ω i <;> simp [h] <;> norm_num
    simp_rw [h_each]
    simp [Finset.prod_const, Finset.card_univ]
  rw [h_prod] at h_toReal
  have h_meas : MeasurableSet ({ω} : Set (BoolCube n)) := MeasurableSet.singleton ω
  have h_single : μWeighted (fun _ : Fin n => (1/2 : ℝ)) hp {ω}
      = localIndepPMF (fun _ : Fin n => (1/2 : ℝ))
        (fun i => (hp i).1) (fun i => (hp i).2) ω :=
    PMF.toMeasure_apply_singleton _ ω h_meas
  rw [h_single]
  have h_ne_top : localIndepPMF (fun _ : Fin n => (1/2 : ℝ))
      (fun i => (hp i).1) (fun i => (hp i).2) ω ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have h_ofReal : localIndepPMF (fun _ : Fin n => (1/2 : ℝ))
      (fun i => (hp i).1) (fun i => (hp i).2) ω
      = ENNReal.ofReal ((1/2 : ℝ) ^ n) := by
    have h_eq := ENNReal.ofReal_toReal h_ne_top
    rw [h_toReal] at h_eq
    exact h_eq.symm
  rw [h_ofReal]
  rw [ENNReal.ofReal_pow (by positivity)]
  have h12 : (1/2 : ℝ) = 2⁻¹ := by norm_num
  rw [h12, ENNReal.ofReal_inv_of_pos (by norm_num)]
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  rw [h2, ← ENNReal.inv_pow]

theorem coord_mean_of_uniform_weights (n : ℕ) (i : Fin n)
    (hp : ∀ i, 0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1) :
    ∫ ω, coord n i ω ∂μWeighted (fun _ : Fin n => (1/2 : ℝ)) hp = 0 := by
  have h := weighted_coord_mean hp i
  rw [h]
  norm_num

/-! ## (b) Concrete `Fin 2` fixtures: four realized outcomes -/

/-- Outcome `(-1, -1)`. -/
def ωFF : BoolCube 2 := fun _ => false

/-- Outcome `(+1, +1)`. -/
def ωTT : BoolCube 2 := fun _ => true

/-- Outcome `(+1, -1)`: first coordinate `true`, second `false`. -/
def ωTF : BoolCube 2 := fun i => i = 0

/-- Outcome `(-1, +1)`: first coordinate `false`, second `true`. -/
def ωFT : BoolCube 2 := fun i => i = 1

theorem outcomes_two_card : Fintype.card (BoolCube 2) = 4 := by decide

theorem outcomes_two_univ :
    (Finset.univ : Finset (BoolCube 2)) = {ωFF, ωFT, ωTF, ωTT} := by decide

theorem sum_outcomes_two (f : BoolCube 2 → ℝ) :
    ∑ ω : BoolCube 2, f ω = f ωFF + (f ωFT + (f ωTF + f ωTT)) := by
  rw [show (Finset.univ : Finset (BoolCube 2)) = {ωFF, ωFT, ωTF, ωTT} from outcomes_two_univ]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

theorem μUnif_two_apply_singleton (ω : BoolCube 2) :
    μUnif 2 {ω} = (4 : ℝ≥0∞)⁻¹ := by
  unfold μUnif
  rw [Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ ω),
    Finset.card_univ, outcomes_two_card]
  norm_num

theorem μUnif_two_real_singleton (ω : BoolCube 2) :
    (μUnif 2).real {ω} = 1 / 4 := by
  rw [MeasureTheory.measureReal_def, μUnif_two_apply_singleton]
  norm_num

theorem coord_two_values :
    coord 2 0 ωTF = 1 ∧ coord 2 1 ωTF = -1
      ∧ coord 2 0 ωFT = -1 ∧ coord 2 1 ωFT = 1
      ∧ coord 2 0 ωFF = -1 ∧ coord 2 1 ωFF = -1
      ∧ coord 2 0 ωTT = 1 ∧ coord 2 1 ωTT = 1 := by
  simp [coord, cubeVal, ωTF, ωFT, ωFF, ωTT]

theorem sum_coord_two_zero (i : Fin 2) :
    ∑ ω : BoolCube 2, coord 2 i ω = 0 := by
  rw [sum_outcomes_two]
  fin_cases i <;> simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]

theorem sum_coord_two_sq (i : Fin 2) :
    ∑ ω : BoolCube 2, (coord 2 i ω) ^ 2 = 4 := by
  rw [sum_outcomes_two]
  fin_cases i <;> simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT] <;> norm_num

theorem sum_coord_two_cross :
    ∑ ω : BoolCube 2, coord 2 0 ω * coord 2 1 ω = 0 := by
  rw [sum_outcomes_two]
  simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]

theorem sum_coord_two_self :
    ∑ ω : BoolCube 2, coord 2 0 ω * coord 2 0 ω = 4 := by
  rw [sum_outcomes_two]
  simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]
  norm_num

theorem integral_coord_two_zero (i : Fin 2) :
    ∫ ω, coord 2 i ω ∂μUnif 2 = 0 := by
  exact coord_mean 2 i

theorem integral_coord_two_second (i : Fin 2) :
    ∫ ω, (coord 2 i ω) ^ 2 ∂μUnif 2 = 1 := by
  exact coord_second_moment 2 i

theorem integral_coord_two_cross :
    ∫ ω, coord 2 0 ω * coord 2 1 ω ∂μUnif 2 = 0 := by
  exact coord_cross_moment (show (0 : Fin 2) ≠ 1 by decide)

theorem integral_coord_two_shared :
    ∫ ω, coord 2 0 ω * coord 2 0 ω ∂μUnif 2 = 1 := by
  exact coord_self_moment 2 0

theorem integral_two_scaling (a : ℝ) :
    ∫ ω, (a * coord 2 0 ω) ^ 2 ∂μUnif 2 = a ^ 2 := by
  exact integral_smul_coord_sq 2 0 a

theorem integral_two_coord_add_sq :
    ∫ ω, (coord 2 0 ω + coord 2 1 ω) ^ 2 ∂μUnif 2 = 2 := by
  rw [integral_unif_eq_sum, sum_outcomes_two]
  simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]
  norm_num

theorem integral_two_coord_sub_sq :
    ∫ ω, (coord 2 0 ω - coord 2 1 ω) ^ 2 ∂μUnif 2 = 2 := by
  rw [integral_unif_eq_sum, sum_outcomes_two]
  simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]
  norm_num

theorem integral_two_shared_add_sq :
    ∫ ω, (coord 2 0 ω + coord 2 0 ω) ^ 2 ∂μUnif 2 = 4 := by
  rw [integral_unif_eq_sum, sum_outcomes_two]
  simp [coord, cubeVal, ωFF, ωFT, ωTF, ωTT]
  norm_num

end MathlibExtTest.Probability.Statistics.Measurement.FiniteFixtures
