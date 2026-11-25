/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.CDF
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Fisher's geometric model: the beneficial-mutation probability

The optimum is at `0` in `EuclideanSpace ℝ (Fin n)`; the phenotype is a point `a`
(at distance `‖a‖` from the optimum). A mutation of size `r` in a uniformly random
direction is modelled through the Gaussian representation of the uniform
distribution on the sphere: for `G` with the standard Gaussian law, the direction
is `‖G‖⁻¹ • G` (which is `0` on the event `G = 0`, null when `n ≥ 1`; in dimension `0`
the only point is `0` and the beneficial probability is `0`). For `r > 0` the mutant is
beneficial iff `⟪a, u⟫ < -r / 2` for the unit direction `u`; the beneficial probability
depends only on `‖a‖`, is `1/2` below the one-dimensional cutoff `r < 2‖a‖`
(and `0` beyond it) when `r > 0` and `‖a‖ > 0`, and, for fixed `z = ‖a‖ > 0` and `x > 0`,
in the large-dimension limit with `x = r √n / (2z)` held fixed tends to `1 - Φ(x)` for
`Φ` the standard normal cdf (Fisher 1930; Orr 1998).

## Main results

* `gaussDirection`, `beneficialProb`: the Gaussian-representation direction and
  the beneficial probability.
* `norm_add_smul_lt_iff_inner_lt`, `norm_add_smul_lt_iff_div_lt`: the exact
  beneficial criterion and its cosine form.
* `beneficialProb_zero_size`, `beneficialProb_at_optimum`: degenerate endpoints.
* `beneficialProb_eq_of_norm_eq`: the probability depends only on `‖a‖`.
* `beneficialProb_one_dim`: the one-dimensional exact value.
* `tendsto_beneficialProb`: the large-dimension limit.

## References

* R. A. Fisher, *The Genetical Theory of Natural Selection*, Clarendon, 1930.
* H. A. Orr, "The population genetics of adaptation: the distribution of
  factors fixed during adaptive evolution", *Evolution* 52 (1998), 935–949.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace MathlibExt.Biology.PopulationGenetics.Classical.FisherGeometric

variable {n : ℕ}

/-- The random direction obtained from a Gaussian vector `G` by normalization
(the Gaussian representation of a uniform direction on the unit sphere). For
`G = 0` the convention `0⁻¹ = 0` makes it `0`, an event of probability `0`
under the standard Gaussian law when `n ≥ 1`. -/
noncomputable def gaussDirection (G : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ‖G‖⁻¹ • G

/-- The probability that a mutation of size `r` in a uniformly random direction
(modelled by the Gaussian representation) moves the phenotype `a` strictly closer
to the optimum at `0`. This reading needs `n ≥ 1`, where `G = 0` has probability `0`, and
`r ≥ 0` (for `r < 0` the displacement has length `|r|` when `G ≠ 0`, so almost surely). In
dimension `0` the space is `{0}`, `G = 0` surely, `gaussDirection G = 0` by the convention
`0⁻¹ = 0`, the event is empty and the probability is `0`. -/
noncomputable def beneficialProb (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin n))).real
    {G | ‖a + r • gaussDirection G‖ < ‖a‖}

/-- **Exact beneficial criterion.** For a phenotype `a`, mutation size `r > 0` and
a unit direction `u`, the mutant is closer to the optimum iff
`⟪a, u⟫ < -r / 2`; with `z = ‖a‖ > 0` this is `cos θ < -r / (2z)` for
`cos θ = ⟪a, u⟫ / z`. -/
theorem norm_add_smul_lt_iff_inner_lt {a u : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ = 1) :
    ‖a + r • u‖ < ‖a‖ ↔ ⟪a, u⟫ < -r / 2 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), norm_add_sq_real, norm_smul,
    real_inner_smul_right, hu, Real.norm_eq_abs, abs_of_pos hr]
  constructor <;> intro h <;> nlinarith

/-- The criterion in the `cos θ` form: for a mutation size `r > 0`, a unit direction `u`
(`‖u‖ = 1`) and `z = ‖a‖ > 0` the distance to the optimum, the mutant is closer to the optimum
iff `⟪a, u⟫ / z < -r / (2 * z)`. Here `cos θ = ⟪a, u⟫ / z`, with `θ` the angle between `u` and
the outward radial direction `a / z` (from the optimum to the phenotype). -/
theorem norm_add_smul_lt_iff_div_lt {a u : EuclideanSpace ℝ (Fin n)} {r z : ℝ}
    (hr : 0 < r) (hz : 0 < z) (ha : ‖a‖ = z) (hu : ‖u‖ = 1) :
    ‖a + r • u‖ < ‖a‖ ↔ ⟪a, u⟫ / z < -r / (2 * z) := by
  subst ha
  rw [norm_add_smul_lt_iff_inner_lt hr hu, ← div_div, div_lt_div_iff_of_pos_right hz]

/-- Fitness form: if fitness is a strictly decreasing function `φ` of the distance
to the optimum, beneficial means exactly `‖a + r • u‖ < ‖a‖`. -/
theorem fitness_lt_iff {a u : EuclideanSpace ℝ (Fin n)} {r : ℝ} {φ : ℝ → ℝ}
    (hφ : StrictAnti φ) :
    φ ‖a‖ < φ ‖a + r • u‖ ↔ ‖a + r • u‖ < ‖a‖ := by
  exact hφ.lt_iff_gt

/-- Endpoint `r = 0` (no displacement): the beneficial probability is `0`. -/
theorem beneficialProb_zero_size (a : EuclideanSpace ℝ (Fin n)) :
    beneficialProb a 0 = 0 := by
  simp [beneficialProb]

/-- Endpoint `z = 0` (phenotype at the optimum): the beneficial probability is `0`
for every mutation size. -/
theorem beneficialProb_at_optimum (r : ℝ) :
    beneficialProb (0 : EuclideanSpace ℝ (Fin n)) r = 0 := by
  simp [beneficialProb, not_lt.2 (norm_nonneg _)]

private theorem measurableSet_beneficial {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) (r : ℝ) :
    MeasurableSet {G : EuclideanSpace ℝ (Fin m) | ‖a + r • gaussDirection G‖ < ‖a‖} := by
  unfold gaussDirection
  exact measurableSet_lt (by fun_prop) measurable_const

/-- The beneficial probability depends on the phenotype only through its distance
`‖a‖` to the optimum (rotational invariance). -/
theorem beneficialProb_eq_of_norm_eq {a a' : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (h : ‖a‖ = ‖a'‖) :
    beneficialProb a r = beneficialProb a' r := by
  obtain ⟨f, hfa⟩ : ∃ f : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      f a = a' := ⟨_, Submodule.reflection_sub h⟩
  have hmp : MeasurePreserving f (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨f.continuous.measurable, stdGaussian_map f⟩
  have key (G : EuclideanSpace ℝ (Fin n)) :
      ‖a' + r • gaussDirection (f G)‖ = ‖a + r • gaussDirection G‖ := by
    rw [← hfa, gaussDirection, gaussDirection, f.norm_map, ← map_smul, ← map_smul, ← map_add,
      f.norm_map]
  have hset : {G : EuclideanSpace ℝ (Fin n) | ‖a + r • gaussDirection G‖ < ‖a‖} =
      f ⁻¹' {G | ‖a' + r • gaussDirection G‖ < ‖a'‖} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, key, h]
  rw [beneficialProb, beneficialProb, hset,
    hmp.measureReal_preimage (measurableSet_beneficial a' r).nullMeasurableSet]

private theorem measurePreserving_coord {m : ℕ} (i : Fin m) :
    MeasurePreserving (fun G : EuclideanSpace ℝ (Fin m) => G i)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) (gaussianReal 0 1) := by
  simpa using measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin m)))
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosSemidef.one (i := i)

private theorem gaussianReal_real_Ioi_zero : (gaussianReal 0 1).real (Set.Ioi 0) = 1 / 2 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hmp : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)⟩
  have hsymm : (gaussianReal 0 1).real (Set.Iic 0) = (gaussianReal 0 1).real (Set.Ioi 0) := by
    rw [← measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1) (a := (0 : ℝ))),
      ← hmp.measureReal_preimage measurableSet_Ioi.nullMeasurableSet]
    congr 1
    ext x
    simp
  have hcompl := measureReal_compl (μ := gaussianReal 0 1) (measurableSet_Ioi (a := (0 : ℝ)))
  rw [Set.compl_Ioi, probReal_univ] at hcompl
  linarith

/-- For a phenotype away from the optimum and a positive mutation size, the beneficial
probability is the standard Gaussian probability of `{G | r / (2 ‖a‖) * ‖G‖ < G i}`,
for any coordinate `i`. -/
private theorem beneficialProb_eq_coord {m : ℕ} (i : Fin m) {a : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (ha : 0 < ‖a‖) (hr : 0 < r) :
    beneficialProb a r =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).real {G | r / (2 * ‖a‖) * ‖G‖ < G i} := by
  have hnorm : ‖-(‖a‖ • EuclideanSpace.single i (1 : ℝ))‖ = ‖a‖ := by
    rw [norm_neg, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_norm]
  rw [beneficialProb_eq_of_norm_eq hnorm.symm, beneficialProb]
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq]
  rcases eq_or_ne G 0 with rfl | hG
  · simp [gaussDirection]
  · have hGpos : 0 < ‖G‖ := norm_pos_iff.2 hG
    have hu : ‖gaussDirection G‖ = 1 := by
      rw [gaussDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hGpos.ne']
    rw [norm_add_smul_lt_iff_inner_lt hr hu, gaussDirection, inner_neg_left, real_inner_smul_left,
      real_inner_smul_right, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    have e1 : -(‖a‖ * (‖G‖⁻¹ * G i)) = -(‖a‖ * G i / ‖G‖) := by ring
    have hR : r / (2 * ‖a‖) * ‖G‖ < G i ↔ r * ‖G‖ < G i * (2 * ‖a‖) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    rw [e1, neg_div, neg_lt_neg_iff, lt_div_iff₀ hGpos, hR]
    constructor <;> intro h <;> linarith

/-- **One trait, exact value.** In dimension `1`, a mutation of size `r > 0` at distance
`‖a‖ > 0` from the optimum is beneficial with probability `1 / 2` if `r < 2‖a‖` and
with probability `0` otherwise. -/
theorem beneficialProb_one_dim {a : EuclideanSpace ℝ (Fin 1)} {r : ℝ}
    (ha : 0 < ‖a‖) (hr : 0 < r) :
    beneficialProb a r = if r < 2 * ‖a‖ then 1 / 2 else 0 := by
  have hnormG (G : EuclideanSpace ℝ (Fin 1)) : ‖G‖ = |G 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  have hk0 : 0 < r / (2 * ‖a‖) := by positivity
  rw [beneficialProb_eq_coord 0 ha hr]
  split_ifs with hlt
  · have hk1 : r / (2 * ‖a‖) < 1 := (div_lt_one (by positivity)).2 hlt
    have hset : {G : EuclideanSpace ℝ (Fin 1) | r / (2 * ‖a‖) * ‖G‖ < G 0} =
        (fun G : EuclideanSpace ℝ (Fin 1) => G 0) ⁻¹' Set.Ioi 0 := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
      rw [hnormG G]
      constructor
      · intro h
        rcases le_or_gt (G 0) 0 with hle | hpos
        · rw [abs_of_nonpos hle] at h
          nlinarith
        · exact hpos
      · intro h
        rw [abs_of_pos h]
        nlinarith
    rw [hset, (measurePreserving_coord 0).measureReal_preimage measurableSet_Ioi.nullMeasurableSet,
      gaussianReal_real_Ioi_zero]
  · have hk1 : 1 ≤ r / (2 * ‖a‖) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [not_lt.1 hlt]
    have hset : {G : EuclideanSpace ℝ (Fin 1) | r / (2 * ‖a‖) * ‖G‖ < G 0} = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hnormG G]
      nlinarith [le_abs_self (G 0), abs_nonneg (G 0)]
    rw [hset, measureReal_empty]

private theorem integral_sq_gaussianReal : ∫ t, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

private theorem memLp_sq_gaussianReal : MemLp (fun t : ℝ => t ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have h4 : MemLp id ((4 : ℕ) : ENNReal) (gaussianReal 0 1) := by
    simpa using memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by simp)
  refine h4.integrable_norm_pow'.congr (ae_of_all _ fun x => ?_)
  simp only [id, Real.norm_eq_abs]
  rw [Even.pow_abs ⟨2, rfl⟩]
  ring

private theorem integral_sq_eval {m : ℕ} (i : Fin m) :
    ∫ ω, (ω i) ^ 2 ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = 1 := by
  have h := integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i)
    (f := fun t : ℝ => t ^ 2) (by fun_prop)
  rw [h, integral_sq_gaussianReal]

/-- Chebyshev bound: the normalized norm `‖G‖ / √m` of a standard Gaussian vector
deviates from `1` by at least `δ` with probability at most `Var[t ^ 2] / (δ ^ 2 m)`,
for `t` standard normal. -/
private theorem measureReal_norm_dev_le {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {G | δ ≤ |‖G‖ / Real.sqrt m - 1|} ≤
      Var[fun t : ℝ => t ^ 2; gaussianReal 0 1] / δ ^ 2 / m := by
  have hmpL : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    ⟨WithLp.measurable_toLp 2 _, map_pi_eq_stdGaussian⟩
  have hmeas : MeasurableSet {G : EuclideanSpace ℝ (Fin m) | δ ≤ |‖G‖ / Real.sqrt m - 1|} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← hmpL.measureReal_preimage hmeas.nullMeasurableSet]
  have hmem_i (i : Fin m) : MemLp (fun ω : Fin m → ℝ => (ω i) ^ 2) 2
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
    memLp_sq_gaussianReal.comp_measurePreserving (measurePreserving_eval _ i)
  have hmemY : MemLp (∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) 2
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
    memLp_finsetSum' _ (fun i _ => hmem_i i)
  have hmean : ∫ ω, (∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) ω
      ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = m := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun i _ => (hmem_i i).integrable one_le_two)]
    simp [integral_sq_eval]
  have hvar : Var[∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2;
      Measure.pi (fun _ : Fin m => gaussianReal 0 1)] =
      m * Var[fun t : ℝ => t ^ 2; gaussianReal 0 1] := by
    rw [variance_sum_pi (X := fun _ t => t ^ 2) (fun _ => memLp_sq_gaussianReal)]
    simp
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsub : (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹'
      {G | δ ≤ |‖G‖ / Real.sqrt m - 1|} ⊆
      {ω | δ * m ≤ |(∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) ω -
        ∫ ω, (∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) ω
          ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))|} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    rw [hmean, Finset.sum_apply]
    have hsq : ‖(WithLp.toLp 2 ω : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, (ω i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    rw [← hsq]
    set s := ‖(WithLp.toLp 2 ω : EuclideanSpace ℝ (Fin m))‖ / Real.sqrt m with hs
    have hsqrt : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm'.le
    have hNs : ‖(WithLp.toLp 2 ω : EuclideanSpace ℝ (Fin m))‖ = s * Real.sqrt m := by
      rw [hs, div_mul_cancel₀ _ (Real.sqrt_pos.2 hm').ne']
    have hs0 : 0 ≤ s := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have hfac : (s * Real.sqrt m) ^ 2 - m = m * ((s - 1) * (s + 1)) := by
      rw [mul_pow, hsqrt]
      ring
    rw [hNs, hfac, abs_mul, abs_mul, abs_of_pos hm', abs_of_nonneg (by linarith : (0 : ℝ) ≤ s + 1)]
    have h1 : δ ≤ |s - 1| * (s + 1) := by nlinarith [abs_nonneg (s - 1)]
    nlinarith
  have hcheb := meas_ge_le_variance_div_sq hmemY (by positivity : 0 < δ * m)
  calc (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real
        ((WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹'
          {G | δ ≤ |‖G‖ / Real.sqrt m - 1|})
      ≤ (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real
          {ω | δ * m ≤ |(∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) ω -
            ∫ ω, (∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2) ω
              ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))|} := measureReal_mono hsub
    _ ≤ Var[∑ i, fun ω : Fin m → ℝ => (ω i) ^ 2;
          Measure.pi (fun _ : Fin m => gaussianReal 0 1)] / (δ * m) ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (by positivity))
          hcheb
    _ = Var[fun t : ℝ => t ^ 2; gaussianReal 0 1] / δ ^ 2 / m := by
        rw [hvar]
        field_simp

private theorem tendsto_measureReal_norm_dev {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
      {G | δ ≤ |‖G‖ / Real.sqrt (n + 1) - 1|}) atTop (𝓝 0) := by
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (Var[fun t : ℝ => t ^ 2; gaussianReal 0 1] / δ ^ 2)
  rw [mul_zero] at h0
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) h0
  have h := measureReal_norm_dev_le (m := n + 1) (Nat.succ_pos n) hδ
  push_cast at h
  rw [mul_one_div]
  exact h

private theorem gaussianPDFReal_zero_one_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have h1 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by linarith [Real.two_le_pi]))
  have h2 : Real.exp (-x ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ 1 * 1 :=
        mul_le_mul h1 h2 (Real.exp_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem gaussianReal_le_volume (s : Set ℝ) : gaussianReal 0 1 s ≤ volume s := by
  rw [gaussianReal_apply 0 one_ne_zero s]
  calc ∫⁻ x in s, gaussianPDF 0 1 x ≤ ∫⁻ _ in s, 1 :=
        lintegral_mono fun x => ENNReal.ofReal_le_one.2 (gaussianPDFReal_zero_one_le_one x)
    _ = volume s := by rw [setLIntegral_const, one_mul]

/-- Increment bound for the standard Gaussian upper tail: for `a ≤ b`, the tail at `a`
exceeds the tail at `b` by at most `b - a`. -/
private theorem gaussianReal_real_Ioi_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioi a) ≤ (gaussianReal 0 1).real (Set.Ioi b) + (b - a) := by
  have hsub : Set.Ioi a ⊆ Set.Ioc a b ∪ Set.Ioi b := by
    intro y hy
    rcases le_or_gt y b with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr h
  have hIoc : (gaussianReal 0 1).real (Set.Ioc a b) ≤ b - a := by
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hab) ?_
    calc gaussianReal 0 1 (Set.Ioc a b) ≤ volume (Set.Ioc a b) := gaussianReal_le_volume _
      _ = ENNReal.ofReal (b - a) := Real.volume_Ioc
  calc (gaussianReal 0 1).real (Set.Ioi a)
      ≤ (gaussianReal 0 1).real (Set.Ioc a b ∪ Set.Ioi b) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real (Set.Ioc a b) + (gaussianReal 0 1).real (Set.Ioi b) :=
        measureReal_union_le _ _
    _ ≤ (gaussianReal 0 1).real (Set.Ioi b) + (b - a) := by linarith

private theorem one_sub_cdf_gaussianReal (x : ℝ) :
    1 - cdf (gaussianReal 0 1) x = (gaussianReal 0 1).real (Set.Ioi x) := by
  rw [cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]

/-- **Large-dimension limit.** Fix the distance `z > 0` to the optimum and
`x > 0`; in dimension `n + 1`, along mutation sizes
`rₙ = 2 z x / √(n + 1)` (that is, `x = rₙ √(n + 1) / (2z)`), the beneficial
probability tends to `1 - Φ(x)`, where `Φ` is the standard normal cdf.
The `n + 1` indexing makes every dimension positive, so phenotypes with
`‖a n‖ = z` exist at every index. -/
theorem tendsto_beneficialProb {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (a : ∀ n : ℕ, EuclideanSpace ℝ (Fin (n + 1))) (ha : ∀ n, ‖a n‖ = z) :
    Tendsto (fun n : ℕ => beneficialProb (a n) (2 * z * x / Real.sqrt (n + 1))) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) x)) := by
  have hP (n : ℕ) : beneficialProb (a n) (2 * z * x / Real.sqrt (n + 1)) =
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {G | x * (‖G‖ / Real.sqrt (n + 1)) < G 0} := by
    have hs : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by positivity)
    rw [beneficialProb_eq_coord 0 (by rw [ha n]; exact hz) (by positivity), ha n]
    congr 1
    ext G
    have hk : 2 * z * x / Real.sqrt (n + 1) / (2 * z) * ‖G‖ = x * (‖G‖ / Real.sqrt (n + 1)) := by
      field_simp
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hk]
  simp only [hP]
  rw [one_sub_cdf_gaussianReal, Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * x) with hδ
  have hδpos : 0 < δ := by positivity
  have hxδ : x * δ = ε / 2 := by
    rw [hδ]
    field_simp
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_measureReal_norm_dev hδpos) (ε / 2)
    (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hD := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hD
  have hlaw (c : ℝ) : (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real {G | c < G 0} =
      (gaussianReal 0 1).real (Set.Ioi c) :=
    (measurePreserving_coord (m := n + 1) 0).measureReal_preimage
      measurableSet_Ioi.nullMeasurableSet
  have hup : (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {G | x * (‖G‖ / Real.sqrt (n + 1)) < G 0} ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real {G | x * (1 - δ) < G 0} +
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {G | δ ≤ |‖G‖ / Real.sqrt (n + 1) - 1|} := by
    refine (measureReal_mono fun G hG => ?_).trans (measureReal_union_le _ _)
    by_cases hGD : δ ≤ |‖G‖ / Real.sqrt (n + 1) - 1|
    · exact Or.inr hGD
    · left
      simp only [Set.mem_ofPred_eq] at hG ⊢
      have h1 : 1 - δ < ‖G‖ / Real.sqrt (n + 1) := by
        linarith [(abs_lt.1 (not_le.1 hGD)).1]
      exact (mul_lt_mul_of_pos_left h1 hx).trans hG
  have hlow : (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real {G | x * (1 + δ) < G 0} ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {G | x * (‖G‖ / Real.sqrt (n + 1)) < G 0} +
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))).real
        {G | δ ≤ |‖G‖ / Real.sqrt (n + 1) - 1|} := by
    refine (measureReal_mono fun G hG => ?_).trans (measureReal_union_le _ _)
    by_cases hGD : δ ≤ |‖G‖ / Real.sqrt (n + 1) - 1|
    · exact Or.inr hGD
    · left
      simp only [Set.mem_ofPred_eq] at hG ⊢
      have h1 : ‖G‖ / Real.sqrt (n + 1) < 1 + δ := by
        linarith [(abs_lt.1 (not_le.1 hGD)).2]
      exact (mul_lt_mul_of_pos_left h1 hx).trans hG
  rw [hlaw (x * (1 - δ))] at hup
  rw [hlaw (x * (1 + δ))] at hlow
  have hL1 := gaussianReal_real_Ioi_le (a := x * (1 - δ)) (b := x) (by nlinarith)
  have hL2 := gaussianReal_real_Ioi_le (a := x) (b := x * (1 + δ)) (by nlinarith)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> nlinarith

end MathlibExt.Biology.PopulationGenetics.Classical.FisherGeometric
