/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemScore
public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import MathlibExt.Probability.Statistics.FisherInformation
public import MathlibExt.Probability.Statistics.VectorInference

/-!
# Finite two-parameter-logistic test information

The existing vector Fisher-information operator of the finite 2PL model,
evaluated as a quadratic form at `1`, is the sum over items of
`a_j^2 p_j (1 - p_j)` with `p_j = sigmoid (a_j (theta - b_j))`. It is
nonnegative, and strictly positive exactly when some discrimination is
nonzero. The scalar Fisher information at the same parameter agrees.
-/

@[expose] public section

open MeasureTheory

/-! ## New result: 2PL test information from the existing operator

The public interface is `Measurement.vector_fisherInformation_twoPL`
together with its four named clauses:
`twoPL_fisherInformation_quadraticForm`, `twoPL_fisherInformation_eq_scalar`,
`twoPL_information_nonneg`, and `twoPL_information_pos_iff`.  The private
helpers discharge, for this finite model, the analytic hypotheses of the
upstream operator lemmas; they are not part of the public interface. -/

namespace MathlibExt.Probability.Statistics.Measurement

open scoped RealInnerProductSpace

/-- Private helper: the 2PL density at `θ` is strictly positive at every
response pattern (a finite product of logistic values and one-minus
logistic values, via `localIndepPMF_toReal_apply`). -/
private theorem twoPL_density_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) (Y : ι → Bool) :
    0 < (twoPLPMF a b θ Y).toReal := by
  have h : (twoPLPMF a b θ Y).toReal
      = ∏ i, (if Y i then Real.sigmoid (a i * (θ - b i))
        else 1 - Real.sigmoid (a i * (θ - b i))) :=
    localIndepPMF_toReal_apply _ _ _ Y
  rw [h]
  apply Finset.prod_pos
  intro i _
  split
  · exact Real.sigmoid_pos _
  · have h1 := Real.sigmoid_lt_one (a i * (θ - b i))
    linarith

/-- Private helper: the 2PL density at `θ` is measurable (the outcome
type `ι → Bool` is finite and discrete). -/
private theorem twoPL_density_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    Measurable (fun Y : ι → Bool => (twoPLPMF a b θ Y).toReal) := by
  exact Measurable.of_discrete

/-- Private helper: the 2PL density is differentiable in the scalar
parameter at `θ` for every response pattern (a finite product of logistic
functions of affine functions). -/
private theorem twoPL_density_differentiable {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a b : ι → ℝ) (θ : ℝ) (Y : ι → Bool) :
    DifferentiableAt ℝ (fun t => (twoPLPMF a b t Y).toReal) θ := by
  have hfun : (fun t => (twoPLPMF a b t Y).toReal)
      = fun t => ∏ i, (if Y i then Real.sigmoid (a i * (t - b i))
        else 1 - Real.sigmoid (a i * (t - b i))) := by
    funext t
    exact localIndepPMF_toReal_apply _ _ _ Y
  rw [hfun]
  have hprod : (fun t : ℝ => ∏ i, (if Y i then Real.sigmoid (a i * (t - b i))
      else 1 - Real.sigmoid (a i * (t - b i))))
      = ∏ i, (fun t : ℝ => (if Y i then Real.sigmoid (a i * (t - b i))
        else 1 - Real.sigmoid (a i * (t - b i)))) := by
    funext t
    simp only [Finset.prod_apply]
  rw [hprod]
  apply DifferentiableAt.finsetProd
  intro i _
  have haff : DifferentiableAt ℝ (fun t : ℝ => a i * (t - b i)) θ :=
    (differentiableAt_id.sub_const (b i)).const_mul (a i)
  have hsig : DifferentiableAt ℝ (fun t : ℝ => Real.sigmoid (a i * (t - b i))) θ :=
    differentiableAt_sigmoid.comp θ haff
  by_cases hY : Y i
  · simpa [hY] using hsig
  · simpa [hY] using hsig.const_sub 1

/-- Private helper: the 2PL score is square integrable under its own law
(the outcome type is finite and the law is a probability measure, so the
score takes finitely many values).  This discharges the `MemLp`
hypothesis of `inner_fisherInformation_apply` and
`inner_fisherInformation_self` with no extra assumption. -/
private theorem twoPL_score_memLp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    MemLp (MathlibExt.Probability.Statistics.VectorInference.score
        (fun t Y => (twoPLPMF a b t Y).toReal) θ) 2
      (MathlibExt.Probability.Statistics.FisherInformation.lawOf
        Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ) := by
  rw [twoPL_lawOf_eq_toMeasure]
  refine MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable
    (∑ Z, ‖MathlibExt.Probability.Statistics.VectorInference.score
      (fun t Y => (twoPLPMF a b t Y).toReal) θ Z‖) ?_
  filter_upwards with Y
  exact Finset.single_le_sum (fun Z _ => norm_nonneg _) (Finset.mem_univ Y)

/-- **Test information of the two-parameter logistic model.**

For a finite (possibly empty) item type `ι`, arbitrary real
discriminations `a` and difficulties `b`, and scalar ability `θ`, write
`p j = Real.sigmoid (a j * (θ - b j))`.  The quadratic form at `1` of the
existing vector Fisher information operator of the 2PL density (counting
measure on response patterns, density the existing product mass function
through `toReal`, scalar parameter space `ℝ`) satisfies:

1. it is the finite test information `∑ j, (a j)^2 * p j * (1 - p j)`;
2. it is the existing scalar Fisher information of the same density
   family at `θ`;
3. the sum is nonnegative, with no further hypothesis;
4. the sum is strictly positive whenever some discrimination is nonzero.

No new information definition is introduced and no slope sign, slope
nonvanishing or nonemptiness hypothesis is imposed: conclusions 1–3 hold
also for the empty test (both sides `0`) and for zero slopes, and
conclusion 4 is sharp, since a test whose discriminations all vanish has
information `0`.  The familiar package "nonempty test, all slopes
strictly positive" therefore has strictly positive information, as the
tests below record. -/
theorem vector_fisherInformation_twoPL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    (⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ 1, (1 : ℝ)⟫
      = ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j)))))
    ∧ (⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ 1, (1 : ℝ)⟫
      = MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
          Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ)
    ∧ (0 ≤ ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j)))))
    ∧ ((∃ j, a j ≠ 0) ↔ 0 < ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j))))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmem := twoPL_score_memLp a b θ
    have happly := VectorInference.inner_fisherInformation_apply (E := ℝ)
      (𝓧 := ι → Bool) (ν := Measure.count)
      (p := fun t Y => (twoPLPMF a b t Y).toReal) (θ := θ) hmem
      (1 : ℝ) (1 : ℝ)
    rw [happly, twoPL_lawOf_eq_toMeasure]
    have hinner : ∀ s : ℝ, ⟪s, (1 : ℝ)⟫ = s := fun s => by simp
    simp only [hinner, twoPL_score_eq_sum]
    have hmaster : ∀ f : (ι → Bool) → ℝ,
        Integrable f (twoPLPMF a b θ).toMeasure := by
      intro f
      refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
        (∑ Z, ‖f Z‖) ?_
      filter_upwards with Y
      exact Finset.single_le_sum (fun Z _ => norm_nonneg _) (Finset.mem_univ Y)
    have hmom1 : ∀ i : ι, ∫ Y, (if Y i then (1 : ℝ) else 0)
        ∂(twoPLPMF a b θ).toMeasure
        = Real.sigmoid (a i * (θ - b i)) := fun i =>
      (localIndepPMF_coordinate_moments _ _ _).1 i
    have hmom2 : ∀ i k : ι, i ≠ k → ∫ Y, (if Y i then (1 : ℝ) else 0)
        * (if Y k then (1 : ℝ) else 0) ∂(twoPLPMF a b θ).toMeasure
        = Real.sigmoid (a i * (θ - b i)) * Real.sigmoid (a k * (θ - b k)) :=
      fun i k hik => (localIndepPMF_coordinate_moments _ _ _).2 i k hik
    simp only [Fintype.sum_mul_sum]
    rw [integral_finsetSum Finset.univ (fun j _ => hmaster _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum Finset.univ (fun k _ => hmaster _)]
    have hcross : ∀ k : ι, k ≠ j → ∫ Y, (a j * ((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))))
        * (a k * ((if Y k then (1 : ℝ) else 0)
        - Real.sigmoid (a k * (θ - b k)))) ∂(twoPLPMF a b θ).toMeasure = 0 := by
      intro k hkj
      have hexpand : ∀ Y : ι → Bool, (a j * ((if Y j then (1 : ℝ) else 0)
          - Real.sigmoid (a j * (θ - b j))))
          * (a k * ((if Y k then (1 : ℝ) else 0)
          - Real.sigmoid (a k * (θ - b k))))
          = a j * a k * (((if Y j then (1 : ℝ) else 0)
          - Real.sigmoid (a j * (θ - b j)))
          * ((if Y k then (1 : ℝ) else 0)
          - Real.sigmoid (a k * (θ - b k)))) := fun Y => by ring
      simp only [hexpand]
      rw [integral_const_mul]
      have hzero : ∫ Y, (((if Y j then (1 : ℝ) else 0)
          - Real.sigmoid (a j * (θ - b j)))
          * ((if Y k then (1 : ℝ) else 0)
          - Real.sigmoid (a k * (θ - b k)))) ∂(twoPLPMF a b θ).toMeasure
          = 0 := by
        have hexpand2 : ∀ Y : ι → Bool, (((if Y j then (1 : ℝ) else 0)
            - Real.sigmoid (a j * (θ - b j)))
            * ((if Y k then (1 : ℝ) else 0)
            - Real.sigmoid (a k * (θ - b k))))
            = (if Y j then (1 : ℝ) else 0) * (if Y k then (1 : ℝ) else 0)
            - Real.sigmoid (a j * (θ - b j)) * (if Y k then (1 : ℝ) else 0)
            - Real.sigmoid (a k * (θ - b k)) * (if Y j then (1 : ℝ) else 0)
            + Real.sigmoid (a j * (θ - b j))
            * Real.sigmoid (a k * (θ - b k)) := by
          intro Y
          ring
        simp only [hexpand2]
        rw [integral_add (hmaster _) (hmaster _),
          integral_sub (hmaster _) (hmaster _),
          integral_sub (hmaster _) (hmaster _),
          integral_const_mul, integral_const_mul,
          hmom2 j k (Ne.symm hkj), hmom1 j, hmom1 k]
        have hconst : ∫ Y, Real.sigmoid (a j * (θ - b j))
            * Real.sigmoid (a k * (θ - b k)) ∂(twoPLPMF a b θ).toMeasure
            = Real.sigmoid (a j * (θ - b j))
            * Real.sigmoid (a k * (θ - b k)) := by
          simp
        rw [hconst]
        ring
      rw [hzero, mul_zero]
    rw [Finset.sum_eq_single j (fun k _ hkj => hcross k hkj)
      (fun h => absurd (Finset.mem_univ j) h)]
    have hY2 : ∀ Y : ι → Bool, ((if Y j then (1 : ℝ) else 0)) ^ 2
        = (if Y j then (1 : ℝ) else 0) := fun Y => by
      by_cases h : Y j <;> simp [h]
    have hsqpt : ∀ Y : ι → Bool, (a j * ((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))))
        * (a j * ((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))))
        = (a j) ^ 2 * (((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))) ^ 2) := fun Y => by ring
    simp only [hsqpt]
    rw [integral_const_mul]
    have hexpd : ∀ Y : ι → Bool, (((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))) ^ 2)
        = (if Y j then (1 : ℝ) else 0)
        - 2 * Real.sigmoid (a j * (θ - b j)) * (if Y j then (1 : ℝ) else 0)
        + (Real.sigmoid (a j * (θ - b j))) ^ 2 := by
      intro Y
      have h2 := hY2 Y
      calc (((if Y j then (1 : ℝ) else 0) - Real.sigmoid (a j * (θ - b j))) ^ 2)
          = ((if Y j then (1 : ℝ) else 0)) ^ 2
          - 2 * Real.sigmoid (a j * (θ - b j)) * (if Y j then (1 : ℝ) else 0)
          + (Real.sigmoid (a j * (θ - b j))) ^ 2 := by ring
        _ = (if Y j then (1 : ℝ) else 0)
          - 2 * Real.sigmoid (a j * (θ - b j)) * (if Y j then (1 : ℝ) else 0)
          + (Real.sigmoid (a j * (θ - b j))) ^ 2 := by rw [h2]
    simp only [hexpd]
    rw [integral_add (hmaster _) (hmaster _),
      integral_sub (hmaster _) (hmaster _),
      integral_const_mul, hmom1 j]
    have hconst2 : ∫ Y, (Real.sigmoid (a j * (θ - b j))) ^ 2
        ∂(twoPLPMF a b θ).toMeasure
        = (Real.sigmoid (a j * (θ - b j))) ^ 2 := by simp
    rw [hconst2]
    ring
  · have hbridge := VectorInference.inner_fisherInformation_self (E := ℝ)
      (𝓧 := ι → Bool) (ν := Measure.count)
      (p := fun t Y => (twoPLPMF a b t Y).toReal) (θ := θ)
      (fun Y => twoPL_density_pos a b θ Y) (twoPL_density_measurable a b θ)
      (fun Y => twoPL_density_differentiable a b θ Y) (twoPL_score_memLp a b θ)
      (1 : ℝ)
    rw [hbridge]
    show ∫ x, deriv (fun t => (twoPLPMF a b (θ + t • (1 : ℝ)) x).toReal) 0 ^ 2
        / (twoPLPMF a b (θ + 0 • (1 : ℝ)) x).toReal ∂Measure.count
      = ∫ x, deriv (fun t => (twoPLPMF a b t x).toReal) θ ^ 2
        / (twoPLPMF a b θ x).toReal ∂Measure.count
    apply integral_congr_ae
    filter_upwards with x
    have hsmul : ∀ t : ℝ, θ + t • (1 : ℝ) = θ + t := fun t => by
      simp [smul_eq_mul]
    have hderiv : deriv (fun t : ℝ => (twoPLPMF a b (θ + t • (1 : ℝ)) x).toReal) 0
        = deriv (fun t : ℝ => (twoPLPMF a b t x).toReal) θ := by
      have heq : (fun t : ℝ => (twoPLPMF a b (θ + t • (1 : ℝ)) x).toReal)
          = fun t : ℝ => (twoPLPMF a b (θ + t) x).toReal := by
        funext t
        rw [hsmul t]
      rw [heq]
      have hh : HasDerivAt (fun t : ℝ => θ + t) 1 0 :=
        (hasDerivAt_id 0).const_add θ
      have hg : HasDerivAt (fun t : ℝ => (twoPLPMF a b t x).toReal)
          (deriv (fun t : ℝ => (twoPLPMF a b t x).toReal) θ) θ :=
        (twoPL_density_differentiable a b θ x).hasDerivAt
      have hg' : HasDerivAt (fun t : ℝ => (twoPLPMF a b t x).toReal)
          (deriv (fun t : ℝ => (twoPLPMF a b t x).toReal) θ) (θ + 0) := by
        simpa using hg
      have hcomp := HasDerivAt.comp (0 : ℝ) hg' hh
      exact hcomp.deriv.trans (mul_one _)
    rw [hderiv]
    simp only [zero_smul, add_zero]
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (sq_nonneg _)
    apply mul_nonneg (le_of_lt (Real.sigmoid_pos _))
    have h1lt := Real.sigmoid_lt_one (a j * (θ - b j))
    linarith
  · constructor
    · intro hex
      obtain ⟨j0, hj0⟩ := hex
      refine Finset.sum_pos' (fun j _ => ?_) ⟨j0, Finset.mem_univ j0, ?_⟩
      · apply mul_nonneg (sq_nonneg _)
        apply mul_nonneg (le_of_lt (Real.sigmoid_pos _))
        have h1lt := Real.sigmoid_lt_one (a j * (θ - b j))
        linarith
      · apply mul_pos (sq_pos_of_ne_zero hj0)
        apply mul_pos (Real.sigmoid_pos _)
        have h1lt := Real.sigmoid_lt_one (a j0 * (θ - b j0))
        linarith
    · intro hpos
      by_contra hcon
      push_neg at hcon
      have hzero : (∑ j, (a j) ^ 2
            * (Real.sigmoid (a j * (θ - b j))
              * (1 - Real.sigmoid (a j * (θ - b j))))) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hcon j]
        simp
      linarith


/-- The 2PL information quadratic form at `1`, as a named clause of
`vector_fisherInformation_twoPL`. -/
theorem twoPL_fisherInformation_quadraticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ 1, (1 : ℝ)⟫
      = ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j)))) :=
  (vector_fisherInformation_twoPL a b θ).1

/-- The 2PL information quadratic form agrees with the scalar Fisher
information at the same parameter. -/
theorem twoPL_fisherInformation_eq_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    ⟪MathlibExt.Probability.Statistics.VectorInference.fisherInformation
        Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ 1, (1 : ℝ)⟫
      = MathlibExt.Probability.Statistics.FisherInformation.fisherInformation
          Measure.count (fun t Y => (twoPLPMF a b t Y).toReal) θ :=
  (vector_fisherInformation_twoPL a b θ).2.1

/-- The 2PL test information is nonnegative. -/
theorem twoPL_information_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    0 ≤ ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j)))) :=
  (vector_fisherInformation_twoPL a b θ).2.2.1

/-- The 2PL test information is strictly positive exactly when some
discrimination is nonzero. -/
theorem twoPL_information_pos_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    (0 < ∑ j, (a j) ^ 2
          * (Real.sigmoid (a j * (θ - b j))
            * (1 - Real.sigmoid (a j * (θ - b j)))))
      ↔ ∃ j, a j ≠ 0 :=
  (vector_fisherInformation_twoPL a b θ).2.2.2.symm
end MathlibExt.Probability.Statistics.Measurement
