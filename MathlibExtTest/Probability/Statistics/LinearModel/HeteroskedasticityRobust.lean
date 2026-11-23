/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.HeteroskedasticityRobust
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.HeteroskedasticityRobust`

* A concrete heteroskedastic random design: i.i.d. fair signs `ζᵢ, εᵢ ∈ {±1}`, regressor
  `xᵢ = ζᵢ` and error `uᵢ = (2 + ζᵢ) εᵢ`, so `𝔼[u² | ζ = 1] = 9` and `𝔼[u² | ζ = -1] = 1`.
  Every hypothesis of `hc0OLSSandwich_tendsto_ae` is computed from the definitions
  (`Q = 1`, `Ω = 5`), and the OLS HC0 sandwich converges a.s. to `5`.
* A fixed design `x₀ = 1`, `xᵢ = 0` for `i ≥ 1`: the rows are not identically distributed and the
  bread inverse `Q̂ₙ⁻¹ = n` diverges, so neither `hIdent` nor `hQinv` holds and no consistency is
  claimed.
* The robust Wald interval for `β` in the concrete model has asymptotic coverage equal to the
  standard-normal mass of `[-z, z]`; asymptotic normality is supplied by Mathlib's CLT.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open MathlibExt.Probability.Statistics.LinearModel
open MathlibExt.Probability.Statistics.ProcessInference

namespace MathlibExtTest.LinearModelHeteroskedasticityRobust

/-! ### The concrete random design -/

/-- The sign `±1` of a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

/-- Two independent fair signs: the uniform law on `Bool × Bool`. -/
noncomputable def ν : Measure (Bool × Bool) := (4 : ENNReal)⁻¹ • Measure.count

instance : IsProbabilityMeasure ν := ⟨by
  have h4 : ((4 : ℕ) : ENNReal) = 4 := by norm_num
  simp only [ν, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_prod, Fintype.card_bool, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The i.i.d. sample space: one pair of signs `(ζᵢ, εᵢ)` per row. -/
noncomputable def μ : Measure (ℕ → Bool × Bool) := Measure.infinitePi fun _ => ν

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The regressor `xᵢ = ζᵢ` (one coefficient, no intercept). -/
def X (i : ℕ) (ω : ℕ → Bool × Bool) : Fin 1 → ℝ := fun _ => sgn (ω i).1

/-- The heteroskedastic error `uᵢ = (2 + ζᵢ) εᵢ`. -/
def U (i : ℕ) (ω : ℕ → Bool × Bool) : ℝ := (2 + sgn (ω i).1) * sgn (ω i).2

lemma ν_real_singleton (p : Bool × Bool) : ν.real {p} = 1 / 4 := by
  simp [measureReal_def, ν]

lemma map_eval (i : ℕ) : μ.map (fun ω => ω i) = ν := Measure.infinitePi_map_eval _ i

/-- Integrals of functions of one row reduce to the four-point average. -/
lemma integral_row {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (F : Bool × Bool → E) (i : ℕ) :
    ∫ ω, F (ω i) ∂μ = (1 / 4 : ℝ) • (F (true, true) + F (true, false) + F (false, true) +
      F (false, false)) := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable
      (measurable_of_countable F).aestronglyMeasurable, map_eval,
    integral_fintype Integrable.of_finite]
  simp only [ν_real_singleton, Fintype.sum_prod_type, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  simp only [← smul_add]
  abel_nf

lemma integrable_row {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : Bool × Bool → E) (i : ℕ) :
    Integrable (fun ω => F (ω i)) μ := by
  have h : Integrable F (μ.map fun ω => ω i) := by rw [map_eval]; exact Integrable.of_finite
  exact h.comp_measurable (measurable_pi_apply i)

lemma identDistrib_row {E : Type*} [MeasurableSpace E] (F : Bool × Bool → E) (i : ℕ) :
    IdentDistrib (fun ω => F (ω i)) (fun ω => F (ω 0)) μ μ where
  aemeasurable_fst := ((measurable_of_countable F).comp (measurable_pi_apply i)).aemeasurable
  aemeasurable_snd := ((measurable_of_countable F).comp (measurable_pi_apply 0)).aemeasurable
  map_eq := by
    change Measure.map (F ∘ fun ω => ω i) μ = Measure.map (F ∘ fun ω => ω 0) μ
    rw [← Measure.map_map (measurable_of_countable F) (measurable_pi_apply i),
      ← Measure.map_map (measurable_of_countable F) (measurable_pi_apply 0), map_eval, map_eval]

lemma iIndepFun_row {E : Type*} [MeasurableSpace E] (F : Bool × Bool → E) :
    iIndepFun (fun i ω => F (ω i)) μ :=
  iIndepFun_infinitePi (P := fun _ => ν) (X := fun _ => F) fun _ => measurable_of_countable F

/-- One row of the model as a function of its two signs. -/
def row (p : Bool × Bool) : (Fin 1 → ℝ) × ℝ := (fun _ => sgn p.1, (2 + sgn p.1) * sgn p.2)

lemma hJoint : iIndepFun (fun i ω => (X i ω, U i ω)) μ := iIndepFun_row row

lemma hIdent (i : ℕ) :
    IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ :=
  identDistrib_row row i

lemma hMom4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ :=
  integrable_row (fun p => ‖(fun _ => sgn p.1 : Fin 1 → ℝ)‖ ^ 4) 0

lemma hMom2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2 * (U 0 ω) ^ 2) μ :=
  integrable_row (fun p => ‖(fun _ => sgn p.1 : Fin 1 → ℝ)‖ ^ 2 * ((2 + sgn p.1) * sgn p.2) ^ 2) 0

/-- Exogeneity `𝔼[u₀ x₀] = 0`, computed on the four sign patterns. -/
lemma hmeanScore : ∫ ω, U 0 ω • X 0 ω ∂μ = 0 := by
  have h := integral_row (fun p => ((2 + sgn p.1) * sgn p.2) • (fun _ => sgn p.1 : Fin 1 → ℝ)) 0
  refine h.trans ?_
  ext a
  simp [sgn]

/-- The population Gram is the identity: `ζ² = 1`. -/
lemma popGram_eq : popGram (X 0) μ = 1 := by
  ext a b
  rw [Subsingleton.elim a b]
  simp [popGram, X, sgn_mul_self]

lemma hQ : IsUnit (popGram (X 0) μ) := by rw [popGram_eq]; exact isUnit_one

/-- The population meat `𝔼[u² x²] = (9 + 9 + 1 + 1) / 4 = 5`. -/
lemma hc0PopMeat_eq : hc0PopMeat (X 0) (U 0) μ = Matrix.of fun _ _ => 5 := by
  ext a b
  have h := integral_row (fun p => ((2 + sgn p.1) * sgn p.2) ^ 2 * sgn p.1 * sgn p.1) 0
  simp only [hc0PopMeat, Matrix.of_apply, X, U]
  rw [h]
  norm_num [sgn]

lemma hc0PopSandwich_eq : hc0PopSandwich (X 0) (U 0) μ = Matrix.of fun _ _ => 5 := by
  rw [hc0PopSandwich, popGram_eq, hc0PopMeat_eq, inv_one, transpose_one, Matrix.one_mul,
    Matrix.mul_one]

/-- **The OLS HC0 sandwich is consistent in the concrete heteroskedastic design**, with every
hypothesis discharged from the definitions above. -/
theorem hc0OLSSandwich_tendsto_five (β : Fin 1 → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω)
      atTop (𝓝 (Matrix.of fun _ _ => 5)) := by
  have h := hc0OLSSandwich_tendsto_ae β hJoint hIdent hMom4 hMom2 hmeanScore hQ
  rwa [hc0PopSandwich_eq] at h

/-! ### A fixed design where the hypotheses fail -/

/-- A deterministic design: `x₀ = 1` and `xᵢ = 0` for `i ≥ 1`. -/
noncomputable def Xf (i : ℕ) (_ : Unit) : Fin 1 → ℝ := fun _ => if i = 0 then 1 else 0

/-- The sample Gram of the fixed design is `n⁻¹` for `n ≥ 1`: only the first row contributes. -/
lemma olsSampleGram_Xf {n : ℕ} (hn : 1 ≤ n) (a b : Fin 1) :
    olsSampleGram Xf n () a b = (n : ℝ)⁻¹ := by
  simp only [olsSampleGram, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Xf,
    smul_eq_mul]
  rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi]) (fun h => absurd
    (Finset.mem_range.2 (by omega)) h)]
  simp

/-- The bread inverse of the fixed design is `n` and diverges, so `hQinv` fails. -/
lemma not_tendsto_olsSampleGram_inv_Xf (L : ℝ) :
    ¬ Tendsto (fun n : ℕ => (olsSampleGram Xf n ())⁻¹ 0 0) atTop (𝓝 L) := by
  have hev : (fun n : ℕ => (n : ℝ)) =ᶠ[atTop] fun n : ℕ => (olsSampleGram Xf n ())⁻¹ 0 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hG : olsSampleGram Xf n () = Matrix.of fun _ _ => (n : ℝ)⁻¹ := by
      ext a b
      exact olsSampleGram_Xf hn a b
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hinv : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (n : ℝ)⁻¹)⁻¹ =
        Matrix.of fun _ _ => (n : ℝ) := by
      refine Matrix.inv_eq_left_inv ?_
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim a b, hn']
    rw [hG, hinv, Matrix.of_apply]
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_natCast_atTop_atTop.congr' hev) L

/-- The fixed-design rows are not identically distributed, so `hIdent` fails. -/
lemma not_identDistrib_Xf :
    ¬ IdentDistrib (Xf 1) (Xf 0) (Measure.dirac ()) (Measure.dirac ()) := by
  intro h
  have hs : MeasurableSet {v : Fin 1 → ℝ | v 0 = 1} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have := h.measure_mem_eq hs
  simp [Xf] at this

/-! ### Robust Wald coverage in the concrete model -/

/-- The score `wᵢ = uᵢ xᵢ` of the concrete model as a function of one row. -/
def score (p : Bool × Bool) : ℝ := (2 + sgn p.1) * sgn p.2 * sgn p.1

lemma integral_score : ∫ ω, score (ω 0) ∂μ = 0 := by
  rw [integral_row]
  norm_num [score, sgn]

lemma variance_score : Var[fun ω => score (ω 0); μ] = 5 := by
  have hm : AEMeasurable (fun ω => score (ω 0)) μ :=
    ((measurable_of_countable score).comp (measurable_pi_apply 0)).aemeasurable
  rw [variance_eq_integral hm, integral_score]
  have h := integral_row (fun p => (score p - 0) ^ 2) 0
  rw [h]
  norm_num [score, sgn]

/-- OLS in the concrete model: `β̂ₙ = β + n⁻¹ ∑_{i<n} wᵢ`, so the scaled error is a normalized sum
of the i.i.d. scores. -/
lemma sqrt_mul_olsSeqEstimator_sub (β : Fin 1 → ℝ) (n : ℕ) (ω : ℕ → Bool × Bool) :
    √(n : ℝ) * ((fun _ => (1 : ℝ)) ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω -
        (fun _ => (1 : ℝ)) ⬝ᵥ β) =
      (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, score (ω k) - n * ∫ ω, score (ω 0) ∂μ) := by
  rw [integral_score, mul_zero, sub_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hG : olsSampleGram X n ω = 1 := by
    ext a b
    rw [Subsingleton.elim a b, Matrix.one_apply_eq]
    simp only [olsSampleGram, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, X,
      sgn_mul_self, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hn'
  have hols := olsSeqEstimator_eq X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω
  change _ = (olsSampleGram X n ω)⁻¹ *ᵥ _ at hols
  rw [hG, inv_one, Matrix.one_mulVec] at hols
  rw [hols]
  have hterm : ∀ x, (X x ω 0 * β 0 + U x ω) * X x ω 0 = β 0 + score (ω x) := by
    intro x
    simp only [X, U, score]
    linear_combination β 0 * sgn_mul_self (ω x).1
  simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hs0 : √(n : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination (∑ k ∈ Finset.range n, score (ω k)) * hsq

lemma memLp_score : MemLp (fun ω => score (ω 0)) 2 μ :=
  MemLp.of_bound ((measurable_of_countable score).comp (measurable_pi_apply 0)).aestronglyMeasurable
    3 (Eventually.of_forall fun ω => by
      rcases ω 0 with ⟨_ | _, _ | _⟩ <;> norm_num [score, sgn])

lemma hasLaw_id_five :
    HasLaw (id : ℝ → ℝ) (gaussianReal 0 Var[fun ω => score (ω 0); μ].toNNReal)
      (gaussianReal 0 5) := by
  have hvar : Var[fun ω => score (ω 0); μ].toNNReal = 5 := by
    rw [variance_score]; norm_num
  rw [hvar]
  exact HasLaw.id

/-- Asymptotic normality of the OLS coefficient in the concrete model, from Mathlib's CLT. -/
lemma tendstoInDistribution_olsSeqEstimator (β : Fin 1 → ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      ((fun _ => (1 : ℝ)) ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω -
        (fun _ => (1 : ℝ)) ⬝ᵥ β)) atTop id (fun _ => μ) (gaussianReal 0 5) := by
  have hclt : TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      (∑ k ∈ Finset.range n, score (ω k) - n * ∫ ω, score (ω 0) ∂μ))
      atTop id (fun _ => μ) (gaussianReal 0 5) :=
    have h1 := hasLaw_id_five
    have h2 := memLp_score
    have h3 := iIndepFun_row score
    have h4 := fun i => identDistrib_row score i
    tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun k ω => score (ω k)) (P := μ)
      (P' := gaussianReal 0 5) (Y := id) h1 h2 h3 h4
  have heq : (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      (∑ k ∈ Finset.range n, score (ω k) - n * ∫ ω, score (ω 0) ∂μ)) =
      fun (n : ℕ) ω => √(n : ℝ) *
        ((fun _ => (1 : ℝ)) ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω -
          (fun _ => (1 : ℝ)) ⬝ᵥ β) := by
    funext n ω
    exact (sqrt_mul_olsSeqEstimator_sub β n ω).symm
  rw [heq] at hclt
  exact hclt

lemma measurable_X (i : ℕ) : Measurable (X i) :=
  (measurable_of_countable fun p : Bool × Bool => (fun _ => sgn p.1 : Fin 1 → ℝ)).comp
    (measurable_pi_apply i)

lemma measurable_U (i : ℕ) : Measurable (U i) :=
  (measurable_of_countable fun p : Bool × Bool => (2 + sgn p.1) * sgn p.2).comp
    (measurable_pi_apply i)

lemma robustVariance_eq :
    ((5 : NNReal) : ℝ) = (fun _ => (1 : ℝ)) ⬝ᵥ (hc0PopSandwich (X 0) (U 0) μ *ᵥ fun _ => 1) := by
  rw [hc0PopSandwich_eq]
  simp [dotProduct, Matrix.mulVec]

/-- **Asymptotic coverage of the robust Wald interval in the concrete model.** The interval
`β̂ₙ ± z √(V̂ₙ) / √n` with the HC0 sandwich `V̂ₙ` covers the true `β` with probability tending to
the standard-normal mass of `[-z, z]`. Asymptotic normality comes from Mathlib's CLT applied to
the i.i.d. scores `wᵢ = uᵢ xᵢ` (variance `5 = Q⁻¹ Ω Q⁻ᵀ`); consistency of the robust standard
error comes from `hc0OLSSandwich_tendsto_ae`. -/
theorem tendsto_coverage_hc0Wald_concrete (β : Fin 1 → ℝ) (z : ℝ) :
    Tendsto (fun n : ℕ => μ.real {ω | (fun _ => (1 : ℝ)) ⬝ᵥ β ∈
        waldInterval ((fun _ => (1 : ℝ)) ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω)
          (√((fun _ => (1 : ℝ)) ⬝ᵥ (hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω *ᵥ
            fun _ => (1 : ℝ))) / √(n : ℝ)) z})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) :=
  tendsto_coverage_hc0Wald β measurable_X measurable_U hJoint hIdent hMom4 hMom2 hmeanScore hQ
    (fun _ => 1) (by norm_num) robustVariance_eq HasLaw.id
    (tendstoInDistribution_olsSeqEstimator β) z

end MathlibExtTest.LinearModelHeteroskedasticityRobust
