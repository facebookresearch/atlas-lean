/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRMLE
public import MathlibExt.Biology.Phylogenetics.SubstitutionModels
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for GTR maximum-likelihood consistency

* `logLik` at the empirical frequencies of a concrete sample, computed from the definitions,
  and the boundary `n = 0`, where the criterion vanishes and every parameter is an MLE.
* A positive model identified only up to sign: `law θ = ((1 + θ²) / 4, (3 - θ²) / 4)` on
  `Θ = [-1, 1]`. All model hypotheses (continuity, positivity, normalization, identifiability up
  to `E = {θ₀, -θ₀}`) are proved, `E = {θ₀}` is shown to fail, and the strict information
  inequality is checked numerically from the definitions.
* A **fully discharged** instance: i.i.d. fair coin columns on `ℕ → Bool` under the product
  measure satisfy every sampling hypothesis for `θ₀ = 1`, so the MLE converges almost surely to
  `{1, -1}` with no hypothesis left open. (A constant sample cannot be used here: positivity
  rules out point-mass laws.)
* The JC69 (equal-rates GTR) branch-length model on two taxa. Boundary: at branch length `0`
  the law gives probability `0` to every pattern with different bases, so positivity fails and
  the parameter box must stay away from `0`. On `t ∈ [1, 2]` all model hypotheses hold
  (continuity, positivity, normalization, injectivity) and the MLE of the branch length is
  consistent for any sample satisfying the sampling hypotheses, which are left open there; the
  fair-coin test is the only fully discharged instance.
* Wald's argmax theorem on an abstract criterion: the maximizers `1/(n+1)` of
  `-(θ - 1/(n+1))²` on `[-1, 1]` converge to the identified maximum `{0}`.
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExtTest.Biology.Phylogenetics.GTRMLE

open MathlibExt.Biology.Phylogenetics.GTRMLE MathlibExt.Biology.Phylogenetics.GTRInference
  MathlibExt.Biology.Phylogenetics.JukesCantor MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-! ## The criterion at the empirical frequencies -/

/-- An alternating sample `true, false, true, …` (constant in `ω`). -/
def altSample : ℕ → Unit → Bool := fun i _ => decide (i % 2 = 0)

/-- After two columns (`true`, `false`) the criterion is the average of the two
log-probabilities, computed from the definitions of `logLik` and `empiricalFreq`. -/
example {Θ : Type*} (law : Θ → Bool → ℝ) (θ : Θ) :
    logLik law (empiricalFreq altSample 2 ()) θ =
      (Real.log (law θ true) + Real.log (law θ false)) / 2 := by
  have ht : #{i ∈ range 2 | altSample i () = true} = 1 := by decide
  have hf : #{i ∈ range 2 | altSample i () = false} = 1 := by decide
  simp only [logLik, empiricalFreq, Fintype.sum_bool, ht, hf]
  ring

/-- The same value through `logLik_empiricalFreq` (average log-likelihood form). -/
example {Θ : Type*} (law : Θ → Bool → ℝ) (θ : Θ) :
    logLik law (empiricalFreq altSample 2 ()) θ =
      (Real.log (law θ true) + Real.log (law θ false)) / 2 := by
  rw [logLik_empiricalFreq]
  simp [sum_range_succ, altSample]
  ring

/-- Boundary `n = 0`: the criterion vanishes. -/
example {Θ : Type*} (law : Θ → Bool → ℝ) (X : ℕ → Unit → Bool) (θ : Θ) :
    logLik law (empiricalFreq X 0 ()) θ = 0 := by
  simp [logLik, empiricalFreq]

/-- Boundary `n = 0`: every estimator maximizes the criterion at `n = 0`. -/
example {Θ : Type*} (law : Θ → Bool → ℝ) (X : ℕ → Unit → Bool) (est : ℕ → Unit → Θ) (θ : Θ) :
    logLik law (empiricalFreq X 0 ()) θ ≤ logLik law (empiricalFreq X 0 ()) (est 0 ()) := by
  simp [logLik, empiricalFreq]

/-! ## A positive model identified only up to sign -/

/-- The parameter space `[-1, 1]`. -/
abbrev Θs := Set.Icc (-1 : ℝ) 1

instance : Nonempty Θs := ⟨⟨0, by norm_num, by norm_num⟩⟩

/-- The law `((1 + θ²) / 4, (3 - θ²) / 4)` on the patterns `true, false`: positive, normalized,
and invariant under `θ ↦ -θ`. -/
noncomputable def sqLaw (θ : Θs) : Bool → ℝ := fun b =>
  if b then (1 + (θ : ℝ) ^ 2) / 4 else (3 - (θ : ℝ) ^ 2) / 4

theorem continuous_sqLaw : Continuous sqLaw := by
  refine continuous_pi fun b => ?_
  cases b <;> simp only [sqLaw, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem sqLaw_pos (θ : Θs) (b : Bool) : 0 < sqLaw θ b := by
  have h1 : (θ : ℝ) ^ 2 ≤ 1 := by
    have := θ.2; rw [sq_le_one_iff_abs_le_one, abs_le]; exact this
  cases b <;> simp only [sqLaw, Bool.false_eq_true, ite_false, ite_true] <;> nlinarith

theorem sqLaw_sum (θ : Θs) : ∑ b, sqLaw θ b = 1 := by
  simp only [Fintype.sum_bool, sqLaw, ite_true, Bool.false_eq_true, ite_false]
  ring

/-- Identifiability up to sign. -/
theorem sqLaw_identifiable (θ₀ : Θs) :
    ∀ θ, sqLaw θ = sqLaw θ₀ → θ ∈ {θ : Θs | (θ : ℝ) = θ₀ ∨ (θ : ℝ) = -θ₀} := by
  intro θ h
  have := congrFun h true
  simp only [sqLaw, ite_true] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.1 (by linarith)

/-- `E = {θ₀}` fails: `1` and `-1` have the same law. -/
example : ¬ ∀ θ : Θs, sqLaw θ = sqLaw ⟨1, by norm_num, by norm_num⟩ →
    θ = ⟨1, by norm_num, by norm_num⟩ := by
  intro h
  have := h ⟨-1, by norm_num, by norm_num⟩ (by ext b; cases b <;> simp [sqLaw])
  have := congrArg Subtype.val this
  norm_num at this

/-- The true parameter `θ₀ = 1`, with the fair-coin law. -/
def θone : Θs := ⟨1, by norm_num, by norm_num⟩

theorem sqLaw_θone (b : Bool) : sqLaw θone b = 1 / 2 := by
  cases b <;> simp [sqLaw, θone] <;> norm_num

/-- `θ = 0`. -/
def θzero : Θs := ⟨0, by norm_num, by norm_num⟩

/-- The strict information inequality at `θ = 0` against `θ₀ = 1`, computed from the
definitions: `(log (1/4) + log (3/4)) / 2 < log (1/2)`, since `3/16 < 1/4`. -/
example : logLik sqLaw (sqLaw θone) θzero < logLik sqLaw (sqLaw θone) θone := by
  have h1 : Real.log (1 / 4) + Real.log (3 / 4) < Real.log (1 / 2) + Real.log (1 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hz : sqLaw θzero true = 1 / 4 ∧ sqLaw θzero false = 3 / 4 := by
    simp only [sqLaw, θzero, ite_true, Bool.false_eq_true, ite_false]; norm_num
  simp only [logLik, Fintype.sum_bool, sqLaw_θone, hz.1, hz.2]
  linarith

/-- The same inequality through `logLik_lt_logLik_self`. -/
example : logLik sqLaw (sqLaw θone) θzero < logLik sqLaw (sqLaw θone) θone :=
  logLik_lt_logLik_self sqLaw_pos sqLaw_sum fun h => by
    have := congrFun h true
    simp [sqLaw, θzero, θone] at this
    norm_num at this

/-- The sign-symmetric model: MLE consistency in probability up to sign, for any sample
satisfying the sampling law. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (θ₀ : Θs)
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = sqLaw θ₀ a) :
    TendstoInMeasure P
      (fun n ω => infDist (mle continuous_sqLaw sqLaw_pos (empiricalFreq X) n ω)
        {θ : Θs | (θ : ℝ) = θ₀ ∨ (θ : ℝ) = -θ₀}) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mleEstimator continuous_sqLaw sqLaw_pos sqLaw_sum
    (sqLaw_identifiable θ₀) hX hindep hident hsample

/-! ## A fully discharged instance: i.i.d. fair coins -/

/-- The fair-coin law on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac false + (1 / 2 : ENNReal) • Measure.dirac true

instance : IsProbabilityMeasure coin := ⟨by
  simp only [coin, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]; norm_num; exact ENNReal.div_self (by norm_num) (by norm_num)⟩

/-- I.i.d. fair coins. -/
noncomputable abbrev coinSeq : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ => coin

/-- The `i`-th column. -/
def col (i : ℕ) (ω : ℕ → Bool) : Bool := ω i

theorem measurable_col (i : ℕ) : Measurable (col i) := measurable_pi_apply i

theorem indep_col : Pairwise ((· ⟂ᵢ[coinSeq] ·) on col) := fun _ _ hij =>
  (iIndepFun_infinitePi (P := fun _ : ℕ => coin) (X := fun _ => id)
    (fun _ => measurable_id)).indepFun hij

theorem ident_col (i : ℕ) : IdentDistrib (col i) (col 0) coinSeq coinSeq :=
  ⟨(measurable_col i).aemeasurable, (measurable_col 0).aemeasurable, by
    change Measure.map (Function.eval i) coinSeq = Measure.map (Function.eval 0) coinSeq
    rw [(measurePreserving_eval_infinitePi (μ := fun _ : ℕ => coin) i).map_eq,
      (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => coin) 0).map_eq]⟩

theorem sample_col (a : Bool) : coinSeq.real (col 0 ⁻¹' {a}) = sqLaw θone a := by
  have hmp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => coin) 0
  rw [Measure.real, show col 0 ⁻¹' {a} = (fun ω : ℕ → Bool => ω 0) ⁻¹' {a} from rfl,
    hmp.measure_preimage (measurableSet_singleton a).nullMeasurableSet, sqLaw_θone]
  cases a <;> simp [coin]

/-- **Fully discharged MLE consistency**: for i.i.d. fair-coin columns, the MLE in the
sign-symmetric model converges almost surely to `{1, -1}`; every hypothesis is proved. -/
example : ∀ᵐ ω ∂coinSeq, Tendsto
    (fun n => infDist (mle continuous_sqLaw sqLaw_pos (empiricalFreq col) n ω)
      {θ : Θs | (θ : ℝ) = θone ∨ (θ : ℝ) = -θone}) atTop (𝓝 0) :=
  ae_tendsto_infDist_mle continuous_sqLaw sqLaw_pos sqLaw_sum (sqLaw_identifiable θone)
    measurable_col indep_col ident_col sample_col (isMLE_mle continuous_sqLaw sqLaw_pos _)

/-- The same instance, in probability. -/
example : TendstoInMeasure coinSeq
    (fun n ω => infDist (mle continuous_sqLaw sqLaw_pos (empiricalFreq col) n ω)
      {θ : Θs | (θ : ℝ) = θone ∨ (θ : ℝ) = -θone}) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_mleEstimator continuous_sqLaw sqLaw_pos sqLaw_sum
    (sqLaw_identifiable θone) measurable_col indep_col ident_col sample_col

/-! ## The JC69 (equal-rates GTR) branch-length model -/

/-- The two-taxon site-pattern law of the equal-rates GTR model (frequencies `1/4`,
exchangeabilities `4/3`, i.e. JC69 with rate `1`), at any real branch length `t`:
`P (X = (i, j)) = P t i j / 4` with `P t = exp (t • gtrRate π s)`. -/
noncomputable def jcLawR (t : ℝ) : Fin 4 × Fin 4 → ℝ := fun p =>
  ctmcTransition (gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * 1 / 3)) t p.1 p.2 / 4

theorem jcLawR_eq (t : ℝ) (p : Fin 4 × Fin 4) : jcLawR t p = jcProb 1 t p.1 p.2 / 4 := by
  rw [jcLawR, ctmcTransition_gtrRate_jukesCantor]

/-- Boundary: at branch length `0` a pattern with different bases has probability `0`, so the
positivity hypothesis fails and the parameter box must exclude `0`. -/
example : jcLawR 0 (0, 1) = 0 := by
  rw [jcLawR_eq]; simp [jcProb]

/-- Branch lengths `t ∈ [1, 2]`. -/
abbrev Θjc := Set.Icc (1 : ℝ) 2

instance : Nonempty Θjc := ⟨⟨1, le_rfl, one_le_two⟩⟩

/-- The JC69 law on `Θjc`. -/
noncomputable def jcLaw (t : Θjc) : Fin 4 × Fin 4 → ℝ := jcLawR t

theorem continuous_jcLaw : Continuous jcLaw := by
  refine continuous_pi fun p => ?_
  simp only [jcLaw, jcLawR_eq, jcProb]
  split_ifs <;> fun_prop

theorem jcLaw_pos (t : Θjc) (p : Fin 4 × Fin 4) : 0 < jcLaw t p := by
  have ht : (0 : ℝ) < t := lt_of_lt_of_le one_pos t.2.1
  have he : Real.exp (-4 * 1 * (t : ℝ) / 3) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have he0 := Real.exp_pos (-4 * 1 * (t : ℝ) / 3)
  simp only [jcLaw, jcLawR_eq, jcProb]
  split_ifs <;> linarith

theorem jcLaw_sum (t : Θjc) : ∑ p, jcLaw t p = 1 := by
  simp only [jcLaw, jcLawR_eq, Fintype.sum_prod_type, Fin.sum_univ_four, jcProb]
  norm_num
  ring

/-- The JC69 law identifies the branch length (from the probability of a constant site). -/
theorem jcLaw_injective (t₀ : Θjc) : ∀ t, jcLaw t = jcLaw t₀ → t = t₀ := by
  intro t h
  have h0 := congrFun h (0, 0)
  simp only [jcLaw, jcLawR_eq, jcProb, ite_true] at h0
  have he : Real.exp (-4 * 1 * (t : ℝ) / 3) = Real.exp (-4 * 1 * (t₀ : ℝ) / 3) := by linarith
  have := Real.exp_injective he
  exact Subtype.ext (by linarith)

/-- **Consistency of the JC69 maximum-likelihood branch-length estimator**, almost surely and
in probability. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (t₀ : Θjc)
    {X : ℕ → Ω → Fin 4 × Fin 4} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = jcLaw t₀ a) :
    (∀ᵐ ω ∂P, Tendsto (fun n => mle continuous_jcLaw jcLaw_pos (empiricalFreq X) n ω) atTop
      (𝓝 t₀)) ∧
    TendstoInMeasure P (mle continuous_jcLaw jcLaw_pos (empiricalFreq X)) atTop fun _ => t₀ :=
  ⟨ae_tendsto_mle_of_injective continuous_jcLaw jcLaw_pos jcLaw_sum (jcLaw_injective t₀) hX
      hindep hident hsample (isMLE_mle continuous_jcLaw jcLaw_pos _),
    tendstoInMeasure_mle_of_injective continuous_jcLaw jcLaw_pos jcLaw_sum (jcLaw_injective t₀) hX
      hindep hident hsample (isMLE_mle continuous_jcLaw jcLaw_pos _)⟩

/-! ## Wald's argmax theorem on an abstract criterion -/

/-- The point `1/(n+1) ∈ [-1, 1]`. -/
noncomputable def θn (n : ℕ) : Θs :=
  ⟨1 / (n + 1), by
    have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨le_trans (by norm_num) (div_pos one_pos h0).le, ?_⟩
    rw [div_le_one h0]; linarith [n.cast_nonneg (α := ℝ)]⟩

/-- Criteria `-(θ - 1/(n+1))²` on `[-1, 1]` converge uniformly to `-θ²`, whose maximum `0` is
identified; the maximizers `1/(n+1)` approach `{0}` (Wald's argmax theorem). -/
example : Tendsto (fun n => infDist (θn n) {θzero}) atTop (𝓝 0) := by
  refine tendsto_infDist_of_tendstoUniformly (M := fun θ : Θs => -(θ : ℝ) ^ 2) (by fun_prop)
    (θ₀ := θzero) (fun θ hθ => ?_) (Mn := fun n θ => -((θ : ℝ) - 1 / (n + 1)) ^ 2) ?_
    fun n θ => ?_
  · simp only [θzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero] at hθ
    exact Set.mem_singleton_iff.2
      (Subtype.ext (by simp only [θzero]; nlinarith [sq_nonneg (θ : ℝ)]))
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 5 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn θ
    have hθ := θ.2
    have h0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := (θn n).2.2
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [hθ.1, hθ.2]
  · simp only [θn, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero]
    exact neg_nonpos.2 (sq_nonneg _)

end MathlibExtTest.Biology.Phylogenetics.GTRMLE
