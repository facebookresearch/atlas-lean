/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRInference
public import MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-!
# Tests for the GTR inference corollary

* `empiricalFreq` on a concrete alternating sample, and its boundary value `0` at `n = 0`.
* A model identified only up to a symmetry: `law θ = (θ², 1 - θ²)` on `Θ = [-1, 1]`, where
  `θ` and `-θ` have the same law. The identifiability hypothesis holds with the class
  `E = {θ₀, -θ₀}` and fails for `E = {θ₀}`, so the corollary gives consistency only up to sign.
* A fully discharged instance: the degenerate sample `X i = true` from the law of `θ₀ = 1`
  satisfies every sampling hypothesis, so the corollary applies with no assumption left open.
* The JC69 branch-length model (the equal-rates GTR model,
  `SubstitutionModels.ctmcTransition_gtrRate_jukesCantor`) on two taxa with `t ∈ [0, 1]`:
  the site-pattern law is continuous and identifies `t`, so the minimum-distance estimator of
  the branch length is consistent in probability.
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology

namespace MathlibExtTest.Biology.Phylogenetics.GTRInference

open MathlibExt.Biology.Phylogenetics.GTRInference MathlibExt.Biology.Phylogenetics.JukesCantor

/-! ## Empirical frequencies -/

/-- An alternating sample `true, false, true, …` (constant in `ω`). -/
def altSample : ℕ → Unit → Bool := fun i _ => decide (i % 2 = 0)

example : empiricalFreq altSample 2 () true = 1 / 2 := by
  simp [empiricalFreq, altSample]
  decide

example : empiricalFreq altSample 3 () false = 1 / 3 := by
  simp [empiricalFreq, altSample]
  decide

/-- Boundary case: no columns give the zero frequency vector. -/
example (X : ℕ → Unit → Bool) : empiricalFreq X 0 () = 0 := by
  ext a
  simp [empiricalFreq]

/-! ## A model identified only up to sign -/

/-- The parameter space `[-1, 1]`. -/
abbrev Θs := Set.Icc (-1 : ℝ) 1

instance : Nonempty Θs := ⟨⟨0, by norm_num, by norm_num⟩⟩

/-- The law `(θ², 1 - θ²)` on the two patterns `true, false`: invariant under `θ ↦ -θ`. -/
noncomputable def sqLaw (θ : Θs) : Bool → ℝ := fun b => if b then (θ : ℝ) ^ 2 else 1 - (θ : ℝ) ^ 2

theorem continuous_sqLaw : Continuous sqLaw := by
  refine continuous_pi fun b => ?_
  cases b <;> simp only [sqLaw, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- Identifiability up to sign: equal laws force `θ = θ₀` or `θ = -θ₀`. -/
theorem sqLaw_identifiable (θ₀ : Θs) :
    ∀ θ, sqLaw θ = sqLaw θ₀ → θ ∈ {θ : Θs | (θ : ℝ) = θ₀ ∨ (θ : ℝ) = -θ₀} := by
  intro θ h
  have := congrFun h true
  simp only [sqLaw, ite_true] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.1 this

/-- Non-vacuity of the symmetry: `1/2` and `-1/2` have the same law, so the model is not
identified pointwise and `E = {θ₀}` fails the identifiability hypothesis. -/
example : ¬ ∀ θ : Θs, sqLaw θ = sqLaw ⟨1 / 2, by norm_num, by norm_num⟩ →
    θ = ⟨1 / 2, by norm_num, by norm_num⟩ := by
  intro h
  have := h ⟨-1 / 2, by norm_num, by norm_num⟩ (by ext b; cases b <;> simp [sqLaw] <;> norm_num)
  have := congrArg Subtype.val this
  norm_num at this

/-- The corollary in the sign-symmetric model: the minimum-distance estimator approaches
`{θ₀, -θ₀}` in probability, for any sample satisfying the sampling law. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (θ₀ : Θs)
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = sqLaw θ₀ a) :
    TendstoInMeasure P (fun n ω => infDist (minDistEstimator continuous_sqLaw (empiricalFreq X) n ω)
      {θ : Θs | (θ : ℝ) = θ₀ ∨ (θ : ℝ) = -θ₀}) atTop fun _ => 0 :=
  tendstoInMeasure_infDist_minDistEstimator continuous_sqLaw (sqLaw_identifiable θ₀) hX hindep
    hident hsample

/-! ## A fully discharged instance -/

/-- The true parameter `θ₀ = 1`, whose law is the point mass at `true`. -/
def θone : Θs := ⟨1, by norm_num, by norm_num⟩

/-- Every sampling hypothesis holds for the constant sample `X i = true` under any probability
measure, so the corollary holds with no hypothesis left open. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    TendstoInMeasure P
      (fun n ω => infDist (minDistEstimator continuous_sqLaw
        (empiricalFreq fun (_ : ℕ) (_ : Ω) => true) n ω)
        {θ : Θs | (θ : ℝ) = θone ∨ (θ : ℝ) = -θone}) atTop fun _ => 0 := by
  refine tendstoInMeasure_infDist_minDistEstimator continuous_sqLaw (sqLaw_identifiable θone)
    (fun _ => measurable_const) (fun _ _ _ => indepFun_const_left true _)
    (fun _ => IdentDistrib.refl measurable_const.aemeasurable) fun a => ?_
  cases a <;> simp [sqLaw, θone]

/-! ## The JC69 (equal-rates GTR) branch-length model -/

/-- Branch lengths `t ∈ [0, 1]`. -/
abbrev Θjc := Set.Icc (0 : ℝ) 1

instance : Nonempty Θjc := ⟨⟨0, le_rfl, zero_le_one⟩⟩

/-- The two-taxon JC69 site-pattern law with rate `μ = 1`: `P (X = (i, j)) = jcProb 1 t i j / 4`
(uniform root, one branch of length `t`). -/
noncomputable def jcLaw (t : Θjc) : Fin 4 × Fin 4 → ℝ := fun p => jcProb 1 t p.1 p.2 / 4

theorem continuous_jcLaw : Continuous jcLaw := by
  refine continuous_pi fun p => ?_
  simp only [jcLaw, jcProb]
  split_ifs <;> fun_prop

/-- The JC69 law identifies the branch length (from the probability of a constant site). -/
theorem jcLaw_injective (t₀ : Θjc) : ∀ t, jcLaw t = jcLaw t₀ → t = t₀ := by
  intro t h
  have h0 := congrFun h (0, 0)
  simp only [jcLaw, jcProb, ite_true] at h0
  have he : Real.exp (-4 * 1 * (t : ℝ) / 3) = Real.exp (-4 * 1 * (t₀ : ℝ) / 3) := by linarith
  have := Real.exp_injective he
  exact Subtype.ext (by linarith)

/-- **Consistency of the JC69 minimum-distance branch-length estimator** from the sampling law. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (t₀ : Θjc)
    {X : ℕ → Ω → Fin 4 × Fin 4} (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsample : ∀ a, P.real (X 0 ⁻¹' {a}) = jcLaw t₀ a) :
    TendstoInMeasure P (minDistEstimator continuous_jcLaw (empiricalFreq X)) atTop
      fun _ => t₀ :=
  tendstoInMeasure_minDist_of_injective continuous_jcLaw (jcLaw_injective t₀) hX hindep hident
    hsample (isMinDistEstimator_minDistEstimator continuous_jcLaw _)

end MathlibExtTest.Biology.Phylogenetics.GTRInference
