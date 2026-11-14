/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldEnvelope

/-!
# Tests for Wald consistency under Wald's original conditions

* **Laplace location model on `ℝ`.** `ℓ θ x = -|θ - x|` with parameter set `S = ℝ`, which is not
  compact, so `MLEConsistency` does not apply. Computed from the definitions: for every sample
  with `X 0` integrable, local envelopes `-|θ - x| + 1 / (n + 1)` at every `θ` and the envelope at
  infinity `|x| - n` around `0`; for `X 0 = 0`, a one-set Wald cover at every radius (envelope
  `min (|x| - ε) 0`).
* **Joint non-vacuity.** For a constant sample `X i = 0` on a one-point probability space, every
  hypothesis of Wald's theorem `ae_tendsto_of_isMLEOn_of_hasTailEnvelope` holds on `S = ℝ`:
  identifiability of the population criterion `-|θ|` at `0` and the MLE `0` are computed from the
  definitions. The instance is degenerate (independence and identical distribution are trivial
  for a constant sample); a non-degenerate i.i.d. instance on a product space is not constructed.
* **Boundary: the strict inequality.** For the flat log-likelihood `ℓ = 0` on `ℝ`, a cover of
  `ℝ \ ball 0 1` by one set with envelope `0` meets every requirement of a Wald cover except the
  strict inequality (its mean equals the population criterion at `0`), no Wald cover at radius `1`
  exists, no envelope at infinity exists, and the MLE `est n = n` does not converge to `0`.
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology Set

namespace MathlibExtTest.Probability.Statistics.WaldEnvelope

open MathlibExt.Probability.Statistics.MLEConsistency
  MathlibExt.Probability.Statistics.WaldEnvelope

/-! ## The Laplace location model on `ℝ` -/

/-- The Laplace location log-likelihood of one observation, up to an additive constant:
`-|θ - x|`. -/
def absLL (θ x : ℝ) : ℝ := -|θ - x|

/-- The parameter set `ℝ` of the Laplace model is not compact. -/
example : ¬ IsCompact (univ : Set ℝ) := noncompact_univ ℝ

/-- The single envelope of the Wald cover of the Laplace model at radius `ε`. -/
def absEnv (ε x : ℝ) : ℝ := min (|x| - ε) 0

theorem measurable_absEnv (ε : ℝ) : Measurable (absEnv ε) := by
  unfold absEnv; fun_prop

/-- `absEnv ε` is an upper envelope of `absLL θ` for `|θ| ≥ ε`. -/
theorem absLL_le_absEnv {ε θ : ℝ} (hθ : θ ∈ (univ : Set ℝ) \ ball 0 ε) (x : ℝ) :
    absLL θ x ≤ absEnv ε x := by
  have h1 : ε ≤ |θ| := by
    have := hθ.2
    rw [mem_ball, Real.dist_eq, sub_zero, not_lt] at this
    exact this
  have h2 := abs_sub_abs_le_abs_sub θ x
  unfold absLL absEnv
  exact le_min (by linarith) (by linarith [abs_nonneg (θ - x)])

/-- **A Wald cover of `ℝ` for the Laplace model** by one set, at every radius `ε`, when `X 0 = 0`:
the mean of the envelope is `-ε < 0 = E ℓ 0 (X 0)`. (For a spread-out law of `X 0` one set does
not suffice at small `ε`; `exists_isWaldCover` builds the finer cover from the local envelopes
and the envelope at infinity below, which hold for every integrable `X 0`.) -/
theorem absLL_isWaldCover {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hX : ∀ ω, X 0 ω = 0) {ε : ℝ} (hε : 0 < ε) :
    IsWaldCover P absLL X univ 0 ε {(univ \ ball 0 ε, absEnv ε)} := by
  have hint : Integrable (fun ω => absEnv ε (X 0 ω)) P := by
    simp only [hX]; exact integrable_const _
  refine ⟨finite_singleton _, fun θ hθ => by simpa using hθ, ?_⟩
  rintro p hp
  rw [mem_singleton_iff.1 hp]
  refine ⟨measurable_absEnv ε, hint, fun θ hθ x => absLL_le_absEnv hθ x, ?_⟩
  simp only [popCrit, absLL, absEnv, hX, integral_const, sub_zero, abs_zero, neg_zero,
    probReal_univ, one_smul, zero_sub]
  rw [min_eq_left (by linarith)]
  linarith

/-- **Local envelopes of the Laplace model** at every `θ`: `-|θ - x| + 1 / (n + 1)`. -/
theorem absLL_hasLocalEnvelope {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} (hX : Integrable (X 0) P) (S : Set ℝ) (θ : ℝ) :
    HasLocalEnvelope P S absLL X θ := by
  refine ⟨fun n x => -|θ - x| + 1 / ((n : ℝ) + 1), fun n => by fun_prop, ?_, ?_, ?_, ?_⟩
  · have h : Integrable (fun ω => |θ - X 0 ω|) P :=
      ((integrable_const θ).sub hX).abs
    simpa using h.neg.add (integrable_const 1)
  · intro n θ' _ hd x
    rw [Real.dist_eq] at hd
    have := abs_sub_le θ θ' x
    rw [abs_sub_comm θ θ'] at this
    unfold absLL
    linarith
  · intro x m n hmn
    have h : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have := one_div_le_one_div_of_le (by positivity) h
    simp only
    linarith
  · intro x
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (-|θ - x|)
    simpa [absLL] using this

/-- **The envelope at infinity of the Laplace model** around `0`: `|x| - n`. -/
theorem absLL_hasTailEnvelope {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} (hX : Integrable (X 0) P) (S : Set ℝ) :
    HasTailEnvelope P S absLL X 0 := by
  refine ⟨fun n x => |x| - n, fun n => by fun_prop, ?_, ?_, ?_, ?_⟩
  · simpa using hX.abs
  · intro n θ _ hd x
    rw [Real.dist_eq, sub_zero] at hd
    have := abs_sub_abs_le_abs_sub θ x
    unfold absLL
    linarith
  · intro x m n hmn
    have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
    simp only
    linarith
  · intro x
    rw [tendsto_atBot]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge (|x| - b)
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-! ## Joint non-vacuity on a one-point probability space -/

/-- The one-point probability space. -/
noncomputable def P₁ : Measure Unit := Measure.dirac ()

instance : IsProbabilityMeasure P₁ := by unfold P₁; infer_instance

/-- The constant sample `X i = 0`. -/
def X₀ : ℕ → Unit → ℝ := fun _ _ => 0

/-- The population criterion of the Laplace model for the constant sample is `-|θ|`. -/
theorem popCrit_absLL_X₀ (θ : ℝ) : popCrit P₁ absLL X₀ θ = -|θ| := by
  simp [popCrit, absLL, X₀]

/-- The Laplace model for the constant sample is identified at `0` on `ℝ`. -/
theorem absLL_isIdentifiedOn : IsIdentifiedOn univ (popCrit P₁ absLL X₀) 0 := by
  refine ⟨mem_univ _, fun θ _ hθ => ?_⟩
  rw [popCrit_absLL_X₀, popCrit_absLL_X₀, abs_zero, neg_zero, neg_lt_zero]
  exact abs_pos.2 hθ

/-- The constant estimator `0` is an MLE on `ℝ` for the constant sample. -/
theorem absLL_isMLEOn : IsMLEOn univ absLL X₀ fun _ _ => (0 : ℝ) := by
  refine fun n ω => ⟨mem_univ _, fun θ _ => ?_⟩
  simp only [avgLogLik, absLL, X₀, sub_zero, abs_zero, neg_zero, Finset.sum_const_zero,
    mul_zero, Finset.sum_neg_distrib, mul_neg]
  exact neg_nonpos.2 (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun _ _ => abs_nonneg θ))

theorem integrable_X₀ : Integrable (X₀ 0) P₁ := integrable_const (0 : ℝ)

/-- **Every hypothesis of Wald's theorem holds jointly** for the Laplace model on `ℝ` with the
constant sample, so the theorem applies with no hypothesis left open. -/
example : ∀ᵐ ω ∂P₁, Tendsto (fun n : ℕ => (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) n ω) atTop (𝓝 0) :=
  ae_tendsto_of_isMLEOn_of_hasTailEnvelope isClosed_univ absLL_isIdentifiedOn
    (by unfold absLL; fun_prop) (fun θ _ => by simp only [absLL, X₀]; exact integrable_const _)
    (fun θ _ _ => absLL_hasLocalEnvelope integrable_X₀ univ θ)
    (absLL_hasTailEnvelope integrable_X₀ univ)
    (fun i j _ => indepFun_const_left 0 _) (fun _ => IdentDistrib.refl aemeasurable_const)
    absLL_isMLEOn

/-- The Wald cover hypothesis holds for the constant sample, at every radius. -/
example {ε : ℝ} (hε : 0 < ε) : ∃ C, IsWaldCover P₁ absLL X₀ univ 0 ε C :=
  ⟨_, absLL_isWaldCover (fun _ => rfl) hε⟩

/-! ## Boundary: the strict inequality of a Wald cover -/

/-- The flat log-likelihood `ℓ = 0`. -/
def flatLL (_ _ : ℝ) : ℝ := 0

/-- For the flat log-likelihood, one set with envelope `0` meets every requirement of a Wald cover
of `ℝ \ ball 0 1` except the strict inequality: its mean equals the population criterion at
`0`. -/
theorem flatLL_cover_eq :
    ({(univ \ ball (0 : ℝ) 1, fun _ => (0 : ℝ))} : Set (Set ℝ × (ℝ → ℝ))).Finite ∧
      univ \ ball (0 : ℝ) 1 ⊆
        ⋃ p ∈ ({(univ \ ball (0 : ℝ) 1, fun _ => (0 : ℝ))} : Set (Set ℝ × (ℝ → ℝ))), p.1 ∧
      (∀ θ ∈ univ \ ball (0 : ℝ) 1, ∀ x, flatLL θ x ≤ 0) ∧
      ∫ _, (0 : ℝ) ∂P₁ = popCrit P₁ flatLL X₀ 0 :=
  ⟨finite_singleton _, fun θ hθ => by simpa using hθ, fun _ _ _ => le_rfl,
    by simp [popCrit, flatLL]⟩

/-- For the flat log-likelihood, **no Wald cover** of `ℝ` at radius `1` exists: every envelope of
`ℓ 2 = 0` has nonnegative mean, equal to or above the population criterion at `0`. -/
theorem flatLL_not_isWaldCover : ¬ ∃ C, IsWaldCover P₁ flatLL X₀ univ 0 1 C := by
  rintro ⟨C, -, hcov, hprop⟩
  have h2 : (2 : ℝ) ∈ univ \ ball (0 : ℝ) 1 := by
    refine ⟨mem_univ _, ?_⟩
    rw [mem_ball, Real.dist_eq]
    norm_num
  obtain ⟨p, hpC, hp2⟩ := mem_iUnion₂.1 (hcov h2)
  obtain ⟨-, -, henv, hlt⟩ := hprop p hpC
  have hnn : 0 ≤ ∫ ω, p.2 (X₀ 0 ω) ∂P₁ :=
    integral_nonneg fun ω => henv 2 hp2 (X₀ 0 ω)
  have h0 : popCrit P₁ flatLL X₀ 0 = 0 := by simp [popCrit, flatLL]
  linarith

/-- For the flat log-likelihood, **no envelope at infinity** exists: `ℓ = 0` at points arbitrarily
far out, so no envelope tends to `-∞`. -/
theorem flatLL_not_hasTailEnvelope : ¬ HasTailEnvelope P₁ univ flatLL X₀ 0 := by
  rintro ⟨v, -, -, henv, -, hlim⟩
  obtain ⟨n, hn⟩ := ((hlim 0).eventually (eventually_le_atBot (-1))).exists
  have hd : (n : ℝ) < dist ((n : ℝ) + 1) 0 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have := henv n _ (mem_univ _) hd 0
  simp only [flatLL] at this
  linarith

/-- For the flat log-likelihood, `est n = n` is an MLE on `ℝ`. -/
theorem flatLL_isMLEOn : IsMLEOn univ flatLL X₀ fun n _ => (n : ℝ) :=
  fun n ω => ⟨mem_univ _, fun θ _ => by simp [avgLogLik, flatLL]⟩

/-- For the flat log-likelihood, the MLE `est n = n` **does not converge** to `0`. -/
theorem flatLL_not_tendsto (ω : Unit) :
    ¬ Tendsto (fun n : ℕ => (fun n _ => (n : ℝ)) n ω) atTop (𝓝 0) := fun h =>
  not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop 0 h

end MathlibExtTest.Probability.Statistics.WaldEnvelope
