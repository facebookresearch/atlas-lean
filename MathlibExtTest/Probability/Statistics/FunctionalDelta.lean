/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FunctionalDelta

/-!
# Tests for the functional delta theorem and the grid product integral

* Concrete values of `prodIntegral`, `duhamelDeriv`, `gridIncrements`, and the boundary case
  `x = 0`, where the Duhamel derivative is the cumulative sum.
* A non-vacuous application of `functional_delta_of_continuous` to the product integral on
  `Fin 2 → ℝ`: with `X n ω = θ + (n + 1)⁻¹ • ω` under a Dirac law, the scaled sequence converges
  to `id` and the theorem gives the limit `duhamelDeriv θ`.
* Satisfiable instances of the Kaplan–Meier theorems (grid and continuous time), showing that
  their hypotheses can be met.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.FunctionalDelta MathlibExt.Probability.Statistics.KaplanMeier
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.FunctionalDelta

/-! ### Concrete values -/

example (a b : ℝ) : prodIntegral ![a, b] 1 = (1 + a) * (1 + b) := by
  have h : Iic (1 : Fin 2) = {0, 1} := by decide
  simp [prodIntegral, h]

example (a b : ℝ) : prodIntegral ![a, b] 0 = 1 + a := by
  have h : Iic (0 : Fin 2) = {0} := by decide
  simp [prodIntegral, h]

/-- The product integral of the zero hazard is `1` (survival `1`). -/
example {k : ℕ} (j : Fin k) : prodIntegral (0 : Fin k → ℝ) j = 1 := by
  simp [prodIntegral]

/-- Boundary case: at `x = 0` the Duhamel derivative is the cumulative sum. -/
example {k : ℕ} (h : Fin k → ℝ) (j : Fin k) :
    duhamelDeriv (0 : Fin k → ℝ) h j = ∑ i ∈ Iic j, h i := by
  simp [duhamelDeriv_apply]

/-- Two-point Duhamel derivative, at the last grid point:
`D(h)₁ = h₀ (1 + x₁) + (1 + x₀) h₁`, the product rule. -/
example (x h : Fin 2 → ℝ) :
    duhamelDeriv x h 1 = h 0 * (1 + x 1) + (1 + x 0) * h 1 := by
  rw [duhamelDeriv_apply]
  have h1 : (Iic (1 : Fin 2)) = {0, 1} := by decide
  have h2 : (Iio (0 : Fin 2)) = ∅ := by decide
  have h3 : (Ioc (0 : Fin 2) 1) = {1} := by decide
  have h4 : (Iio (1 : Fin 2)) = {0} := by decide
  simp [h1, h2, h3, h4]

/-- The discrete Duhamel equation, one grid point. -/
example (x y : Fin 1 → ℝ) :
    prodIntegral y 0 - prodIntegral x 0 = (y 0 - x 0) := by
  rw [prodIntegral_sub_prodIntegral]
  have h1 : Iic (0 : Fin 1) = {0} := by decide
  have h2 : Iio (0 : Fin 1) = ∅ := by decide
  simp [h1, h2]

example : gridIncrements (![1, 3] : Fin 2 → ℝ) = ![1, 2] := by
  funext j
  fin_cases j <;> norm_num [gridIncrements_apply]

/-- The cumulative sum of the increments `![1, 2]` is `![1, 3]`, and `gridIncrements` recovers
the increments. -/
example : gridIncrements (fun j : Fin 2 ↦ ∑ i ∈ Iic j, (![1, 2] : Fin 2 → ℝ) i) = ![1, 2] :=
  gridIncrements_cumsum _

/-- The Lipschitz bound at `x = 0`, `y = c` on one grid point: `|c| ≤ e^{|c|} |c|`. -/
example (c : ℝ) :
    |prodIntegral (fun _ : Fin 1 ↦ c) 0 - prodIntegral (0 : Fin 1 → ℝ) 0| ≤
      Real.exp |c| * |c| := by
  simpa using abs_prodIntegral_sub_le 0 (fun _ : Fin 1 ↦ c) 0

/-! ### Hadamard differentiability -/

/-- A continuous linear map is its own Hadamard derivative. -/
example (L : ℝ →L[ℝ] ℝ) (θ : ℝ) : HasHadamardDerivWithinAt L L Set.univ Set.univ θ :=
  L.hasFDerivAt.hasHadamardDerivWithinAt _ _

/-- `x ↦ x²` is Hadamard differentiable at `θ` with derivative `h ↦ 2θh`. -/
example (θ : ℝ) :
    HasHadamardDerivWithinAt (fun x : ℝ ↦ x ^ 2) (fun h ↦ 2 * θ * h) Set.univ Set.univ θ := by
  have := ((hasDerivAt_pow 2 θ).hasFDerivAt).hasHadamardDerivWithinAt Set.univ Set.univ
  intro h hh
  convert this h hh using 2
  simp [mul_comm]

/-! ### Functional delta theorem: a non-vacuous instance -/

/-- The scale `r n = n + 1`. -/
noncomputable def r (n : ℕ) : ℝ := n + 1

theorem r_tendsto : Tendsto r atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-- `X θ n ω = θ + (n + 1)⁻¹ • ω` on `Ω = Fin 2 → ℝ`. -/
noncomputable def X (θ : Fin 2 → ℝ) (n : ℕ) (ω : Fin 2 → ℝ) : Fin 2 → ℝ := θ + (r n)⁻¹ • ω

/-- `(n + 1) • (X θ n - θ) = id` exactly, so it converges in distribution to `id` under any
probability law; here a Dirac mass at `v`. -/
theorem scaled_tendsto (θ v : Fin 2 → ℝ) :
    TendstoInDistribution (fun n ω ↦ r n • (X θ n ω - θ)) atTop id
      (fun _ ↦ Measure.dirac v) (Measure.dirac v) :=
  (tendstoInDistribution_const (l := atTop) aemeasurable_id).congr
    (fun n ↦ ae_of_all _ fun ω ↦ by
      have : r n ≠ 0 := by unfold r; positivity
      simp [X, smul_smul, this])
    (ae_of_all _ fun _ ↦ rfl)

/-- The functional delta theorem for the grid product integral:
`(n + 1) • (prodIntegral (X n) - prodIntegral θ) ⇒ duhamelDeriv θ`. -/
example (θ v : Fin 2 → ℝ) :
    TendstoInDistribution (fun n ω ↦ r n • (prodIntegral (X θ n ω) - prodIntegral θ)) atTop
      (fun ω ↦ duhamelDeriv θ ω) (fun _ ↦ Measure.dirac v) (Measure.dirac v) :=
  (scaled_tendsto θ v).functional_delta_of_continuous r_tendsto
    (hasHadamardDerivWithinAt_prodIntegral θ Set.univ Set.univ)
    (fun _ ↦ ae_of_all _ fun _ ↦ trivial) (ae_of_all _ fun _ ↦ trivial)
    continuous_prodIntegral (duhamelDeriv θ).continuous

/-- The extended continuous mapping theorem with `g n = g₀ = prodIntegral` (no domain
restriction) recovers the ordinary continuous mapping theorem. -/
example (θ v : Fin 2 → ℝ) :
    TendstoInDistribution (fun n ω ↦ prodIntegral (r n • (X θ n ω - θ))) atTop
      (fun ω ↦ prodIntegral (id ω)) (fun _ ↦ Measure.dirac v) (Measure.dirac v) :=
  (scaled_tendsto θ v).extended_comp (g := fun _ ↦ prodIntegral) (D := fun _ ↦ Set.univ)
    (X₀ := Set.univ)
    (fun x _ ↦ ((continuous_prodIntegral.tendsto x).comp tendsto_snd).mono_left inf_le_left)
    (fun _ ↦ ae_of_all _ fun _ ↦ trivial) (ae_of_all _ fun _ ↦ trivial)
    (fun n ↦ (continuous_prodIntegral.measurable.comp_aemeasurable
      ((scaled_tendsto θ v).forall_aemeasurable n)))
    (continuous_prodIntegral.measurable.comp_aemeasurable aemeasurable_id)

/-! ### Kaplan–Meier -/

/-- One grid time, one death and one censoring. -/
def D₁ : CensoredData 1 where
  time := fun _ ↦ 0
  strictMono_time := Subsingleton.strictMono _
  deaths := fun _ ↦ 1
  censored := fun _ ↦ 1

/-- `Ŝ(t₀) = 1 - 1/2`, computed through the product-integral representation. -/
example : D₁.kmSurvival (D₁.time 0) = 1 / 2 := by
  rw [kmSurvival_time_eq_prodIntegral]
  have hr : D₁.atRisk 0 = 2 := by decide
  have hd : D₁.deaths 0 = 1 := rfl
  have h : Iic (0 : Fin 1) = {0} := by decide
  simp [prodIntegral, h, hr, hd]
  norm_num

example : D₁.nelsonAalen (D₁.time 0) = 1 / 2 := by
  rw [nelsonAalen_time_eq_sum]
  have hr : D₁.atRisk 0 = 2 := by decide
  have hd : D₁.deaths 0 = 1 := rfl
  have h : Iic (0 : Fin 1) = {0} := by decide
  simp [h, hr, hd]

/-- The grid Kaplan–Meier theorem has satisfiable hypotheses: for constant data the centred
increments vanish, and the conclusion is convergence to `0`. -/
example (v : Fin 2 → ℝ) (D : CensoredData 2) :
    TendstoInDistribution
      (fun (n : ℕ) (_ : Fin 2 → ℝ) ↦ √(n : ℝ) •
        ((fun j ↦ D.kmSurvival (D.time j)) -
          prodIntegral (-fun i ↦ (D.deaths i : ℝ) / D.atRisk i)))
      atTop (fun _ ↦ -duhamelDeriv (-fun i ↦ (D.deaths i : ℝ) / D.atRisk i) (0 : Fin 2 → ℝ))
      (fun _ ↦ Measure.dirac v) (Measure.dirac v) :=
  tendstoInDistribution_kmSurvival_grid (Dn := fun _ _ ↦ D) (G := fun _ ↦ (0 : Fin 2 → ℝ))
    ((tendstoInDistribution_const (l := atTop) (Z := (0 : (Fin 2 → ℝ) → Fin 2 → ℝ))
      aemeasurable_const).congr (fun n ↦ ae_of_all _ fun ω ↦ by simp)
      (ae_of_all _ fun _ ↦ rfl))

/-- `tendstoInDistribution_lInfty_of_hadamard` has satisfiable hypotheses (Borel σ-algebra on
`ℓ^∞([0, 1])`, constant process, identity map). This shows only non-vacuity of the abstract
statement, not anything about Kaplan–Meier. -/
example (v : Fin 2 → ℝ) (Λ : lp (fun _ : Set.Icc (0 : ℝ) 1 ↦ ℝ) ∞) :
    letI : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 1 ↦ ℝ) ∞) := borel _
    haveI : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 1 ↦ ℝ) ∞) := ⟨rfl⟩
    TendstoInDistribution (fun (n : ℕ) (_ : Fin 2 → ℝ) ↦ √(n : ℝ) • (id Λ - id Λ)) atTop
      (fun _ ↦ id 0) (fun _ ↦ Measure.dirac v) (Measure.dirac v) := by
  let _ : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 1 ↦ ℝ) ∞) := borel _
  have _ : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 1 ↦ ℝ) ∞) := ⟨rfl⟩
  exact tendstoInDistribution_lInfty_of_hadamard (Λhat := fun _ _ ↦ Λ) (G := fun _ ↦ 0)
    (dom := Set.univ)
    ((tendstoInDistribution_const (l := atTop) aemeasurable_const).congr
      (fun n ↦ ae_of_all _ fun _ ↦ by simp) (ae_of_all _ fun _ ↦ rfl))
    (ae_of_all _ fun _ ↦ by simpa using continuous_const)
    ((ContinuousLinearMap.id ℝ _).hasFDerivAt.hasHadamardDerivWithinAt _ _)
    (fun _ ↦ ae_of_all _ fun _ ↦ trivial) (fun _ ↦ aemeasurable_const) aemeasurable_const

end MathlibExtTest.Probability.Statistics.FunctionalDelta
