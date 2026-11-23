/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ContinuousProductIntegral

/-!
# Tests for the Hadamard differentiability of the product integral

* Concrete values of `gridDuhamel` and its Duhamel equation.
* A genuine instance of `IsDuhamelProductIntegral` (T44's grid product integral on a
  total-variation ball) and the Hadamard derivative it yields, which is T44's `duhamelDeriv`.
* `hasHadamardDerivWithinAt_of_duhamel` for a continuous linear map (the derivative is the map).
* A satisfiable instance of `IsStieltjesProductIntegral` and of the hypotheses of
  `tendstoInDistribution_kmSurvival_lInfty`, at the degenerate horizon `τ = 0` (where the product
  integral over `(0, 0]` is identically `1`). This shows consistency of the hypothesis bundle;
  a genuine `τ > 0` instance is the Lebesgue–Stieltjes product integral of T77.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.FunctionalDelta
open MathlibExt.Probability.Statistics.ContinuousProductIntegral
open MathlibExt.Probability.Statistics.KaplanMeier
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.ContinuousProductIntegral

/-! ### The grid Duhamel operator -/

example (a b c d : ℝ) (h : Fin 2 → ℝ) :
    gridDuhamel ![a, b] ![c, d] h 1 = h 0 * (1 + d) + (1 + a) * h 1 := by
  rw [gridDuhamel_apply]
  have h1 : Iic (1 : Fin 2) = {0, 1} := by decide
  have h2 : Iio (0 : Fin 2) = ∅ := by decide
  have h3 : Ioc (0 : Fin 2) 1 = {1} := by decide
  have h4 : Iio (1 : Fin 2) = {0} := by decide
  simp [h1, h2, h3, h4]

/-- The Duhamel equation on `Fin 1`: `(1 + y) - (1 + x) = 1 · (y - x) · 1`. -/
example (x y : Fin 1 → ℝ) :
    prodIntegral y - prodIntegral x = gridDuhamel x y (y - x) :=
  prodIntegral_sub_prodIntegral_eq_gridDuhamel x y

/-- At `x = y = 0` the Duhamel operator is the cumulative sum. -/
example {k : ℕ} (h : Fin k → ℝ) (j : Fin k) :
    gridDuhamel 0 0 h j = ∑ i ∈ Iic j, h i := by
  simp [gridDuhamel_apply]

/-! ### A genuine instance of the Duhamel hypotheses -/

/-- T44's grid product integral is Hadamard differentiable on a total-variation ball through
`IsDuhamelProductIntegral`, and the derivative it produces is T44's `duhamelDeriv`. -/
example {k : ℕ} (M : ℝ) (x : Fin k → ℝ) (hx : ∑ l, |x l| ≤ M) :
    HasHadamardDerivWithinAt prodIntegral (duhamelDeriv x) {y | ∑ l, |y l| ≤ M} Set.univ x := by
  have := (isDuhamelProductIntegral_prodIntegral (k := k) M).hasHadamardDerivWithinAt
    (E₀ := Set.univ) hx (by simp)
  rwa [gridDuhamel_self] at this

/-- The Lipschitz bound on a total-variation ball, for the grid product integral. -/
example {k : ℕ} (M : ℝ) (x y : Fin k → ℝ) (hx : ∑ l, |x l| ≤ M) (hy : ∑ l, |y l| ≤ M) :
    ‖prodIntegral y - prodIntegral x‖ ≤ k * (Real.exp M * Real.exp M) * ‖y - x‖ :=
  (isDuhamelProductIntegral_prodIntegral M).norm_sub_le hx hy

/-- The abstract theorem for a continuous linear map `L`, with `Ψ B = L`: the derivative is `L`. -/
example (L : ℝ →L[ℝ] ℝ) (θ : ℝ) :
    HasHadamardDerivWithinAt L L Set.univ Set.univ θ :=
  hasHadamardDerivWithinAt_of_duhamel (Ψ := fun _ ↦ L) (S := Set.univ) (C := ‖L‖)
    (Set.mem_univ θ) (fun B _ ↦ (map_sub L B θ).symm) (fun _ _ ↦ le_rfl)
    (fun _ _ ↦ tendsto_const_nhds) (by simp)

/-! ### The `ℓ^∞` hypothesis bundle at the degenerate horizon `τ = 0` -/

/-- The constant function `1` in `ℓ^∞([0, 0])`. -/
noncomputable def one₀ : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ :=
  ⟨fun _ ↦ 1, memℓp_infty_iff.2 ⟨1, by rintro _ ⟨_, rfl⟩; simp⟩⟩

theorem one₀_apply (t : Set.Icc (0 : ℝ) 0) : one₀ t = 1 := rfl

/-- On `[0, 0]` every jump time `s j > 0` lies after `t`. -/
theorem filter_eq_empty_of_pos {k : ℕ} (s : Fin k → ℝ) (hs : ∀ j, 0 < s j)
    (t : Set.Icc (0 : ℝ) 0) : (univ.filter fun j ↦ s j ≤ (t : ℝ)) = ∅ :=
  filter_false_of_mem fun j _ ↦ not_le.2 ((t.2.2).trans_lt (hs j))

/-- On the horizon `τ = 0` the product integral over `(0, 0]` is identically `1`, with zero
Duhamel operator: the hypothesis bundle `IsStieltjesProductIntegral` is satisfiable. -/
theorem isStieltjesProductIntegral_zero :
    IsStieltjesProductIntegral 0 (fun _ ↦ one₀) (fun _ _ ↦ 0) Set.univ Set.univ 0 where
  duhamel _ _ _ _ := by simp
  norm_le _ _ _ _ := by simp
  tendsto _ _ _ _ := tendsto_const_nhds
  continuous_subset_closure := by simp
  pureJump s a _ hs _ _ t := by
    rw [one₀_apply, filter_eq_empty_of_pos s hs t, prod_empty]

/-- The resulting Hadamard derivative at `0` is `0`. -/
example : HasHadamardDerivWithinAt (fun _ ↦ one₀) (fun _ ↦ 0) Set.univ
    {h : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ | Continuous fun t ↦ h t} 0 := by
  have := isStieltjesProductIntegral_zero.hasHadamardDerivWithinAt (Set.mem_univ 0)
  exact this

/-- The `C[0, τ]` corollary for the survival map, on the degenerate instance. -/
example : HasHadamardDerivWithinAt (fun _ ↦ one₀) (fun h ↦ -(0 : _ →L[ℝ] _) h) Set.univ
    {h : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ | Continuous fun t ↦ h t} 0 :=
  isStieltjesProductIntegral_zero.hasHadamardDerivWithinAt_neg_continuous (Set.mem_univ _)

/-- One subject, one death at time `1`. -/
def D₁ : CensoredData 1 where
  time := fun _ ↦ 1
  strictMono_time := Subsingleton.strictMono _
  deaths := fun _ ↦ 1
  censored := fun _ ↦ 0

/-- `tendstoInDistribution_kmSurvival_lInfty` has satisfiable hypotheses: horizon `τ = 0`,
constant data `D₁` (no event in `[0, 0]`), so `Λ̂ = 0`, `Ŝ = 1`, and the limit is `0`. This shows
only consistency of the hypotheses (the `ℓ^∞` processes here are constant, hence Borel
measurable); it is not an instance of the measurability caveat's failing case. -/
example :
    letI : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
    haveI : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
    TendstoInDistribution (fun (n : ℕ) (_ : Unit) ↦ √(n : ℝ) • (one₀ - one₀)) atTop
      (fun _ ↦ -(0 : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ →L[ℝ] _) 0)
      (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) := by
  let _ : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
  have _ : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
  refine tendstoInDistribution_kmSurvival_lInfty isStieltjesProductIntegral_zero
    (Dn := fun _ _ ↦ D₁) (fun _ _ _ ↦ one_pos) (Λhat := fun _ _ ↦ 0) (KMhat := fun _ _ ↦ one₀)
    (Λ := 0) (G := fun _ ↦ 0) ?_ ?_ (Set.mem_univ _) ?_ ?_ (fun _ ↦ ae_of_all _ fun _ ↦ trivial)
    (fun _ ↦ aemeasurable_const)
  · intro _ _ t
    rw [CensoredData.nelsonAalen, filter_eq_empty_of_pos D₁.time (fun _ ↦ one_pos) t, sum_empty]
    rfl
  · intro _ _ t
    rw [CensoredData.kmSurvival, filter_eq_empty_of_pos D₁.time (fun _ ↦ one_pos) t, prod_empty]
    rfl
  · exact (tendstoInDistribution_const (l := atTop) aemeasurable_const).congr
      (fun n ↦ ae_of_all _ fun _ ↦ by simp) (ae_of_all _ fun _ ↦ rfl)
  · exact ae_of_all _ fun _ ↦ by simp

end MathlibExtTest.Probability.Statistics.ContinuousProductIntegral
