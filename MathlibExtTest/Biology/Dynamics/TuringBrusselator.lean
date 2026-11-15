/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringBrusselator
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FinCases

/-! Tests for `TuringBrusselator` on the Brusselator with `a = 2`, `b = 4`.

`J₂ = brusselatorJacobian 2 4 = [[3, 4], [-4, -4]]` (`tr J₂ = -1`, `det J₂ = 4`: stable kinetics),
`d_u = 1`, Neumann wavenumbers `κ₂ = (0, 1)`. Mode `1` is critical at `d₀ = 4` (its mode matrix is
`[[2, 4], [-4, -8]]`), mode `0` is not (`det J₂ = 4`). This is the Turing threshold for `d = 4`:
`b = (1 + a / √d)² = 4`. The map is `F₂(w, d) = (D(d) ∂ₓₓ + J₂) w - (w₁₀)² w₁₁ e₁`, the
Brusselator's cubic term `-u² v` of the inhibitor equation kept on mode `1` alone (a toy truncation, not the
Galerkin projection). On the critical line `F₂(s φ, d) = (2 (d - 4) s + 32 s³) e₁`, so with the
cokernel complement `ℝ e₁` the correction `W` vanishes and the scalar bifurcation function is
computed from the definitions: `G₂(s, d) = (d - 4) / 3 + (16 / 3) s²`. Every hypothesis of
`brusselator_patternBranch_of_reduction` is proved, and its crossing speed equals the directly
computed `∂_d G₂ = 1/3`. The branch `d = 4 - 16 s²` is subcritical. -/

open Filter Topology Matrix
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExtTest.Biology.Dynamics.TuringBrusselator

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches
  MathlibExt.Biology.Dynamics.TuringBranchesPDE MathlibExt.Biology.Dynamics.TuringBranchApplication
  MathlibExt.Biology.Dynamics.TuringBrusselator

/-! ### Kinetics, computed from the definitions -/

/-- `(2, 2)` is the steady state of the Brusselator with `a = 2`, `b = 4`. -/
example : brusselator 2 4 ![2, 2] = 0 := by
  funext i
  fin_cases i <;> norm_num [brusselator]

/-- A point off the steady state is not a zero of the kinetics. -/
example : brusselator 2 4 ![1, 1] ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [brusselator] at this

/-- The Jacobian at `a = 2`, `b = 4`. -/
example : brusselatorJacobian 2 4 = !![3, 4; -4, -4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [brusselatorJacobian]

/-- The neutral diffusion of the mode `k = 1` is `4`, computed from `neutralDiffusion`. -/
example : neutralDiffusion (brusselatorJacobian 2 4) 1 1 = 4 := by
  norm_num [neutralDiffusion, brusselatorJacobian, det_fin_two]

/-! ### The Turing threshold, from the dispersion polynomial -/

theorem htrJ (b : ℝ) (hb : b < 5) : (brusselatorJacobian 2 b).trace < 0 := by
  simp [brusselatorJacobian, Matrix.trace_fin_two]
  linarith

/-- Above threshold (`b = 9/2`, `d = 4`) the mode `k = 1` is unstable: `h(1) = -2`. -/
example : IsUnstableMode (brusselatorJacobian 2 (9 / 2)) 1 4 1 := by
  rw [isUnstableMode_iff_dispersionDet_neg (htrJ _ (by norm_num)) zero_le_one (by norm_num)]
  norm_num [dispersionDet, brusselatorJacobian, det_fin_two]

/-- At threshold (`b = 4`, `d = 4`) no mode is unstable: `h(q) = 4 (q - 1)² ≥ 0`. -/
theorem not_unstable_threshold : ¬ ∃ k, IsUnstableMode (brusselatorJacobian 2 4) 1 4 k := by
  rintro ⟨k, hk⟩
  rw [isUnstableMode_iff_dispersionDet_neg (htrJ _ (by norm_num)) zero_le_one (by norm_num)] at hk
  norm_num [dispersionDet, brusselatorJacobian, det_fin_two] at hk
  nlinarith [sq_nonneg (k ^ 2 - 1)]

/-- `brusselator_turing_iff` agrees at both test points: its threshold inequality holds at
`b = 9/2` and fails at `b = 4`. -/
example : (2 * 2 * Real.sqrt 4 < 4 * ((9 / 2 : ℝ) - 1) - 2 ^ 2) ∧
    ¬ (2 * 2 * Real.sqrt 4 < 4 * ((4 : ℝ) - 1) - 2 ^ 2) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

example : ¬ (2 * 2 * Real.sqrt 4 < 4 * ((4 : ℝ) - 1) - 2 ^ 2) ↔
    ¬ ∃ k, IsUnstableMode (brusselatorJacobian 2 4) 1 4 k :=
  not_congr (brusselator_turing_iff (by norm_num) (by norm_num) (by norm_num)).symm

/-! ### A concrete steady-state map -/

/-- The two Neumann wavenumbers of the example. -/
def κ₂ : Fin 2 → ℝ := ![0, 1]

theorem hb₂ : (4 : ℝ) < 1 + 2 ^ 2 := by norm_num

theorem hk₂ : 0 < ((4 : ℝ) - 1) * κ₂ 1 ^ 2 - 1 * (κ₂ 1 ^ 2) ^ 2 := by
  norm_num [κ₂]

theorem hd₂ : (4 : ℝ) = brusselatorNeutralDiffusion 2 4 1 (κ₂ 1 ^ 2) := by
  norm_num [brusselatorNeutralDiffusion, κ₂]

theorem hnr₂ : ∀ i, i ≠ 1 → (modeMatrix (brusselatorJacobian 2 4) 1 4 (κ₂ i)).det ≠ 0 := by
  intro i hi
  fin_cases i
  · norm_num [modeMatrix, diffusionMatrix, brusselatorJacobian, κ₂, det_fin_two]
  · exact absurd rfl hi

theorem hcrit₂ : (modeMatrix (brusselatorJacobian 2 4) 1 4 (κ₂ 1)).det = 0 := by
  norm_num [modeMatrix, diffusionMatrix, brusselatorJacobian, κ₂, det_fin_two]

theorem hfv₂ : brusselatorJacobian (2 : ℝ) 4 0 1 ≠ 0 := by norm_num

/-- The critical mode is `(4, -2)` in mode `1`, computed from the definitions. -/
theorem criticalMode₂ : criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1 = Pi.single 1 ![4, -2] := by
  simp only [criticalMode, kerVec, modeMatrix, diffusionMatrix, brusselatorJacobian, κ₂]
  congr 1
  ext i; fin_cases i <;> norm_num

/-- The second species in mode `1`. -/
noncomputable def e₁ : Fin 2 → Fin 2 → ℝ := Pi.single 1 ![0, 1]

/-- The steady-state map `F₂(w, d) = (D(d) ∂ₓₓ + J₂) w - (w₁₀)² w₁₁ e₁`. -/
noncomputable def F₂ (q : (Fin 2 → Fin 2 → ℝ) × ℝ) : Fin 2 → Fin 2 → ℝ :=
  modeOperator (brusselatorJacobian 2 4) 1 q.2 κ₂ q.1 + (-(q.1 1 0 ^ 2 * q.1 1 1)) • e₁

/-- The coordinate `w ↦ w₁₀`. -/
noncomputable def c₀ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 ∘L ContinuousLinearMap.proj 1

/-- The coordinate `w ↦ w₁₁`. -/
noncomputable def c₁ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 1 ∘L ContinuousLinearMap.proj 1

/-- The derivative of `F₂` at `(0, 4)`: `(w, d) ↦ (D(4) ∂ₓₓ + J₂) w`. -/
noncomputable def F₂' : (Fin 2 → Fin 2 → ℝ) × ℝ →L[ℝ] Fin 2 → Fin 2 → ℝ :=
  modeOperator (brusselatorJacobian 2 4) 1 4 κ₂ ∘L ContinuousLinearMap.fst ℝ _ ℝ

theorem hF₂ : HasStrictFDerivAt F₂ F₂' ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)) := by
  have hfun : F₂ = fun q => modeOperator (brusselatorJacobian 2 4) 1 4 κ₂ q.1 +
      (q.2 - 4) • modeOperator 0 0 1 κ₂ q.1 + (-((c₀ q.1) ^ 2 * c₁ q.1)) • e₁ := by
    funext q
    rw [F₂, modeOperator_eq_add_smul (brusselatorJacobian 2 4) 1 q.2 4 κ₂]
    rfl
  have hL := (modeOperator (brusselatorJacobian 2 4) 1 4 κ₂ ∘L
    ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt (x := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))
  have hS := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (E := Fin 2 → Fin 2 → ℝ) (F := ℝ)
    (p := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))).sub_const (4 : ℝ)).smul
    (modeOperator 0 0 1 κ₂ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
  have h0 := (c₀ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
    (x := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))
  have h1 := (c₁ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
    (x := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))
  have hN := ((h0.pow 2).mul h1).neg.smul_const e₁
  rw [hfun]
  exact ((hL.add hS).add hN).congr_fderiv (by ext <;> simp [F₂'])

theorem hFL₂ :
    F₂' ∘L .inl ℝ (Fin 2 → Fin 2 → ℝ) ℝ = modeOperator (brusselatorJacobian 2 4) 1 4 κ₂ := by
  ext; simp [F₂']

theorem htriv₂ : ∀ᶠ d in 𝓝 (4 : ℝ), F₂ (0, d) = 0 := Eventually.of_forall fun d => by simp [F₂]

theorem hlin₂ : ∀ᶠ d in 𝓝 (4 : ℝ),
    HasFDerivAt (fun w => F₂ (w, d)) (modeOperator (brusselatorJacobian 2 4) 1 d κ₂) 0 :=
  Eventually.of_forall fun d =>
    ((modeOperator (brusselatorJacobian 2 4) 1 d κ₂).hasFDerivAt.add
      ((((c₀.hasFDerivAt (x := (0 : Fin 2 → Fin 2 → ℝ))).pow 2).mul
        (c₁.hasFDerivAt (x := (0 : Fin 2 → Fin 2 → ℝ)))).neg.smul_const e₁)).congr_fderiv
      (by ext; simp)

/-! ### The Fredholm package with cokernel complement `ℝ e₁` -/

/-- `ψ(e₁) = -4` for the critical functional `y ↦ -8 y₁₀ - 4 y₁₁`. -/
theorem criticalFunctional_e₁ : criticalFunctional (brusselatorJacobian 2 4) 1 4 κ₂ 1 e₁ = -4 := by
  norm_num [e₁, brusselatorJacobian]

theorem isCompl_range₂ :
    IsCompl (modeOperator (brusselatorJacobian 2 4) 1 4 κ₂).range (Submodule.span ℝ {e₁}) := by
  have hran : ∀ y, y ∈ (modeOperator (brusselatorJacobian 2 4) 1 4 κ₂).range ↔
      criticalFunctional (brusselatorJacobian 2 4) 1 4 κ₂ 1 y = 0 := fun y =>
    LinearMap.mem_range.trans (exists_modeOperator_eq_iff hcrit₂ hfv₂ hnr₂ y)
  constructor
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    rw [hran, map_smul, criticalFunctional_e₁, smul_eq_mul] at hy
    rw [show c = 0 by linarith, zero_smul]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro y
    set c := criticalFunctional (brusselatorJacobian 2 4) 1 4 κ₂ 1 y / -4 with hc
    refine Submodule.mem_sup.2 ⟨y - c • e₁, (hran _).2 ?_, c • e₁,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), by abel⟩
    rw [map_sub, map_smul, criticalFunctional_e₁, smul_eq_mul, hc]
    ring

/-- Some Fredholm package, used only for its domain complement. -/
noncomputable def pkg₀ : FredholmPackage (modeOperator (brusselatorJacobian 2 4) 1 4 κ₂) :=
  (isFredholm_modeOperator (J := brusselatorJacobian 2 4) (du := 1) (d := 4)
    (κ := κ₂)).nonempty_fredholmPackage.some

/-- The Fredholm package with cokernel complement `ℝ e₁`. -/
noncomputable def pkg₂ : FredholmPackage (modeOperator (brusselatorJacobian 2 4) 1 4 κ₂) :=
  (isFredholm_modeOperator (J := brusselatorJacobian 2 4) (du := 1) (d := 4)
    (κ := κ₂)).fredholmPackage
    (dom₁ := pkg₀.decDom.X₁) (codom₀ := Submodule.span ℝ {e₁})
    (by rw [pkg₀.ker_eq]; exact pkg₀.decDom.isTopCompl.symm)
    ((Submodule.IsCompl.isTopCompl_iff isCompl_range₂).2
      (LinearMap.continuous_of_finiteDimensional _))

theorem hφ₂ : criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1 ∈ pkg₂.decDom.X₀ :=
  (modeOperator_simpleKernel hcrit₂ hfv₂ hnr₂ pkg₂).1

/-- On the critical line, `F₂(s φ, d) = (2 (d - 4) s + 32 s³) e₁` lies in the cokernel
complement. -/
theorem F₂_smul_criticalMode (s d : ℝ) :
    F₂ (s • criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1, d) =
      (2 * (d - 4) * s + 32 * s ^ 3) • e₁ := by
  rw [criticalMode₂]
  funext i j
  fin_cases i <;> fin_cases j
  · norm_num [F₂, e₁]
  · norm_num [F₂, e₁]
  · norm_num [F₂, e₁, brusselatorJacobian, κ₂, modeMatrix, diffusionMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  · norm_num [F₂, e₁, brusselatorJacobian, κ₂, modeMatrix, diffusionMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring

/-- **The correction vanishes**: `W(s φ, d) = 0` near `(0, 4)`, pinned down by the uniqueness
clause of the implicit function theorem (`eventually_lsRangeMap_eq_zero_iff`). -/
theorem eventually_lsSolution₂ : ∀ᶠ p in 𝓝 ((0 : ℝ), (4 : ℝ)),
    lsSolution pkg₂ hF₂ hFL₂ (p.1 • ⟨_, hφ₂⟩, p.2) = 0 := by
  set v : ℝ × ℝ → (pkg₂.decDom.X₀ × ℝ) × pkg₂.decDom.X₁ := fun p =>
    ((p.1 • ⟨_, hφ₂⟩, p.2), 0) with hv
  have ht : Tendsto v (𝓝 ((0 : ℝ), (4 : ℝ)))
      (𝓝 (((0 : pkg₂.decDom.X₀), (4 : ℝ)), (0 : pkg₂.decDom.X₁))) := by
    have hc : Continuous v := by fun_prop
    have h0 : v ((0 : ℝ), (4 : ℝ)) = (((0 : pkg₂.decDom.X₀), (4 : ℝ)), (0 : pkg₂.decDom.X₁)) := by
      simp only [hv, zero_smul]
    rw [← h0]
    exact hc.tendsto _
  filter_upwards [ht.eventually (eventually_lsRangeMap_eq_zero_iff pkg₂ hF₂ hFL₂
    (htriv₂.self_of_nhds))] with p hp
  have hR : lsRangeMap pkg₂ F₂ (v p) = 0 := by
    simp only [lsRangeMap, FredholmDecomposition.proj]
    rw [Submodule.projectionOntoL_apply_eq_zero_iff]
    have hx : lsEmbed pkg₂ (v p) =
        (p.1 • criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1, p.2) := by
      simp only [hv, lsEmbed_apply, Submodule.coe_smul, Submodule.coe_zero, add_zero]
    rw [hx, F₂_smul_criticalMode]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact hp.1 hR

/-- The reduced factor `G₂(s, d) = (d - 4) / 3 + (16 / 3) s²`. -/
noncomputable def G₂ (q : ℝ × ℝ) : ℝ := 1 / 3 * (q.2 - 4) + 16 / 3 * q.1 ^ 2

/-- **The scalar bifurcation function is `s G₂(s, d)`**, computed from `lsScalar` with the
normalized critical functional (`ψ(φ) = -24`, `ψ(e₁) = -4`). -/
theorem hfac₂ : ∀ᶠ q in 𝓝 ((0 : ℝ), (4 : ℝ)),
    lsScalar pkg₂ hφ₂ (normalizedCriticalFunctional (brusselatorJacobian 2 4) 1 4 κ₂ 1) hF₂ hFL₂ q =
      q.1 * G₂ q := by
  filter_upwards [eventually_lsSolution₂] with q hq
  have hψφ : criticalFunctional (brusselatorJacobian 2 4) 1 4 κ₂ 1
      (criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1) = -24 := by
    rw [criticalFunctional_criticalMode]
    norm_num [brusselatorJacobian, κ₂, Matrix.trace_fin_two]
  simp only [lsScalar, hq, Submodule.coe_zero, add_zero, F₂_smul_criticalMode,
    normalizedCriticalFunctional, _root_.smul_apply, map_smul, criticalFunctional_e₁,
    hψφ, smul_eq_mul, G₂]
  ring

theorem hG₂ : HasStrictFDerivAt G₂ ((1 / 3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    ((0 : ℝ), (4 : ℝ)) := by
  have hfst := hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), (4 : ℝ)))
  have hsnd := hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), (4 : ℝ)))
  exact (((hsnd.sub_const 4).const_mul (1 / 3)).add ((hfst.pow 2).const_mul (16 / 3))).congr_fderiv
    (by ext <;> simp)

/-! ### The theorem applies -/

/-- **The crossing speed is the reduced coefficient.** The theorem's value
`(d_u k⁴ - (b - 1) k²) / (b - 1 - a² - k² (d_u + d₀))` of `∂_d G(0, d₀)` is the directly computed
`1/3`. -/
example : (1 * (κ₂ 1 ^ 2) ^ 2 - ((4 : ℝ) - 1) * κ₂ 1 ^ 2) / (4 - 1 - 2 ^ 2 - κ₂ 1 ^ 2 * (1 + 4)) =
    ((1 / 3 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) := by
  norm_num [κ₂]

/-- **Non-vacuity.** For small `s ≠ 0` the theorem yields nonzero steady states `s φ` of `F₂` on
the branch `d = β(s)`, and `G₂(0, d)` has the sign of the critical eigenvalue near `4`. -/
example : ∃ β : ℝ → ℝ, β 0 = 4 ∧
    (∀ᶠ s in 𝓝[≠] (0 : ℝ), F₂ (s • criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1, β s) = 0 ∧
      s • criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1 ≠ 0) ∧
    ∀ᶠ d in 𝓝 (4 : ℝ), SignType.sign (G₂ (0, d)) =
      SignType.sign (leadingEigenvalue (modeMatrix (brusselatorJacobian 2 4) 1 d (κ₂ 1))) := by
  obtain ⟨-, -, hsign, β, hβ0, hβd, -, hbr, -, -⟩ :=
    brusselator_patternBranch_of_reduction two_ne_zero hb₂ zero_le_one hk₂ hd₂ hnr₂ pkg₂ hφ₂ hF₂
      hFL₂ htriv₂ hlin₂ hfac₂ hG₂
  refine ⟨β, hβ0, ?_, hsign⟩
  have hβc : Tendsto (fun s : ℝ => (s, β s)) (𝓝 0) (𝓝 ((0 : ℝ), (4 : ℝ))) :=
    tendsto_id.prodMk_nhds (hβ0 ▸ hβd.hasDerivAt.continuousAt.tendsto)
  filter_upwards [hbr, nhdsWithin_le_nhds (hβc.eventually eventually_lsSolution₂)] with s hs hW
  simp only [hW, Submodule.coe_zero, add_zero] at hs
  exact hs

/-- The branch is `d = 4 - 16 s²` (direct computation): it bends to `d < d₀`. -/
example (s : ℝ) : F₂ (s • criticalMode (brusselatorJacobian 2 4) 1 4 κ₂ 1, 4 - 16 * s ^ 2) = 0 := by
  rw [F₂_smul_criticalMode]
  ring_nf
  simp

/-- At `d = 5 > 4` the critical eigenvalue of mode `1` is positive and so is `G₂(0, 5) = 1/3`:
the signs agree, as the theorem says. The mode matrix there has trace `-7` and determinant `-2`. -/
example : 0 < leadingEigenvalue (modeMatrix (brusselatorJacobian 2 4) 1 5 (κ₂ 1)) ∧
    0 < G₂ (0, 5) := by
  refine ⟨?_, by norm_num [G₂]⟩
  have htr : (modeMatrix (brusselatorJacobian 2 4) 1 5 (κ₂ 1)).trace = -7 := by
    rw [trace_modeMatrix]
    norm_num [brusselatorJacobian, κ₂, Matrix.trace_fin_two]
  have hdet : (modeMatrix (brusselatorJacobian 2 4) 1 5 (κ₂ 1)).det = -2 := by
    rw [det_modeMatrix, dispersionDet]
    norm_num [brusselatorJacobian, κ₂, det_fin_two]
  have h : 7 < Real.sqrt 57 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [leadingEigenvalue, htr, hdet]
  norm_num
  linarith

end MathlibExtTest.Biology.Dynamics.TuringBrusselator
