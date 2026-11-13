/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringBranchApplication
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FinCases

/-! Tests for `TuringBranchApplication` on a concrete two-mode Turing map.

`J₁ = [[1, -2], [3, -4]]` (`tr J₁ = -3`, `det J₁ = 2`: stable kinetics), `d_u = 1/4`, Neumann
wavenumbers `κ₁ = (0, 1)`. Mode `1` is critical at `d₀ = 4` (its mode matrix is
`[[3/4, -2], [3, -8]]`, determinant `0`), mode `0` is not (`det J₁ = 2`). The map is
`F₁(w, d) = (D(d) ∂ₓₓ + J₁) w + (w₁₀)³ e₁` with `e₁` the second species in mode `1`. The Fredholm
package uses the cokernel complement `ℝ e₁`; the implicit-function uniqueness then pins the
correction `W` to `0`, so the scalar bifurcation function is computed from the definitions:
`G̃(a, d) = a G₁(a, d)`, `G₁(a, d) = (3/29)(d - 4) - (32/29) a²`. Every hypothesis of
`turing_patternBranch_of_reduction` is proved, and the theorem's crossing speed
`(d_u k⁴ - f_u k²) / tr (J - k² D)` equals the directly computed `∂_d G₁ = 3/29`. The last test
shows that `G₁(0, d)` is not the critical eigenvalue for any `d ≠ 4` near `4`, so the exact
identity `G(0, d) = leadingEigenvalue (J - k² D(d))` is not available from this reduction. -/

open Filter Topology Matrix
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExtTest.Biology.Dynamics.TuringBranchApplication

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches
  MathlibExt.Biology.Dynamics.TuringBranchesPDE MathlibExt.Biology.Dynamics.TuringBranchApplication

/-- The Jacobian of the example. -/
def J₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, -2; 3, -4]

/-- The two Neumann wavenumbers of the example. -/
def κ₁ : Fin 2 → ℝ := ![0, 1]

theorem htr₁ : J₁.trace - κ₁ 1 ^ 2 * (1 / 4 + 4) < 0 := by
  simp [J₁, κ₁, Matrix.trace_fin_two]
  norm_num

theorem hk₁ : 0 < J₁ 0 0 * κ₁ 1 ^ 2 - 1 / 4 * (κ₁ 1 ^ 2) ^ 2 := by
  simp [J₁, κ₁]
  norm_num

theorem hd₁ : (4 : ℝ) = neutralDiffusion J₁ (1 / 4) (κ₁ 1 ^ 2) := by
  simp [neutralDiffusion, J₁, κ₁, det_fin_two]
  norm_num

theorem hfv₁ : J₁ 0 1 ≠ 0 := by simp [J₁]

theorem hnr₁ : ∀ i, i ≠ 1 → (modeMatrix J₁ (1 / 4) 4 (κ₁ i)).det ≠ 0 := by
  intro i hi
  fin_cases i
  · simp [modeMatrix, diffusionMatrix, J₁, κ₁, det_fin_two]
    norm_num
  · exact absurd rfl hi

theorem hcrit₁ : (modeMatrix J₁ (1 / 4) 4 (κ₁ 1)).det = 0 := by
  simp [modeMatrix, diffusionMatrix, J₁, κ₁, det_fin_two]
  norm_num

/-- The critical mode is `(-2, -3/4)` in mode `1`, computed from the definitions. -/
theorem criticalMode₁ : criticalMode J₁ (1 / 4) 4 κ₁ 1 = Pi.single 1 ![-2, -(3 / 4)] := by
  simp only [criticalMode, kerVec, modeMatrix, diffusionMatrix, J₁, κ₁]
  congr 1
  ext i; fin_cases i <;> norm_num

/-- The second species in mode `1`. -/
noncomputable def e₁ : Fin 2 → Fin 2 → ℝ := Pi.single 1 ![0, 1]

/-- The steady-state map `F₁(w, d) = (D(d) ∂ₓₓ + J₁) w + (w₁₀)³ e₁`. -/
noncomputable def F₁ (q : (Fin 2 → Fin 2 → ℝ) × ℝ) : Fin 2 → Fin 2 → ℝ :=
  modeOperator J₁ (1 / 4) q.2 κ₁ q.1 + (q.1 1 0) ^ 3 • e₁

/-- The coordinate `w ↦ w₁₀`. -/
noncomputable def c₁ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 ∘L ContinuousLinearMap.proj 1

/-- The derivative of `F₁` at `(0, 4)`: `(w, d) ↦ (D(4) ∂ₓₓ + J₁) w`. -/
noncomputable def F₁' : (Fin 2 → Fin 2 → ℝ) × ℝ →L[ℝ] Fin 2 → Fin 2 → ℝ :=
  modeOperator J₁ (1 / 4) 4 κ₁ ∘L ContinuousLinearMap.fst ℝ _ ℝ

theorem hF₁ : HasStrictFDerivAt F₁ F₁' ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)) := by
  have hfun : F₁ = fun q => modeOperator J₁ (1 / 4) 4 κ₁ q.1 +
      (q.2 - 4) • modeOperator 0 0 1 κ₁ q.1 + (c₁ q.1) ^ 3 • e₁ := by
    funext q
    rw [F₁, modeOperator_eq_add_smul J₁ (1 / 4) q.2 4 κ₁]
    rfl
  have hL := (modeOperator J₁ (1 / 4) 4 κ₁ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
    (x := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))
  have hS := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (E := Fin 2 → Fin 2 → ℝ) (F := ℝ)
    (p := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ)))).sub_const (4 : ℝ)).smul
    (modeOperator 0 0 1 κ₁ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
  have hN := ((c₁ ∘L ContinuousLinearMap.fst ℝ _ ℝ).hasStrictFDerivAt
    (x := ((0 : Fin 2 → Fin 2 → ℝ), (4 : ℝ))) |>.pow 3).smul_const e₁
  rw [hfun]
  exact ((hL.add hS).add hN).congr_fderiv (by ext <;> simp [F₁'])

theorem hFL₁ : F₁' ∘L .inl ℝ (Fin 2 → Fin 2 → ℝ) ℝ = modeOperator J₁ (1 / 4) 4 κ₁ := by
  ext; simp [F₁']

theorem htriv₁ : ∀ᶠ d in 𝓝 (4 : ℝ), F₁ (0, d) = 0 := Eventually.of_forall fun d => by simp [F₁]

theorem hlin₁ : ∀ᶠ d in 𝓝 (4 : ℝ),
    HasFDerivAt (fun w => F₁ (w, d)) (modeOperator J₁ (1 / 4) d κ₁) 0 :=
  Eventually.of_forall fun d =>
    ((modeOperator J₁ (1 / 4) d κ₁).hasFDerivAt.add
      ((c₁.hasFDerivAt (x := (0 : Fin 2 → Fin 2 → ℝ))).pow 3 |>.smul_const e₁)).congr_fderiv
      (by ext; simp)

/-! ### The Fredholm package with cokernel complement `ℝ e₁` -/

/-- `ψ(e₁) = 2` for the critical functional `y ↦ -8 y₁₀ + 2 y₁₁`. -/
theorem criticalFunctional_e₁ : criticalFunctional J₁ (1 / 4) 4 κ₁ 1 e₁ = 2 := by
  simp [e₁, J₁]

theorem isCompl_range₁ :
    IsCompl (modeOperator J₁ (1 / 4) 4 κ₁).range (Submodule.span ℝ {e₁}) := by
  have hran : ∀ y, y ∈ (modeOperator J₁ (1 / 4) 4 κ₁).range ↔
      criticalFunctional J₁ (1 / 4) 4 κ₁ 1 y = 0 := fun y =>
    LinearMap.mem_range.trans (exists_modeOperator_eq_iff hcrit₁ hfv₁ hnr₁ y)
  constructor
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    rw [hran, map_smul, criticalFunctional_e₁, smul_eq_mul] at hy
    rw [show c = 0 by linarith, zero_smul]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro y
    refine Submodule.mem_sup.2 ⟨y - (criticalFunctional J₁ (1 / 4) 4 κ₁ 1 y / 2) • e₁, (hran _).2 ?_,
      (criticalFunctional J₁ (1 / 4) 4 κ₁ 1 y / 2) • e₁,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), by abel⟩
    rw [map_sub, map_smul, criticalFunctional_e₁, smul_eq_mul]
    ring

/-- Some Fredholm package, used only for its domain complement. -/
noncomputable def pkg₀ : FredholmPackage (modeOperator J₁ (1 / 4) 4 κ₁) :=
  (isFredholm_modeOperator (J := J₁) (du := 1 / 4) (d := 4) (κ := κ₁)).nonempty_fredholmPackage.some

/-- The Fredholm package with cokernel complement `ℝ e₁`. -/
noncomputable def pkg₁ : FredholmPackage (modeOperator J₁ (1 / 4) 4 κ₁) :=
  (isFredholm_modeOperator (J := J₁) (du := 1 / 4) (d := 4) (κ := κ₁)).fredholmPackage
    (dom₁ := pkg₀.decDom.X₁) (codom₀ := Submodule.span ℝ {e₁})
    (by rw [pkg₀.ker_eq]; exact pkg₀.decDom.isTopCompl.symm)
    ((Submodule.IsCompl.isTopCompl_iff isCompl_range₁).2
      (LinearMap.continuous_of_finiteDimensional _))

theorem hφ₁ : criticalMode J₁ (1 / 4) 4 κ₁ 1 ∈ pkg₁.decDom.X₀ :=
  (modeOperator_simpleKernel hcrit₁ hfv₁ hnr₁ pkg₁).1

/-- On the critical line, `F₁(a φ, d) = ((3/4)(d - 4) a - 8 a³) e₁` lies in the cokernel
complement. -/
theorem F₁_smul_criticalMode (a d : ℝ) :
    F₁ (a • criticalMode J₁ (1 / 4) 4 κ₁ 1, d) = (3 / 4 * (d - 4) * a - 8 * a ^ 3) • e₁ := by
  rw [criticalMode₁]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [F₁, e₁, J₁, κ₁, modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · norm_num
  · ring

/-- **The correction vanishes**: `W(a φ, d) = 0` near `(0, 4)`, pinned down by the uniqueness
clause of the implicit function theorem (`eventually_lsRangeMap_eq_zero_iff`). -/
theorem eventually_lsSolution₁ : ∀ᶠ p in 𝓝 ((0 : ℝ), (4 : ℝ)),
    lsSolution pkg₁ hF₁ hFL₁ (p.1 • ⟨_, hφ₁⟩, p.2) = 0 := by
  set v : ℝ × ℝ → (pkg₁.decDom.X₀ × ℝ) × pkg₁.decDom.X₁ := fun p =>
    ((p.1 • ⟨_, hφ₁⟩, p.2), 0) with hv
  have ht : Tendsto v (𝓝 ((0 : ℝ), (4 : ℝ)))
      (𝓝 (((0 : pkg₁.decDom.X₀), (4 : ℝ)), (0 : pkg₁.decDom.X₁))) := by
    have hc : Continuous v := by fun_prop
    have h0 : v ((0 : ℝ), (4 : ℝ)) = (((0 : pkg₁.decDom.X₀), (4 : ℝ)), (0 : pkg₁.decDom.X₁)) := by
      simp only [hv, zero_smul]
    rw [← h0]
    exact hc.tendsto _
  filter_upwards [ht.eventually (eventually_lsRangeMap_eq_zero_iff pkg₁ hF₁ hFL₁
    (htriv₁.self_of_nhds))] with p hp
  have hR : lsRangeMap pkg₁ F₁ (v p) = 0 := by
    simp only [lsRangeMap, FredholmDecomposition.proj]
    rw [Submodule.projectionOntoL_apply_eq_zero_iff]
    have hx : lsEmbed pkg₁ (v p) = (p.1 • criticalMode J₁ (1 / 4) 4 κ₁ 1, p.2) := by
      simp only [hv, lsEmbed_apply, Submodule.coe_smul, Submodule.coe_zero, add_zero]
    rw [hx, F₁_smul_criticalMode]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact hp.1 hR

/-- The reduced factor `G₁(a, d) = (3/29)(d - 4) - (32/29) a²`. -/
noncomputable def G₁ (q : ℝ × ℝ) : ℝ := 3 / 29 * (q.2 - 4) - 32 / 29 * q.1 ^ 2

/-- **The scalar bifurcation function is `a G₁(a, d)`**, computed from `lsScalar` with the
normalized critical functional (`ψ(φ) = 29/2`, `ψ(e₁) = 2`). -/
theorem hfac₁ : ∀ᶠ q in 𝓝 ((0 : ℝ), (4 : ℝ)),
    lsScalar pkg₁ hφ₁ (normalizedCriticalFunctional J₁ (1 / 4) 4 κ₁ 1) hF₁ hFL₁ q = q.1 * G₁ q := by
  filter_upwards [eventually_lsSolution₁] with q hq
  have hψφ : criticalFunctional J₁ (1 / 4) 4 κ₁ 1 (criticalMode J₁ (1 / 4) 4 κ₁ 1) = 29 / 2 := by
    rw [criticalFunctional_criticalMode]
    simp [J₁, κ₁, Matrix.trace_fin_two]
    norm_num
  simp only [lsScalar, hq, Submodule.coe_zero, add_zero, F₁_smul_criticalMode,
    normalizedCriticalFunctional, _root_.smul_apply, map_smul, criticalFunctional_e₁,
    hψφ, smul_eq_mul, G₁]
  ring

theorem hG₁ : HasStrictFDerivAt G₁ ((3 / 29 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    ((0 : ℝ), (4 : ℝ)) := by
  have hfst := hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), (4 : ℝ)))
  have hsnd := hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), (4 : ℝ)))
  exact (((hsnd.sub_const 4).const_mul (3 / 29)).sub ((hfst.pow 2).const_mul (32 / 29))).congr_fderiv
    (by ext <;> simp)

/-! ### The theorem applies -/

/-- **The crossing speed is the reduced coefficient.** The theorem's value
`(d_u k⁴ - f_u k²) / tr (J - k² D(d₀))` of `∂_d G(0, d₀)` is the directly computed `3/29`. -/
example : (1 / 4 * (κ₁ 1 ^ 2) ^ 2 - J₁ 0 0 * κ₁ 1 ^ 2) / (J₁.trace - κ₁ 1 ^ 2 * (1 / 4 + 4)) =
    ((3 / 29 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) := by
  simp [J₁, κ₁, Matrix.trace_fin_two]
  norm_num

/-- **Non-vacuity.** For small `a ≠ 0` the theorem yields nonzero steady states `a φ` of `F₁` on
the branch `d = β(a)`, and `G₁(0, d)` has the sign of the critical eigenvalue near `4`. -/
example : ∃ β : ℝ → ℝ, β 0 = 4 ∧
    (∀ᶠ a in 𝓝[≠] (0 : ℝ), F₁ (a • criticalMode J₁ (1 / 4) 4 κ₁ 1, β a) = 0 ∧
      a • criticalMode J₁ (1 / 4) 4 κ₁ 1 ≠ 0) ∧
    ∀ᶠ d in 𝓝 (4 : ℝ), SignType.sign (G₁ (0, d)) =
      SignType.sign (leadingEigenvalue (modeMatrix J₁ (1 / 4) d (κ₁ 1))) := by
  obtain ⟨-, -, hsign, β, hβ0, hβd, -, hbr, -, -⟩ :=
    turing_patternBranch_of_reduction htr₁ hk₁ hd₁ hfv₁ hnr₁ pkg₁ hφ₁ hF₁ hFL₁ htriv₁ hlin₁ hfac₁
      hG₁
  refine ⟨β, hβ0, ?_, hsign⟩
  have hβc : Tendsto (fun a : ℝ => (a, β a)) (𝓝 0) (𝓝 ((0 : ℝ), (4 : ℝ))) :=
    tendsto_id.prodMk_nhds (hβ0 ▸ hβd.hasDerivAt.continuousAt.tendsto)
  filter_upwards [hbr, nhdsWithin_le_nhds (hβc.eventually eventually_lsSolution₁)] with a ha hW
  simp only [hW, Submodule.coe_zero, add_zero] at ha
  exact ha

/-- The branch is `d = 4 + (32/3) a²` (direct computation). -/
example (a : ℝ) : F₁ (a • criticalMode J₁ (1 / 4) 4 κ₁ 1, 4 + 32 / 3 * a ^ 2) = 0 := by
  rw [F₁_smul_criticalMode]
  ring_nf
  simp

/-- At `d = 5 > 4` the critical eigenvalue of mode `1` is positive and so is `G₁(0, 5) = 3/29`:
the signs agree, as the theorem says. The determinant of the mode matrix there is `-3/4 < 0`. -/
example : 0 < leadingEigenvalue (modeMatrix J₁ (1 / 4) 5 (κ₁ 1)) ∧ 0 < G₁ (0, 5) := by
  refine ⟨?_, by norm_num [G₁]⟩
  have htr : (modeMatrix J₁ (1 / 4) 5 (κ₁ 1)).trace = -33 / 4 := by
    rw [trace_modeMatrix]
    simp [J₁, κ₁, Matrix.trace_fin_two]
    norm_num
  have hdet : (modeMatrix J₁ (1 / 4) 5 (κ₁ 1)).det = -3 / 4 := by
    rw [det_modeMatrix, dispersionDet]
    simp [J₁, κ₁, det_fin_two]
    norm_num
  rw [leadingEigenvalue, htr, hdet]
  have h : 33 / 4 < Real.sqrt ((-33 / 4 : ℝ) ^ 2 - 4 * (-3 / 4)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- **The exact identity of the former interface fails for this reduction.** The reduced
coefficient `G₁(0, d) = (3/29)(d - 4)` is not the critical eigenvalue at any `d ≠ 4` near `4`: it
would be a root of `μ² - tr μ + det`, which equals `(96/841)(d - 4)²` at `μ = G₁(0, d)`. So a
hypothesis `G(0, d) = leadingEigenvalue (J - k² D(d))` near `d₀` cannot be discharged here, while
`turing_patternBranch_of_reduction` applies. -/
example : ¬ ∀ᶠ d in 𝓝 (4 : ℝ),
    G₁ (0, d) = leadingEigenvalue (modeMatrix J₁ (1 / 4) d (κ₁ 1)) := by
  intro h
  obtain ⟨d, ⟨hd, hd35⟩, hne⟩ := (((h.and (Ioo_mem_nhds (show (3 : ℝ) < 4 by norm_num)
    (show (4 : ℝ) < 5 by norm_num))).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[≠] (4 : ℝ), x ∈ ({4}ᶜ : Set ℝ))).exists
  have htr : (modeMatrix J₁ (1 / 4) d (κ₁ 1)).trace = -13 / 4 - d := by
    rw [trace_modeMatrix]
    simp [J₁, κ₁, Matrix.trace_fin_two]
    ring
  have hdet : (modeMatrix J₁ (1 / 4) d (κ₁ 1)).det = 3 - 3 / 4 * d := by
    rw [det_modeMatrix, dispersionDet]
    simp [J₁, κ₁, det_fin_two]
    ring
  have hdisc : 0 ≤ (-13 / 4 - d) ^ 2 - 4 * (3 - 3 / 4 * d) := by nlinarith [hd35.1, hd35.2]
  have hs := Real.sq_sqrt hdisc
  rw [leadingEigenvalue, htr, hdet] at hd
  have hd' : 3 / 29 * (d - 4) =
      ((-13 / 4 - d) + Real.sqrt ((-13 / 4 - d) ^ 2 - 4 * (3 - 3 / 4 * d))) / 2 := by
    rw [← hd, G₁]
    ring
  have hroot : (3 / 29 * (d - 4)) ^ 2 - (-13 / 4 - d) * (3 / 29 * (d - 4)) +
      (3 - 3 / 4 * d) = 0 := by
    rw [hd']
    nlinarith [hs]
  have h2 : (d - 4) ^ 2 = 0 := by linear_combination (841 / 96 : ℝ) * hroot
  exact hne (Set.mem_singleton_iff.2 (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)))

end MathlibExtTest.Biology.Dynamics.TuringBranchApplication
