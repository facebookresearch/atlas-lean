/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringBranchesPDE
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Tactic.FinCases

/-! Tests for the Lyapunov–Schmidt reduction of Turing pattern branches: the `2 × 2` kernel and
range lemmas on concrete matrices (and the boundary case `m₀₁ = 0`), the coefficient
linearization at a concrete critical, non-resonant Turing mode (and the resonant boundary case),
the mode-field bridge, and the full reduction chain on the pitchfork `F(x, d) = (d - d₀) x - x³`,
whose scalar bifurcation function and pattern branch `d = d₀ + a²` are computed from the
definitions. -/

open Filter Topology Matrix
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExtTest.Biology.Dynamics.TuringBranchesPDE

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranchesPDE

/-! ### `2 × 2` kernel and range -/

/-- The kernel vector of `[[1, 1], [2, 2]]` is `(1, -1)`, and it is killed (direct computation). -/
example : kerVec !![(1 : ℝ), 1; 2, 2] = ![1, -1] := by
  simp [kerVec]

example : !![(1 : ℝ), 1; 2, 2] *ᵥ ![1, -1] = 0 := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct]

/-- `(3, -3)` lies in the kernel and is the multiple `3 · kerVec`. -/
example : ∃ a : ℝ, ![(3 : ℝ), -3] = a • kerVec !![(1 : ℝ), 1; 2, 2] :=
  (mulVec_eq_zero_iff_of_det_eq_zero (by simp [det_fin_two]) (by simp) _).1
    (by ext i; fin_cases i <;> simp [mulVec, dotProduct])

/-- Range: `(1, 2) = M (1, 0)` satisfies the criterion `m₁₁ y₀ - m₀₁ y₁ = 0`; `(1, 0)` violates it
and is not in the range. -/
example : !![(1 : ℝ), 1; 2, 2] *ᵥ ![1, 0] = ![1, 2] := by
  ext i; fin_cases i <;> simp [mulVec, dotProduct]

example : ¬ ∃ w, !![(1 : ℝ), 1; 2, 2] *ᵥ w = ![1, 0] := by
  rw [exists_mulVec_eq_iff_of_det_eq_zero (by simp [det_fin_two]) (by simp)]
  norm_num

/-- **Boundary case `m₀₁ = 0`.** For `[[0, 0], [1, 0]]` the formula `(m₀₁, -m₀₀)` gives the zero
vector, while `(0, 1)` is a nonzero kernel vector: the hypothesis `m₀₁ ≠ 0` is needed. -/
example : kerVec !![(0 : ℝ), 0; 1, 0] = 0 ∧ !![(0 : ℝ), 0; 1, 0] *ᵥ ![0, 1] = 0 ∧
    ¬ ∃ a : ℝ, ![(0 : ℝ), 1] = a • kerVec !![(0 : ℝ), 0; 1, 0] := by
  refine ⟨by ext i; fin_cases i <;> simp [kerVec], by
    ext i; fin_cases i <;> simp [mulVec, dotProduct], ?_⟩
  rintro ⟨a, ha⟩
  have := congrFun ha 1
  simp [kerVec] at this

/-! ### A concrete critical Turing mode

`J = [[1, -2], [3, -4]]` (`tr J = -3 < 0`, `det J = 2 > 0`: stable kinetics), `d_u = 1/4`,
`d = 4`, wavenumbers `κ = (0, 1, 2)`. Mode `1` is critical,
`det (J - D) = (3/4)(-8) + 6 = 0`, and modes `0, 2` are not (`det = 2, 6`). -/

/-- The Jacobian of the example. -/
def J₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, -2; 3, -4]

/-- The three wavenumbers of the example. -/
def κ₀ : Fin 3 → ℝ := ![0, 1, 2]

theorem hcrit₀ : (modeMatrix J₀ (1 / 4) 4 (κ₀ 1)).det = 0 := by
  simp [modeMatrix, diffusionMatrix, J₀, κ₀, det_fin_two]
  norm_num

theorem hnr₀ : ∀ i, i ≠ 1 → (modeMatrix J₀ (1 / 4) 4 (κ₀ i)).det ≠ 0 := by
  intro i hi
  fin_cases i
  · simp [modeMatrix, diffusionMatrix, J₀, κ₀, det_fin_two]; norm_num
  · exact absurd rfl hi
  · simp [modeMatrix, diffusionMatrix, J₀, κ₀, det_fin_two]; norm_num

theorem hfv₀ : J₀ 0 1 ≠ 0 := by simp [J₀]

/-- The critical mode is `(-2, -3/4)` in mode `1`, computed from the definitions. -/
example : criticalMode J₀ (1 / 4) 4 κ₀ 1 = Pi.single 1 ![-2, -(3 / 4)] := by
  simp only [criticalMode, kerVec, modeMatrix, diffusionMatrix, J₀, κ₀]
  congr 1
  ext i; fin_cases i <;> norm_num

/-- The linearization kills the critical mode (direct computation, not through the kernel
theorem). -/
example : modeOperator J₀ (1 / 4) 4 κ₀ (Pi.single 1 ![-2, -(3 / 4)]) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mulVec, dotProduct, modeMatrix, diffusionMatrix, J₀, κ₀] <;> norm_num

/-- The kernel theorem: every kernel element is a multiple of the critical mode. -/
example (w : Fin 3 → Fin 2 → ℝ) (hw : modeOperator J₀ (1 / 4) 4 κ₀ w = 0) :
    ∃ a : ℝ, w = a • criticalMode J₀ (1 / 4) 4 κ₀ 1 :=
  (modeOperator_eq_zero_iff hcrit₀ hfv₀ hnr₀ w).1 hw

/-- A field excited in a stable mode is not in the kernel (direct computation). -/
example : modeOperator J₀ (1 / 4) 4 κ₀ (Pi.single 0 ![1, 0]) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [mulVec, dotProduct, modeMatrix, diffusionMatrix, J₀, κ₀] at this

/-- The critical functional `y ↦ m₁₁ y_{1,0} - m₀₁ y_{1,1}` with `m₁₁ = -8`, `m₀₁ = -2`, and a
vector outside the range. -/
example : criticalFunctional J₀ (1 / 4) 4 κ₀ 1 (Pi.single 1 ![1, 0]) = -8 := by
  simp [modeMatrix, diffusionMatrix, J₀, κ₀]
  norm_num

example : ¬ ∃ w, modeOperator J₀ (1 / 4) 4 κ₀ w = Pi.single 1 ![1, 0] := by
  rw [exists_modeOperator_eq_iff hcrit₀ hfv₀ hnr₀]
  simp [modeMatrix, diffusionMatrix, J₀, κ₀]
  norm_num

/-- The example has a Fredholm package, and every package satisfies the simple-kernel
hypotheses of the scalar reduction. -/
example : ∃ pkg : FredholmPackage (modeOperator J₀ (1 / 4) 4 κ₀),
    criticalMode J₀ (1 / 4) 4 κ₀ 1 ∈ pkg.decDom.X₀ ∧
      ∀ y ∈ pkg.decCodom.X₀, criticalFunctional J₀ (1 / 4) 4 κ₀ 1 y = 0 → y = 0 := by
  obtain ⟨pkg⟩ := isFredholm_modeOperator (J := J₀) (du := 1 / 4) (d := 4)
    (κ := κ₀) |>.nonempty_fredholmPackage
  obtain ⟨h1, -, -, h4⟩ := modeOperator_simpleKernel hcrit₀ hfv₀ hnr₀ pkg
  exact ⟨pkg, h1, h4⟩

/-- **Resonant boundary case.** With two equal critical wavenumbers `κ = (1, 1)` the critical mode
in slot `0` is in the kernel but is not a multiple of the critical mode in slot `1`: the kernel
is two-dimensional, so the non-resonance hypothesis is needed. -/
example : modeOperator J₀ (1 / 4) 4 ![1, 1] (criticalMode J₀ (1 / 4) 4 ![1, 1] 0) = 0 ∧
    ¬ ∃ a : ℝ, criticalMode J₀ (1 / 4) 4 ![1, 1] 0 = a • criticalMode J₀ (1 / 4) 4 ![1, 1] 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [criticalMode, kerVec, mulVec, dotProduct, modeMatrix, diffusionMatrix, J₀] <;>
      norm_num
  · rintro ⟨a, ha⟩
    have := congrFun (congrFun ha 0) 0
    simp [criticalMode, kerVec, J₀] at this

/-! ### Mode fields -/

/-- At `x = 0` a mode field is the sum of its coefficients (`cos 0 = 1`). -/
example (w : Fin 3 → Fin 2 → ℝ) : modeField κ₀ w 0 = ∑ i, w i := by
  simp [modeField]

/-- The bridge: `D u_xx + J u` of the critical-mode field vanishes, so the critical mode field is a
steady state of the linearized PDE. -/
example (x : ℝ) : diffusionMatrix (1 / 4) 4 *ᵥ
      deriv (deriv (modeField κ₀ (criticalMode J₀ (1 / 4) 4 κ₀ 1))) x +
    J₀ *ᵥ modeField κ₀ (criticalMode J₀ (1 / 4) 4 κ₀ 1) x = 0 := by
  rw [diffusion_mulVec_deriv_deriv_add,
    (modeOperator_eq_zero_iff hcrit₀ hfv₀ hnr₀ _).2 ⟨1, (one_smul _ _).symm⟩]
  simp [modeField]

/-- Zero flux at both ends of `[0, 1]` for the Neumann modes `n π`, `n = 0, 1, 2`. -/
example (w : Fin 3 → Fin 2 → ℝ) :
    deriv (modeField (fun i => neumannWavenumber 1 (![0, 1, 2] i)) w) 0 = 0 ∧
      deriv (modeField (fun i => neumannWavenumber 1 (![0, 1, 2] i)) w) 1 = 0 :=
  ⟨deriv_modeField_zero _ w, deriv_modeField_neumann one_ne_zero _ w⟩

/-! ### The full reduction on the pitchfork `F(x, d) = (d - d₀) x - x³`

Here `E = Y = ℝ`, `L = ∂ₓF(0, d₀) = 0`, `ker L = ℝ`, `range L = 0`. -/

section Pitchfork

variable (d₀ : ℝ)

/-- The pitchfork map. -/
def pitchfork (q : ℝ × ℝ) : ℝ := (q.2 - d₀) * q.1 - q.1 ^ 3

theorem isFredholm_zero : (0 : ℝ →L[ℝ] ℝ).IsFredholm :=
  ⟨(0 : ℝ →L[ℝ] ℝ).isStrictMap_of_finiteDimensional, Submodule.closed_of_finiteDimensional _,
    inferInstance, Submodule.CoFG.of_finite, Submodule.ClosedComplemented.of_finiteDimensional _⟩

/-- Its strict derivative at `(0, d₀)`: `(x, d) ↦ 0`. -/
theorem hasStrictFDerivAt_pitchfork :
    HasStrictFDerivAt (pitchfork d₀) (0 : ℝ × ℝ →L[ℝ] ℝ) ((0 : ℝ), d₀) := by
  have hfst := hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), d₀))
  have hsnd := hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), d₀))
  exact (((hsnd.sub_const d₀).mul hfst).sub (hfst.pow 3)).congr_fderiv (by ext <;> simp)

theorem hFL : (0 : ℝ × ℝ →L[ℝ] ℝ) ∘L .inl ℝ ℝ ℝ = 0 := by ext; simp

variable (pkg : FredholmPackage (0 : ℝ →L[ℝ] ℝ))

theorem X₀_eq_top : pkg.decDom.X₀ = ⊤ := by
  rw [← pkg.ker_eq]
  ext; simp

theorem coe_X₁_eq_zero (w : pkg.decDom.X₁) : (w : ℝ) = 0 := by
  have h : pkg.decDom.X₁ = ⊥ :=
    eq_bot_of_isCompl_top (X₀_eq_top pkg ▸ pkg.decDom.isTopCompl.isCompl)
  exact (Submodule.eq_bot_iff _).1 h w w.2

theorem one_mem : (1 : ℝ) ∈ pkg.decDom.X₀ := by rw [X₀_eq_top]; trivial

theorem hspan : ∀ z : pkg.decDom.X₀, ∃ a : ℝ, (z : ℝ) = a • (1 : ℝ) :=
  fun z => ⟨z, by simp⟩

theorem hψ1 : ∀ y ∈ pkg.decCodom.X₁, ContinuousLinearMap.id ℝ ℝ y = 0 := by
  intro y hy
  rw [← pkg.range_eq] at hy
  obtain ⟨x, rfl⟩ := hy
  simp

theorem hψ0 : ∀ y ∈ pkg.decCodom.X₀, ContinuousLinearMap.id ℝ ℝ y = 0 → y = 0 :=
  fun _ _ h => h

/-- **The scalar bifurcation function of the pitchfork is the pitchfork itself**, computed from
the definition of `lsScalar` (the solution operator lands in `X₁ = 0`). -/
theorem lsScalar_pitchfork (q : ℝ × ℝ) :
    lsScalar pkg (one_mem pkg) (ContinuousLinearMap.id ℝ ℝ) (hasStrictFDerivAt_pitchfork d₀)
      (hFL) q = (q.2 - d₀) * q.1 - q.1 ^ 3 := by
  simp [lsScalar, coe_X₁_eq_zero, pitchfork]

/-- The factor `G(a, d) = d - d₀ - a²` of `G̃ = a G`. -/
def pitchforkG (q : ℝ × ℝ) : ℝ := q.2 - d₀ - q.1 ^ 2

theorem hasStrictFDerivAt_pitchforkG :
    HasStrictFDerivAt (pitchforkG d₀) (ContinuousLinearMap.snd ℝ ℝ ℝ) ((0 : ℝ), d₀) := by
  have hfst := hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), d₀))
  have hsnd := hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := ((0 : ℝ), d₀))
  exact ((hsnd.sub_const d₀).sub (hfst.pow 2)).congr_fderiv (by ext <;> simp)

/-- The pattern branch `d = d₀ + a²` solves the pitchfork (direct computation). -/
example (a : ℝ) : pitchfork d₀ (a, d₀ + a ^ 2) = 0 := by
  simp [pitchfork]; ring

/-- **The full chain applies to the pitchfork**: every hypothesis of
`lyapunovSchmidt_patternBranch` except the reduced Crandall–Rabinowitz theorem `hCR` (T55's
`exists_patternBranch`, PR #1533) is discharged, and the branch slope is
`-∂_a G / ∂_d G = 0`. -/
example (hCR : ∀ {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ} {d₀ : ℝ},
      HasStrictFDerivAt G G' (0, d₀) → G (0, d₀) = 0 → G' (0, 1) ≠ 0 →
        ∃ φ : ℝ → ℝ, φ 0 = d₀ ∧ HasStrictDerivAt φ (-(G' (1, 0) / G' (0, 1))) 0 ∧
          ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1)) :
    ∃ β : ℝ → ℝ, β 0 = d₀ ∧ HasStrictDerivAt β 0 0 ∧
      ∀ᶠ q in 𝓝 ((0 : ℝ), d₀), (pitchfork d₀ q = 0 ↔ q.1 = 0 ∨ ∃ a : ℝ,
        q.1 = a • (1 : ℝ) + lsSolution pkg (hasStrictFDerivAt_pitchfork d₀) hFL
          (a • ⟨1, one_mem pkg⟩, q.2) ∧ q.2 = β a) := by
  obtain ⟨β, h0, hd, hz, -⟩ := lyapunovSchmidt_patternBranch pkg (hasStrictFDerivAt_pitchfork d₀)
    hFL (Eventually.of_forall fun d => by simp [pitchfork]) (one_mem pkg) one_ne_zero
    (hspan pkg) (ContinuousLinearMap.id ℝ ℝ) (hψ1 pkg) (hψ0 pkg) hCR
    (G := pitchforkG d₀)
    (Eventually.of_forall fun q => by rw [lsScalar_pitchfork, pitchforkG]; ring)
    (hasStrictFDerivAt_pitchforkG d₀) (by simp [pitchforkG]) (by simp)
  refine ⟨β, h0, by simpa using hd, hz⟩

/-- The unconditional scalar reduction on the pitchfork: near `(0, d₀)`, `F(x, d) = 0` iff the
scalar equation `(d - d₀) a - a³ = 0` holds at `a = x`. -/
example : ∀ᶠ q in 𝓝 ((0 : ℝ), d₀), pitchfork d₀ q = 0 ↔
    ∃ a : ℝ, q.1 = a • (1 : ℝ) + lsSolution pkg (hasStrictFDerivAt_pitchfork d₀) hFL
      (a • ⟨1, one_mem pkg⟩, q.2) ∧ (q.2 - d₀) * a - a ^ 3 = 0 := by
  filter_upwards [lyapunovSchmidt_scalar pkg (one_mem pkg) (hspan pkg) (ContinuousLinearMap.id ℝ ℝ)
    (hasStrictFDerivAt_pitchfork d₀) hFL (by simp [pitchfork]) (hψ1 pkg) (hψ0 pkg)] with q hq
  simpa [lsScalar_pitchfork] using hq

/-- The solution operator vanishes on the trivial branch and has zero kernel derivative. -/
example : ∀ᶠ d in 𝓝 d₀, lsSolution pkg (hasStrictFDerivAt_pitchfork d₀) hFL
    ((0 : pkg.decDom.X₀), d) = 0 :=
  (eventually_lsSolution_zero pkg (hasStrictFDerivAt_pitchfork d₀) hFL
    (Eventually.of_forall fun d => by simp [pitchfork])).mono fun _ h => h.1

/-- For `L = 0` on `ℝ` the kernel projection is the identity and the kernel coordinate of `x` is
`x` itself (`φ = 1`). -/
example (x : ℝ) : (kerProj pkg x : ℝ) = x ∧ kerCoord pkg (hspan pkg) x = x := by
  have hk : (kerProj pkg x : ℝ) = x := by
    have := kerProj_add_proj pkg x
    rwa [coe_X₁_eq_zero, add_zero] at this
  refine ⟨hk, ?_⟩
  have := coe_kerProj_eq_kerCoord_smul pkg (hspan pkg) x
  rw [hk, smul_eq_mul, mul_one] at this
  exact this.symm

/-- The range is `0`, so the cokernel projection is the identity. -/
example (y : ℝ) : (cokerProj pkg y : ℝ) = y := by
  have h := proj_add_cokerProj pkg y
  have hY : pkg.decCodom.X₁ = ⊥ := by
    rw [← pkg.range_eq]
    ext; simp
  have h0 : (pkg.decCodom.proj y : ℝ) = 0 :=
    (Submodule.eq_bot_iff _).1 hY _ (pkg.decCodom.proj y).2
  rwa [h0, zero_add] at h

/-- `lsSplit` and `lsEmbed` are mutually inverse on states: `(x, d) ↦ ((π₀ x, d), π₁ x) ↦ (x, d)`. -/
example (q : ℝ × ℝ) : lsEmbed pkg (lsSplit pkg q) = q := lsEmbed_lsSplit pkg q

/-- The reduced map of the pitchfork vanishes exactly at its zeros: `lsReduced = 0` at `(a, d)`
iff `(d - d₀) a - a³ = 0` (through `lsScalar_eq_zero_iff`, with `lsScalar` computed from the
definition). -/
example (a d : ℝ) :
    lsReduced pkg (hasStrictFDerivAt_pitchfork d₀) hFL (a • ⟨1, one_mem pkg⟩, d) = 0 ↔
      (d - d₀) * a - a ^ 3 = 0 := by
  rw [← lsScalar_eq_zero_iff pkg (one_mem pkg) (ContinuousLinearMap.id ℝ ℝ)
    (hasStrictFDerivAt_pitchfork d₀) hFL (hψ1 pkg) (hψ0 pkg) (a, d), lsScalar_pitchfork]

end Pitchfork

end MathlibExtTest.Biology.Dynamics.TuringBranchesPDE
