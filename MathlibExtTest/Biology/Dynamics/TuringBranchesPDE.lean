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

/-- The critical mode is nonzero (`f_v = -2 ≠ 0`). -/
example : criticalMode J₀ (1 / 4) 4 κ₀ 1 ≠ 0 := criticalMode_ne_zero hfv₀

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

/-- The example has a Fredholm package, and every package satisfies the kernel and range
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
`-∂_a G / ∂_d G = 0`. `hCR` is assumed in T55's universal form, which specializes to the
pitchfork's reduced map at the call site. -/
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

/-- `lsSplit` and `lsEmbed` are mutually inverse on states:
`(x, d) ↦ ((π₀ x, d), π₁ x) ↦ (x, d)`. -/
example (q : ℝ × ℝ) : lsEmbed pkg (lsSplit pkg q) = q := lsEmbed_lsSplit pkg q

/-- The range equation of the pitchfork is trivial: `range L = 0`, so `lsRangeMap` is `0`. -/
example (v : (pkg.decDom.X₀ × ℝ) × pkg.decDom.X₁) : lsRangeMap pkg (pitchfork d₀) v = 0 := by
  have hY : pkg.decCodom.X₁ = ⊥ := by
    rw [← pkg.range_eq]
    ext; simp
  exact Subtype.ext ((Submodule.eq_bot_iff _).1 hY _ (lsRangeMap pkg (pitchfork d₀) v).2)

/-- The reduced map of the pitchfork vanishes exactly at its zeros: `lsReduced = 0` at `(a, d)`
iff `(d - d₀) a - a³ = 0` (through `lsScalar_eq_zero_iff`, with `lsScalar` computed from the
definition). -/
example (a d : ℝ) :
    lsReduced pkg (hasStrictFDerivAt_pitchfork d₀) hFL (a • ⟨1, one_mem pkg⟩, d) = 0 ↔
      (d - d₀) * a - a ^ 3 = 0 := by
  rw [← lsScalar_eq_zero_iff pkg (one_mem pkg) (ContinuousLinearMap.id ℝ ℝ)
    (hasStrictFDerivAt_pitchfork d₀) hFL (hψ1 pkg) (hψ0 pkg) (a, d), lsScalar_pitchfork]

end Pitchfork

/-! ### A two-dimensional reduction with a nonzero solution operator

`F((u, v), d) = (u - v², (d - d₀) v - v³)` on `ℝ²`, with `L = ∂ₓF(0, d₀) = diag(1, 0)`. The
Fredholm package is built from the explicit complements `X₁ = ℝ × 0` and `Y₀ = 0 × ℝ`, so the
solution operator is forced by implicit-function uniqueness to be `W(a (0, 1), d) = (a², 0)`, and
the scalar bifurcation function is again the pitchfork `(d - d₀) a - a³`. -/

section TwoDim

variable (d₀ : ℝ)

/-- The two-dimensional map. -/
def F₂ (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (q.1.1 - q.1.2 ^ 2, (q.2 - d₀) * q.1.2 - q.1.2 ^ 3)

/-- `L = diag(1, 0)`: `(u, v) ↦ (u, 0)`. -/
noncomputable def L₂ : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The full derivative `(x, d) ↦ L x`. -/
noncomputable def F₂' : (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ := L₂ ∘L ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ

theorem hasStrictFDerivAt_F₂ : HasStrictFDerivAt (F₂ d₀) F₂' (((0 : ℝ), (0 : ℝ)), d₀) := by
  have hu := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (((0 : ℝ), (0 : ℝ)), d₀))).fst
  have hv := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (((0 : ℝ), (0 : ℝ)), d₀))).snd
  have hd := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (((0 : ℝ), (0 : ℝ)), d₀))
  exact ((hu.sub (hv.pow 2)).prodMk (((hd.sub_const d₀).mul hv).sub (hv.pow 3))).congr_fderiv
    (by ext <;> simp [F₂', L₂])

theorem hFL₂ : F₂' ∘L .inl ℝ (ℝ × ℝ) ℝ = L₂ := by ext <;> simp [F₂', L₂]

theorem ker_L₂ : (L₂ : ℝ × ℝ →L[ℝ] ℝ × ℝ).ker = LinearMap.range (LinearMap.inr ℝ ℝ ℝ) := by
  ext ⟨u, v⟩
  simp [L₂, Prod.ext_iff, eq_comm]

theorem range_L₂ : (L₂ : ℝ × ℝ →L[ℝ] ℝ × ℝ).range = LinearMap.range (LinearMap.inl ℝ ℝ ℝ) := by
  ext ⟨u, v⟩
  simp [L₂, Prod.ext_iff, eq_comm]

theorem isTopCompl_of_isCompl {p q : Submodule ℝ (ℝ × ℝ)} (h : IsCompl p q) :
    Submodule.IsTopCompl p q :=
  (Submodule.IsCompl.isTopCompl_iff h).2 (LinearMap.continuous_of_finiteDimensional _)

/-- The Fredholm package with `X₁ = ℝ × 0` and `Y₀ = 0 × ℝ`. -/
noncomputable def pkg₂ : FredholmPackage L₂ :=
  ContinuousLinearMap.IsFredholm.fredholmPackage
    ⟨L₂.isStrictMap_of_finiteDimensional, Submodule.closed_of_finiteDimensional _, inferInstance,
      Submodule.CoFG.of_finite, Submodule.ClosedComplemented.of_finiteDimensional _⟩
    (dom₁ := LinearMap.range (LinearMap.inl ℝ ℝ ℝ))
    (codom₀ := LinearMap.range (LinearMap.inr ℝ ℝ ℝ))
    (isTopCompl_of_isCompl (ker_L₂ ▸ LinearMap.isCompl_range_inl_inr.symm))
    (isTopCompl_of_isCompl (range_L₂ ▸ LinearMap.isCompl_range_inl_inr))

theorem φ₂_mem : ((0 : ℝ), (1 : ℝ)) ∈ pkg₂.decDom.X₀ := by
  change ((0 : ℝ), (1 : ℝ)) ∈ (L₂ : ℝ × ℝ →L[ℝ] ℝ × ℝ).ker
  rw [ker_L₂]
  exact ⟨1, rfl⟩

theorem hF₂0 : F₂ d₀ (((0 : ℝ), (0 : ℝ)), d₀) = 0 := by simp [F₂]

/-- **The solution operator is `W(a (0, 1), d) = (a², 0)`** near `(0, d₀)`: a nonzero `W`, pinned
down by the uniqueness clause of the implicit function theorem (`eventually_lsRangeMap_eq_zero_iff`)
and the explicit range equation `lsRangeMap` (its first component `u - v²`). -/
theorem eventually_lsSolution_F₂ : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀),
    (lsSolution pkg₂ (hasStrictFDerivAt_F₂ d₀) hFL₂ (p.1 • ⟨((0 : ℝ), (1 : ℝ)), φ₂_mem⟩, p.2) :
      ℝ × ℝ) = (p.1 ^ 2, 0) := by
  have hmem : ∀ a : ℝ, ((a ^ 2, (0 : ℝ)) : ℝ × ℝ) ∈ pkg₂.decDom.X₁ := fun a => ⟨a ^ 2, rfl⟩
  set v : ℝ × ℝ → (pkg₂.decDom.X₀ × ℝ) × pkg₂.decDom.X₁ := fun p =>
    ((p.1 • ⟨((0 : ℝ), (1 : ℝ)), φ₂_mem⟩, p.2), ⟨(p.1 ^ 2, 0), hmem p.1⟩) with hv
  have hcont : Continuous v :=
    ((continuous_fst.smul continuous_const).prodMk continuous_snd).prodMk
      (((continuous_fst.pow 2).prodMk continuous_const).subtype_mk _)
  have ht : Tendsto v (𝓝 ((0 : ℝ), d₀))
      (𝓝 (((0 : pkg₂.decDom.X₀), d₀), (0 : pkg₂.decDom.X₁))) := by
    have := hcont.tendsto ((0 : ℝ), d₀)
    have h0 : v ((0 : ℝ), d₀) = (((0 : pkg₂.decDom.X₀), d₀), (0 : pkg₂.decDom.X₁)) := by
      simp only [hv, zero_smul]
      congr 2
      ext <;> simp
    rwa [h0] at this
  filter_upwards [ht.eventually (eventually_lsRangeMap_eq_zero_iff pkg₂ (hasStrictFDerivAt_F₂ d₀)
    hFL₂ (hF₂0 d₀))] with p hp
  have hR : lsRangeMap pkg₂ (F₂ d₀) (v p) = 0 := by
    simp only [lsRangeMap, FredholmDecomposition.proj]
    rw [Submodule.projectionOntoL_apply_eq_zero_iff]
    refine ⟨(p.2 - d₀) * p.1 - p.1 ^ 3, ?_⟩
    simp [hv, F₂]
  exact congrArg Subtype.val (hp.1 hR)

/-- The scalar bifurcation function (`ψ = snd`) is the pitchfork `(d - d₀) a - a³` near `(0, d₀)`,
computed from `lsScalar` and the explicit `W`. -/
example : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀),
    lsScalar pkg₂ φ₂_mem (ContinuousLinearMap.snd ℝ ℝ ℝ) (hasStrictFDerivAt_F₂ d₀) hFL₂ p =
      (p.2 - d₀) * p.1 - p.1 ^ 3 := by
  filter_upwards [eventually_lsSolution_F₂ d₀] with p hp
  simp only [lsScalar, ContinuousLinearMap.coe_snd']
  rw [show (p.1 • ((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) +
      (lsSolution pkg₂ (hasStrictFDerivAt_F₂ d₀) hFL₂ (p.1 • ⟨((0 : ℝ), (1 : ℝ)), φ₂_mem⟩, p.2) :
        ℝ × ℝ) = (p.1 ^ 2, p.1) by rw [hp]; simp]
  simp [F₂]

end TwoDim

end MathlibExtTest.Biology.Dynamics.TuringBranchesPDE
