/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The energy of dilute Bose gases

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Physics.BoseGases` — annals_bose_gases (manifest `manifests/problems/annals_bose_gases.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.BoseGasesWanted` namespace. Mathematical
statements are unchanged. Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Geometry.BoseGasesWanted
/-!
# Main Statement from The energy of dilute Bose gases

We formalise the statement of the main result from S. Fournais and J. P. Solovej,
`The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020.
-/

set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian

open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Given `Ψ : (ℝ³)ᴺ → ℝ` for `i : Fin N` we define `Δ[i] Ψ = ∂²Ψ/∂xᵢ² + ∂²Ψ/∂yᵢ² + ∂²Ψ/∂zᵢ²`. -/
noncomputable
def partialLaplacian {N : ℕ} (i : Fin N) (Ψ : (Fin N → ℝ³) → ℝ) (x : Fin N → ℝ³) : ℝ :=
  Δ (fun y ↦ Ψ (Function.update x i y)) (x i)

local notation "Δ[" i "]" => partialLaplacian i

/-- We define the Hamiltonian Operator on `N` bosons in three dimensions with potential
`v : ℝ³ → ℝ` by `𝓗 N v = (∑ i, - Δ[i]) + Σ i,j, i < j, v (xᵢ - xⱼ)`. -/
noncomputable
def 𝓗 (N : ℕ) (v : ℝ³ → ℝ) (Ψ : (Fin N → ℝ³) → ℝ) (x : Fin N → ℝ³) : ℝ :=
  (∑ i : Fin N, - Δ[i] Ψ x) + ∑ ⟨i, j⟩ ∈ {(i, j) : Fin N × Fin N | i < j}, v (x i - x j) * Ψ x

/-- We define the set `([0,L]³)ᴺ`. -/
def box (N : ℕ) (L : ℝ) : Set (Fin N → ℝ³) := {x | ∀ i k, x i k ∈ Set.Icc 0 L}

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- We define the filter for the limit as `L → ∞` and `N / L^3 → ρ`. -/
noncomputable
def jointFilter (ρ : ℝ) : Filter (ℝ × ℕ) :=
  atTop.comap Prod.fst ⊓ (𝓝 ρ).comap fun (L, N) ↦ N / L ^ 3

/-- We define `C₀^∞(([0,L]³)ᴺ)\{0}` to be the set of functions `Ψ : (ℝ³)ᴺ → ℝ` such that
`Ψ` is smooth on `([0,L]³)ᴺ`, the support of `Ψ` is contained in
the interior of `([0,L]³)ᴺ`, and `Ψ ≠ 0`. -/
structure CInfty0Box (N : ℕ) (L : ℝ) where
  /-- The underlying function `(ℝ³)ᴺ → ℝ`. Note that unlike the paper the domain of the
  function is `(ℝ³)ᴺ` rather than `[0,L]³ᴺ` since this makes it easier to state differentiability
  in Lean. -/
  toFun : (Fin N → ℝ³) → ℝ
  /-- If `Ψ : C₀^∞(([0,L]³)ᴺ)\{0}` then `Ψ` is smooth on `([0,L]³)ᴺ`. -/
  contDiff : ContDiffOn ℝ ∞ toFun (box N L)
  /-- If `Ψ : C₀^∞(([0,L]³)ᴺ)\{0}` then the support of `Ψ` is contained in the interior
  of `([0,L]³)ᴺ`. -/
  support : tsupport toFun ⊆ interior (box N L)
  /-- If `Ψ : C₀^∞(([0,L]³)ᴺ)\{0}` then `Ψ ≠ 0`. -/
  nezero : toFun ≠ 0

instance (N : ℕ) (L : ℝ) : CoeFun (CInfty0Box N L) (fun _ ↦ (Fin N → ℝ³) → ℝ) where
  coe Ψ := Ψ.toFun

/-- We define the thermodynamic limit of the ground state energy density by
`e ρ v = lim_{L → ∞, N/L³ → ρ} L⁻³ inf_{Ψ ∈ C₀^∞(([0,L]³)ᴺ)\{0}} ⟪Ψ, 𝓗 N v Ψ⟫ / ‖Ψ‖²`. -/
noncomputable
def e (ρ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  (jointFilter ρ).limUnder fun (L, N) ↦ L ^ (-3 : ℤ) *
    ⨅ Ψ : CInfty0Box N L, ⟪Ψ, 𝓗 N v Ψ⟫_[N,L] / ‖Ψ‖_[N,L] ^ 2

/-- We say that a function `v : ℝ³ → ℝ` is radial if for all `x,y ∈ ℝ³`, `‖x‖ = ‖y‖`
implies `v x = v y`. -/
def IsRadial (v : ℝ³ → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → v x = v y

/-- We say that `w : ℝ³ → ℝ` is a scattering solution to the scattering equation with potential
`v` if `w` is locally integrable, `w x → 0` as `|x| → ∞`, and `w` satisfies the equation:

`- Δ w = 1/2 v (1 - w)` (Equation (3.4) in the paper)

in the weak sense that `w, v(1 - w) ∈ L¹_loc (ℝ³)` and for any `φ ∈ C∞c(ℝ³)`

`- ∫ w * (Δ φ) = (1 / 2) * ∫ v * (1 - w) * φ`. -/
structure IsScatteringSolution (w v : ℝ³ → ℝ) where
  lhs_integrable : LocallyIntegrable w
  rhs_integrable : LocallyIntegrable (v * (1 - w))
  eq : ∀ φ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ →
    - ∫ x, w x * (Δ φ) x = (1 / 2) * ∫ x, v x * (1 - w x) * φ x
  lim : Tendsto w (cocompact ℝ³) (𝓝 0)

open Classical in
/-- When the potential `v : ℝ³ → ℝ` has a radial scattering solution `w : ℝ³ → ℝ`, we define
the scattering length `a` of `v` (using Equation (3.5)) by

`a = (8 π)⁻¹ ∫ v * (1 - w)`.

Under the assumptions of theorem 1.2 we know that `v` has a unique radial scattering solution,
and hence a well-defined scattering length `a`. -/
noncomputable def a (v : ℝ³ → ℝ) : ℝ :=
  if w : ∃ w, IsRadial w ∧ IsScatteringSolution w v then
    (8 * π)⁻¹ * ∫ x, (v x * (1 - w.choose x))
  else
    0

/-- We define `𝓡 v = ∫ x, v x / (8 * π * a v)`. -/
noncomputable def 𝓡 (v : ℝ³ → ℝ) := ∫ x, v x / (8 * π * a v)

/- Constant `η` in Theorem 1.2. -/
/-- Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`. -/
public def_wanted η : ℝ

/- Constant `𝓒` in Theorem 1.2. -/
/-- Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`. -/
public def_wanted 𝓒 (𝓡 : ℝ) (r : ℝ) : ℝ

/--
Statement of Theorem 1.2 (The Lee-Huang-Yang Formula):

For any non-zero, non-negative, radial potential `v ∈ L¹(ℝ³)` with compact support contained
in some ball `B(0,R)`, there exists `η > 0` and `𝓒` (depending only on `𝓡`and `R / a`) such that
as `ρ → 0⁺`,

`e ρ v ≥ 4πρ²a(1 + 128/(15√π)√(ρa³) - 𝓒(ρa³)^{1/2 + η})`.

Note: We (equivalently) take the limit as `ρ → 0⁺` rather than `ρa³ → 0⁺` as in the paper.

Note: While the wording of Theorem 1.2 in the paper suggests that `η` should also be allowed to
depend on `𝓡` and `R / a`, Theorem 6.8 makes it clear that `η` is in fact a universal constant.

Note: Since `v` is in `L¹(ℝ³)`, we interpret `v ≠ 0` to mean that `v` is not zero in `L¹(ℝ³)`.
Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`.
-/
public theorem_wanted theorem_1_2 (v : ℝ³ → ℝ) (hv_ne_zero : ¬ v =ᵐ[volume] 0) (hv_nonneg : 0 ≤ v)
    (hv_radial : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball 0 R) : 0 < ❰η❱ ∧ ∀ᶠ ρ in 𝓝[>] 0,
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        ❰𝓒❱ (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + ❰η❱))

end BoseGases

end MathlibExt.Geometry.BoseGasesWanted
