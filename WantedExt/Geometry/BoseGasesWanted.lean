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

/-- **The box $([0,L]^3)^N$.** For a natural number $N$ and a real number $L$, the box
$([0,L]^3)^N$ is the set of configurations $(x_1, \dots, x_N)$ of $N$ points of $\mathbb{R}^3$
such that every coordinate of every point $x_i$ lies in the closed interval $[0, L]$. -/
def box (N : ℕ) (L : ℝ) : Set (Fin N → ℝ³) := {x | ∀ i k, x i k ∈ Set.Icc 0 L}

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- We define the filter for the limit as `L → ∞` and `N / L^3 → ρ`. -/
noncomputable
def jointFilter (ρ : ℝ) : Filter (ℝ × ℕ) :=
  atTop.comap Prod.fst ⊓ (𝓝 ρ).comap fun (L, N) ↦ N / L ^ 3

/-- **Smooth functions supported inside the box.** For a natural number $N$ and a real number
$L$, $C_0^\infty(([0,L]^3)^N) \setminus \{0\}$ consists of the functions
$\Psi : (\mathbb{R}^3)^N \to \mathbb{R}$ that are smooth on the box $([0,L]^3)^N$, whose closed
support is contained in the interior of the box, and that are not identically zero.

The functions are defined on all of $(\mathbb{R}^3)^N$ rather than on the box only. -/
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

/-- **Radial functions.** A function $v : \mathbb{R}^3 \to \mathbb{R}$ is radial if
$v(x) = v(y)$ for all $x, y \in \mathbb{R}^3$ with $\|x\| = \|y\|$. -/
def IsRadial (v : ℝ³ → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → v x = v y

/-- **Scattering solutions.** Let $v, w : \mathbb{R}^3 \to \mathbb{R}$. The function $w$ is a
scattering solution for the potential $v$ if $w$ and $v\,(1 - w)$ are locally integrable,
$w(x) \to 0$ as $\|x\| \to \infty$, and $w$ solves the scattering equation
$-\Delta w = \frac{1}{2} v\,(1 - w)$ (Equation (3.4) of Fournais–Solovej) in the weak sense:
for every smooth, compactly supported $\varphi : \mathbb{R}^3 \to \mathbb{R}$,

$$-\int_{\mathbb{R}^3} w\,\Delta\varphi = \frac{1}{2} \int_{\mathbb{R}^3} v\,(1 - w)\,\varphi.$$
-/
structure IsScatteringSolution (w v : ℝ³ → ℝ) where
  lhs_integrable : LocallyIntegrable w
  rhs_integrable : LocallyIntegrable (v * (1 - w))
  eq : ∀ φ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ →
    - ∫ x, w x * (Δ φ) x = (1 / 2) * ∫ x, v x * (1 - w x) * φ x
  lim : Tendsto w (cocompact ℝ³) (𝓝 0)

open Classical in
/-- **Scattering length.** Let $v : \mathbb{R}^3 \to \mathbb{R}$ be a potential. If there is a
radial scattering solution $w$ to the scattering equation with potential $v$, the scattering
length of $v$ is $a(v) = (8\pi)^{-1} \int_{\mathbb{R}^3} v(x)\,(1 - w(x))\,dx$, where $w$ is
one such solution, chosen arbitrarily; if there is no radial scattering solution, $a(v) = 0$.

This is Equation (3.5) of Fournais–Solovej. Under the assumptions of Theorem 1.2 the radial
scattering solution exists and is unique, so the choice does not matter there. -/
noncomputable def a (v : ℝ³ → ℝ) : ℝ :=
  if w : ∃ w, IsRadial w ∧ IsScatteringSolution w v then
    (8 * π)⁻¹ * ∫ x, (v x * (1 - w.choose x))
  else
    0

/-- **The ratio $\mathcal{R}(v)$.** For a potential $v : \mathbb{R}^3 \to \mathbb{R}$ with
scattering length $a(v)$, let $\mathcal{R}(v) = \int_{\mathbb{R}^3} v(x)/(8\pi a(v))\,dx$. When
$a(v) \neq 0$ this is the ratio of $(8\pi)^{-1} \int v$ to $a(v)$. -/
noncomputable def 𝓡 (v : ℝ³ → ℝ) := ∫ x, v x / (8 * π * a v)

/- Constant `η` in Theorem 1.2. -/
/-- **Lee–Huang–Yang error exponent.** $\eta$ is a real constant, not given explicitly, that
serves as the exponent in the error term $(\rho a^3)^{1/2 + \eta}$ of the Lee–Huang–Yang lower
bound (Theorem 1.2), where $\rho$ is the density and $a$ the scattering length of the
potential; that theorem asserts $\eta > 0$.

Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`. -/
public def_wanted η : ℝ

/- Constant `𝓒` in Theorem 1.2. -/
/-- **Lee–Huang–Yang error constant.** $\mathcal{C}$ is a real-valued function of two real
variables, not given explicitly. Let $v$ be a potential with scattering length $a$ whose closed
support lies in the open ball $B(0, R)$, and let $\mathcal{R}(v) = \int v/(8\pi a)$. In the
Lee–Huang–Yang lower bound (Theorem 1.2) for $v$ at density $\rho$, the error term is
$\mathcal{C}(\mathcal{R}(v), R/a)\,(\rho a^3)^{1/2 + \eta}$, where $\eta$ is the Lee–Huang–Yang
error exponent, so its constant depends only on $\mathcal{R}(v)$ and $R/a$.

Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`. -/
public def_wanted 𝓒 (𝓡 : ℝ) (r : ℝ) : ℝ

/--
**Lee–Huang–Yang lower bound for dilute Bose gases.** There are a real number $\eta$ and a
function $\mathcal{C}$ of two real variables such that the following holds. Let
$v : \mathbb{R}^3 \to \mathbb{R}$ be a non-negative, radial, integrable potential that is not
almost everywhere zero, and let $R > 0$ be such that the closed support of $v$ lies in the open
ball $B(0, R)$. Let $a$ be the scattering length of $v$, let $\mathcal{R}(v) = \int v/(8\pi a)$,
and let $e(\rho, v)$ be the ground state energy density at density $\rho$: the limit, as
$L \to \infty$ and $N/L^3 \to \rho$, of $L^{-3}$ times the infimum, over
$\Psi \in C_0^\infty(([0,L]^3)^N) \setminus \{0\}$, of
$\langle \Psi, H_N \Psi \rangle / \|\Psi\|^2$, where the inner product and norm are those of
$L^2(([0,L]^3)^N)$ and, writing points of $(\mathbb{R}^3)^N$ as $(x_1, \dots, x_N)$ and
$\Delta_{x_i}$ for the Laplacian in the variable $x_i$,
$H_N = \sum_{i=1}^{N} -\Delta_{x_i} + \sum_{1 \le i < j \le N} v(x_i - x_j)$. Then
$\eta > 0$, and for all sufficiently small $\rho > 0$,

$$
e(\rho, v) \ge 4\pi\rho^2 a \left(1 + \frac{128}{15\sqrt{\pi}}\sqrt{\rho a^3} -
\mathcal{C}(\mathcal{R}(v), R/a)\,(\rho a^3)^{1/2 + \eta}\right).
$$

The source takes the limit $\rho a^3 \to 0^+$; for fixed $v$ this is the same as $\rho \to 0^+$.
Although the wording of Theorem 1.2 in the source suggests that $\eta$ may depend on
$\mathcal{R}(v)$ and $R/a$, Theorem 6.8 there shows that $\eta$ is a universal constant.

Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`.
-/
public theorem_wanted theorem_1_2 (v : ℝ³ → ℝ) (hv_ne_zero : ¬ v =ᵐ[volume] 0) (hv_nonneg : 0 ≤ v)
    (hv_radial : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball 0 R) : 0 < ❰η❱ ∧ ∀ᶠ ρ in 𝓝[>] 0,
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        ❰𝓒❱ (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + ❰η❱))

end BoseGases

end MathlibExt.Geometry.BoseGasesWanted
