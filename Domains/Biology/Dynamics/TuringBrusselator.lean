/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.TuringBranchApplication
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Turing pattern branches of the Brusselator

The Brusselator of Prigogine and Lefever is the reaction scheme `A → X`, `B + X → Y + D`,
`2X + Y → 3X`, `X → E`; with the pool concentrations `a, b > 0` held fixed, the activator `u = [X]`
and the inhibitor `v = [Y]` obey the kinetics

`f(u, v) = a - (b + 1) u + u² v`, `g(u, v) = b u - u² v`.

Its only homogeneous steady state is `(a, b / a)`, with Jacobian `J = [[b - 1, a²], [-b, -a²]]`,
`tr J = b - 1 - a²` and `det J = a²`. This file applies the general Turing branch results of
`TuringBranches` and `TuringBranchApplication` to this concrete system: every hypothesis there
that is a property of `J` alone is discharged from the Brusselator parameters.

## Main results

* `brusselator_steadyState`, `jacobianMatrix_brusselator`: `(a, b / a)` is a steady state and (for
  `a ≠ 0`) the Jacobian of the kinetics there is `brusselatorJacobian a b`.
* `neutralDiffusion_brusselatorJacobian`: the neutral inhibitor diffusion of squared wavenumber
  `q` is `a² (1 + d_u q) / ((b - 1) q - d_u q²)`.
* `brusselator_turing_iff`: with `d_u = 1`, `d_v = d > 0` and `b < 1 + a²` (stable without
  diffusion), some Fourier mode is unstable iff `2 a √d < d (b - 1) - a²`, the classical threshold
  `b > (1 + a / √d)²`.
* `brusselator_patternBranch_of_reduction`: for `a ≠ 0`, `b < 1 + a²`, `d_u ≥ 0`, an admissible
  critical mode (`0 < (b - 1) k² - d_u k⁴`) at its neutral diffusion `d₀`, no other critical mode,
  and a steady-state map `F` on Neumann-mode coefficients whose linearization along the trivial
  branch is the Brusselator linearization: `∂_d G(0, d₀)` is the explicit crossing speed
  `(d_u k⁴ - (b - 1) k²) / (b - 1 - a² - k² (d_u + d₀))`, which is positive; `G(0, d)` has the sign
  of the critical eigenvalue near `d₀`; and `F` has a pattern branch through `(0, d₀)` whose states
  are nonzero steady states.

## Source receipt

* **Brusselator**: I. Prigogine and R. Lefever, *Symmetry breaking instabilities in dissipative
  systems. II*, J. Chem. Phys. 48 (1968) 1695–1700; G. Nicolis and I. Prigogine,
  *Self-Organization in Nonequilibrium Systems*, Wiley (1977), ch. 7. Proved here: the steady
  state, the Jacobian, the neutral diffusion and the Turing threshold.
* **Turing criterion and transversal crossing**: A. M. Turing, *The chemical basis of
  morphogenesis*, Phil. Trans. R. Soc. Lond. B 237 (1952) 37–72; J. D. Murray, *Mathematical
  Biology II*, 3rd ed., Springer (2003), ch. 2. Reused: `exists_isUnstableMode_iff`.
* **Pattern branch**: M. G. Crandall and P. H. Rabinowitz, *Bifurcation from simple eigenvalues*,
  J. Funct. Anal. 8 (1971) 321–340. Reused: `turing_patternBranch_of_reduction`.

## Scope

As in `TuringBranchApplication`, the map `F` on Neumann-mode coefficients is a hypothesis: no
Galerkin projection of the Brusselator nonlinearity is constructed, and the factorization of the
scalar bifurcation function is assumed. The link to the Brusselator is that the linearization of
`F` along the trivial branch is `D(d) ∂ₓₓ + J` with `J` the Brusselator Jacobian, which is the
Jacobian of the kinetics at the steady state (`jacobianMatrix_brusselator`). Only the selected mode
is controlled, so nothing is claimed about the stability of the branch.
-/

@[expose] public section

open Filter Topology
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExt.Biology.Dynamics.TuringBrusselator

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches
  MathlibExt.Biology.Dynamics.TuringBranchesPDE MathlibExt.Biology.Dynamics.TuringBranchApplication

/-! ### Kinetics, steady state and Jacobian -/

/-- The Brusselator kinetics `(f, g) = (a - (b + 1) u + u² v, b u - u² v)` on `x = (u, v)`, with
pool concentrations `a, b` (biologically `a, b > 0`). -/
def brusselator (a b : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a - (b + 1) * x 0 + x 0 ^ 2 * x 1, b * x 0 - x 0 ^ 2 * x 1]

/-- The homogeneous steady state `(a, b / a)` of the Brusselator (meaningful for `a ≠ 0`; at
`a = 0` the division gives the junk `v₀ = 0`). -/
noncomputable def brusselatorSteadyState (a b : ℝ) : Fin 2 → ℝ :=
  ![a, b / a]

/-- The matrix `[[b - 1, a²], [-b, -a²]]`, defined for all real `a`, `b`: for `a ≠ 0` it is the
Jacobian of the Brusselator kinetics at its steady state (`jacobianMatrix_brusselator`). -/
def brusselatorJacobian (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b - 1, a ^ 2; -b, -a ^ 2]

@[simp]
theorem brusselatorJacobian_zero_zero (a b : ℝ) : brusselatorJacobian a b 0 0 = b - 1 := rfl

@[simp]
theorem brusselatorJacobian_zero_one (a b : ℝ) : brusselatorJacobian a b 0 1 = a ^ 2 := rfl

@[simp]
theorem brusselatorJacobian_one_zero (a b : ℝ) : brusselatorJacobian a b 1 0 = -b := rfl

@[simp]
theorem brusselatorJacobian_one_one (a b : ℝ) : brusselatorJacobian a b 1 1 = -a ^ 2 := rfl

/-- `(a, b / a)` is a steady state of the Brusselator. (At `a = 0` the junk point `(0, 0)` is
also a zero of the kinetics, so no hypothesis is needed.) -/
theorem brusselator_steadyState (a b : ℝ) :
    brusselator a b (brusselatorSteadyState a b) = 0 := by
  funext i
  fin_cases i <;> simp [brusselator, brusselatorSteadyState] <;> field_simp <;> ring

/-- For `a ≠ 0`, the Jacobian matrix of the Brusselator kinetics at the steady state is
`brusselatorJacobian a b`. (At `a = 0` the steady state is `(0, 0)`, where `f_u = -(b + 1)`.) -/
theorem jacobianMatrix_brusselator {a b : ℝ} (ha : a ≠ 0) :
    MetaMathlibExt.jacobianMatrix (brusselator a b) (brusselatorSteadyState a b) =
      brusselatorJacobian a b := by
  have hu : HasDerivAt (fun t : ℝ => a + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add a
  have hv : HasDerivAt (fun t : ℝ => b / a + t) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add _
  have e00 : MetaMathlibExt.jacobianMatrix (brusselator a b) (brusselatorSteadyState a b) 0 0 =
      b - 1 := by
    rw [MetaMathlibExt.jacobianMatrix_apply]
    have hf : (fun t : ℝ => brusselator a b
        (brusselatorSteadyState a b + t • Pi.single 0 (1 : ℝ)) 0) =
        fun t => a - (b + 1) * (a + t) + (a + t) ^ 2 * (b / a) := by
      funext t
      simp [brusselator, brusselatorSteadyState]
    rw [hf, (((hu.const_mul (b + 1)).const_sub a).fun_add
      ((hu.fun_pow 2).mul_const (b / a))).deriv]
    field_simp
    ring
  have e01 : MetaMathlibExt.jacobianMatrix (brusselator a b) (brusselatorSteadyState a b) 0 1 =
      a ^ 2 := by
    rw [MetaMathlibExt.jacobianMatrix_apply]
    have hf : (fun t : ℝ => brusselator a b
        (brusselatorSteadyState a b + t • Pi.single 1 (1 : ℝ)) 0) =
        fun t => a - (b + 1) * a + a ^ 2 * (b / a + t) := by
      funext t
      simp [brusselator, brusselatorSteadyState]
    rw [hf, ((hv.const_mul (a ^ 2)).const_add (a - (b + 1) * a)).deriv]
    ring
  have e10 : MetaMathlibExt.jacobianMatrix (brusselator a b) (brusselatorSteadyState a b) 1 0 =
      -b := by
    rw [MetaMathlibExt.jacobianMatrix_apply]
    have hf : (fun t : ℝ => brusselator a b
        (brusselatorSteadyState a b + t • Pi.single 0 (1 : ℝ)) 1) =
        fun t => b * (a + t) - (a + t) ^ 2 * (b / a) := by
      funext t
      simp [brusselator, brusselatorSteadyState]
    rw [hf, ((hu.const_mul b).fun_sub ((hu.fun_pow 2).mul_const (b / a))).deriv]
    field_simp
    ring
  have e11 : MetaMathlibExt.jacobianMatrix (brusselator a b) (brusselatorSteadyState a b) 1 1 =
      -a ^ 2 := by
    rw [MetaMathlibExt.jacobianMatrix_apply]
    have hf : (fun t : ℝ => brusselator a b
        (brusselatorSteadyState a b + t • Pi.single 1 (1 : ℝ)) 1) =
        fun t => b * a - a ^ 2 * (b / a + t) := by
      funext t
      simp [brusselator, brusselatorSteadyState]
    rw [hf, ((hv.const_mul (a ^ 2)).const_sub (b * a)).deriv]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

/-- `tr J = b - 1 - a²`. -/
theorem trace_brusselatorJacobian (a b : ℝ) :
    (brusselatorJacobian a b).trace = b - 1 - a ^ 2 := by
  rw [Matrix.trace_fin_two, brusselatorJacobian_zero_zero, brusselatorJacobian_one_one]
  ring

/-- `det J = a²`. -/
theorem det_brusselatorJacobian (a b : ℝ) : (brusselatorJacobian a b).det = a ^ 2 := by
  rw [Matrix.det_fin_two, brusselatorJacobian_zero_zero, brusselatorJacobian_zero_one,
    brusselatorJacobian_one_zero, brusselatorJacobian_one_one]
  ring

/-! ### Turing instability of the Brusselator -/

/-- **Turing threshold of the Brusselator** (Prigogine–Lefever 1968). With `d_u = 1`,
`d_v = d > 0`, `0 < a` and `b < 1 + a²` (stable without diffusion), some Fourier mode is unstable
iff `2 a √d < d (b - 1) - a²`, i.e. `b > (1 + a / √d)²`. -/
theorem brusselator_turing_iff {a b d : ℝ} (ha : 0 < a) (hb : b < 1 + a ^ 2) (hd : 0 < d) :
    (∃ k, IsUnstableMode (brusselatorJacobian a b) 1 d k) ↔
      2 * a * Real.sqrt d < d * (b - 1) - a ^ 2 := by
  have htr : (brusselatorJacobian a b).trace < 0 := by
    rw [trace_brusselatorJacobian]
    linarith
  have hdet : 0 < (brusselatorJacobian a b).det := by
    rw [det_brusselatorJacobian]
    positivity
  have hs : Real.sqrt (1 * d * (brusselatorJacobian a b).det) = a * Real.sqrt d := by
    rw [det_brusselatorJacobian, show (1 : ℝ) * d * a ^ 2 = (a * Real.sqrt d) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hd.le]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [exists_isUnstableMode_iff one_pos hd htr hdet, hs, brusselatorJacobian_zero_zero,
    brusselatorJacobian_one_one]
  constructor <;> intro h <;> linarith

/-! ### Neutral diffusion and the pattern branch -/

/-- The neutral inhibitor diffusion `a² (1 + d_u q) / ((b - 1) q - d_u q²)` of squared
wavenumber `q` for the Brusselator, with `x / 0 = 0`: it is `0` where `(b - 1) q - d_u q² = 0`,
for example at `q = 0`. -/
noncomputable def brusselatorNeutralDiffusion (a b du q : ℝ) : ℝ :=
  a ^ 2 * (1 + du * q) / ((b - 1) * q - du * q ^ 2)

/-- The general neutral diffusion of the Brusselator Jacobian is
`brusselatorNeutralDiffusion`, for all real inputs (both quotients use `x / 0 = 0` and have the
same denominator). -/
theorem neutralDiffusion_brusselatorJacobian (a b du q : ℝ) :
    neutralDiffusion (brusselatorJacobian a b) du q = brusselatorNeutralDiffusion a b du q := by
  rw [neutralDiffusion, det_brusselatorJacobian, brusselatorJacobian_one_one,
    brusselatorJacobian_zero_zero, brusselatorNeutralDiffusion]
  ring

/-- For `0 < q`, the squared wavenumber `q` is admissible, `0 < (b - 1) q - d_u q²`, iff
`d_u q < b - 1`. -/
theorem brusselator_admissible_iff {b du q : ℝ} (hq : 0 < q) :
    0 < (b - 1) * q - du * q ^ 2 ↔ du * q < b - 1 := by
  rw [show (b - 1) * q - du * q ^ 2 = q * (b - 1 - du * q) by ring, mul_pos_iff_of_pos_left hq,
    sub_pos]

/-- At an admissible squared wavenumber `q ≥ 0` the neutral diffusion is positive (`a ≠ 0`,
`d_u ≥ 0`). -/
theorem brusselatorNeutralDiffusion_pos {a b du q : ℝ} (ha : a ≠ 0) (hdu : 0 ≤ du)
    (hq : 0 ≤ q) (hk : 0 < (b - 1) * q - du * q ^ 2) :
    0 < brusselatorNeutralDiffusion a b du q := by
  have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (pow_ne_zero 2 ha).symm
  exact div_pos (mul_pos ha2 (by nlinarith)) hk

/-- With `a ≠ 0`, `b < 1 + a²` and `d_u ≥ 0`, the mode matrix at the neutral diffusion of an
admissible wavenumber has negative trace. -/
theorem trace_modeMatrix_brusselator_neg {a b du k : ℝ} (ha : a ≠ 0) (hb : b < 1 + a ^ 2)
    (hdu : 0 ≤ du) (hk : 0 < (b - 1) * k ^ 2 - du * (k ^ 2) ^ 2) :
    (brusselatorJacobian a b).trace -
      k ^ 2 * (du + brusselatorNeutralDiffusion a b du (k ^ 2)) < 0 := by
  have hd := brusselatorNeutralDiffusion_pos ha hdu (sq_nonneg k) hk
  have h : 0 ≤ k ^ 2 * (du + brusselatorNeutralDiffusion a b du (k ^ 2)) :=
    mul_nonneg (sq_nonneg k) (by linarith)
  rw [trace_brusselatorJacobian]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Turing pattern branch of the Brusselator.** Let `a ≠ 0` and `b < 1 + a²` (the steady state
`(a, b / a)` is stable without diffusion), `d_u ≥ 0`, and let mode `i₀`, with wavenumber
`k = κ i₀`, be admissible, `0 < (b - 1) k² - d_u k⁴`, with neutral inhibitor diffusion
`d₀ = a² (1 + d_u k²) / ((b - 1) k² - d_u k⁴)`, and no other mode critical at `d₀`. Let `F(w, d)`
be a map on Neumann-mode coefficients with the trivial branch `F(0, d) = 0` for `d` near `d₀`,
strictly differentiable at `(0, d₀)` with state derivative there the linearization at `d₀`,
whose linearization along the trivial branch is the Brusselator linearization `D(d) ∂ₓₓ + J` for
every `d` near `d₀`. Fix a Fredholm package of the linearization at `d₀` whose kernel part
contains the critical mode `φ`, and let `G` be a factor, strictly differentiable at `(0, d₀)`, of
the scalar bifurcation function for the critical mode and the normalized critical functional.
Then

* `∂_d G(0, d₀) = (d_u k⁴ - (b - 1) k²) / (b - 1 - a² - k² (d_u + d₀))`, and it is positive;
* near `d₀`, `G(0, d)` has the sign of the critical eigenvalue of `J - k² D(d)`;
* there is a branch `d = β(s)` through `β 0 = d₀`, with slope `-∂_s G / ∂_d G` at `0`, such that
  near `(0, d₀)` the zeros of `F` are exactly the trivial ones and the branch
  `w = s φ + W(s φ, d)`, `d = β(s)`;
* for small `s ≠ 0` the branch state is a **nonzero** steady state at `d = β(s)` (a pattern);
* `G(0, d)` is negative for `d < d₀` and positive for `d > d₀` near `d₀`. -/
theorem brusselator_patternBranch_of_reduction {a b du d₀ : ℝ} {κ : ι → ℝ} {i₀ : ι}
    (ha : a ≠ 0) (hb : b < 1 + a ^ 2) (hdu : 0 ≤ du)
    (hk : 0 < (b - 1) * κ i₀ ^ 2 - du * (κ i₀ ^ 2) ^ 2)
    (hd₀ : d₀ = brusselatorNeutralDiffusion a b du (κ i₀ ^ 2))
    (hnr : ∀ i, i ≠ i₀ → (modeMatrix (brusselatorJacobian a b) du d₀ (κ i)).det ≠ 0)
    (pkg : FredholmPackage (modeOperator (brusselatorJacobian a b) du d₀ κ))
    (hφ : criticalMode (brusselatorJacobian a b) du d₀ κ i₀ ∈ pkg.decDom.X₀)
    {F : (ι → Fin 2 → ℝ) × ℝ → ι → Fin 2 → ℝ}
    {F' : (ι → Fin 2 → ℝ) × ℝ →L[ℝ] ι → Fin 2 → ℝ}
    (hF : HasStrictFDerivAt F F' ((0 : ι → Fin 2 → ℝ), d₀))
    (hFL : F' ∘L .inl ℝ (ι → Fin 2 → ℝ) ℝ = modeOperator (brusselatorJacobian a b) du d₀ κ)
    (htriv : ∀ᶠ d in 𝓝 d₀, F (0, d) = 0)
    (hlin : ∀ᶠ d in 𝓝 d₀,
      HasFDerivAt (fun w => F (w, d)) (modeOperator (brusselatorJacobian a b) du d κ) 0)
    {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hfac : ∀ᶠ q in 𝓝 ((0 : ℝ), d₀),
      lsScalar pkg hφ (normalizedCriticalFunctional (brusselatorJacobian a b) du d₀ κ i₀) hF hFL
        q = q.1 * G q)
    (hG : HasStrictFDerivAt G G' (0, d₀)) :
    G' (0, 1) = (du * (κ i₀ ^ 2) ^ 2 - (b - 1) * κ i₀ ^ 2) /
        (b - 1 - a ^ 2 - κ i₀ ^ 2 * (du + d₀)) ∧
      0 < G' (0, 1) ∧
      (∀ᶠ d in 𝓝 d₀, SignType.sign (G (0, d)) =
        SignType.sign (leadingEigenvalue (modeMatrix (brusselatorJacobian a b) du d (κ i₀)))) ∧
      ∃ β : ℝ → ℝ, β 0 = d₀ ∧ HasStrictDerivAt β (-(G' (1, 0) / G' (0, 1))) 0 ∧
        (∀ᶠ q in 𝓝 ((0 : ι → Fin 2 → ℝ), d₀), (F q = 0 ↔ q.1 = 0 ∨
          ∃ s : ℝ, q.1 = s • criticalMode (brusselatorJacobian a b) du d₀ κ i₀ +
            lsSolution pkg hF hFL (s • ⟨_, hφ⟩, q.2) ∧ q.2 = β s)) ∧
        (∀ᶠ s in 𝓝[≠] (0 : ℝ),
          F (s • criticalMode (brusselatorJacobian a b) du d₀ κ i₀ +
              lsSolution pkg hF hFL (s • ⟨_, hφ⟩, β s), β s) = 0 ∧
            s • criticalMode (brusselatorJacobian a b) du d₀ κ i₀ +
              lsSolution pkg hF hFL (s • ⟨_, hφ⟩, β s) ≠ 0) ∧
        (∀ᶠ d in 𝓝[<] d₀, G (0, d) < 0) ∧ ∀ᶠ d in 𝓝[>] d₀, 0 < G (0, d) := by
  have hk' : 0 < brusselatorJacobian a b 0 0 * κ i₀ ^ 2 - du * (κ i₀ ^ 2) ^ 2 := by
    rwa [brusselatorJacobian_zero_zero]
  have htr : (brusselatorJacobian a b).trace - κ i₀ ^ 2 * (du + d₀) < 0 := by
    rw [hd₀]
    exact trace_modeMatrix_brusselator_neg ha hb hdu hk
  have hd₀' : d₀ = neutralDiffusion (brusselatorJacobian a b) du (κ i₀ ^ 2) := by
    rw [neutralDiffusion_brusselatorJacobian, hd₀]
  have hfv : brusselatorJacobian a b 0 1 ≠ 0 := by
    rw [brusselatorJacobian_zero_one]
    exact pow_ne_zero 2 ha
  obtain ⟨hσ, hrest⟩ :=
    turing_patternBranch_of_reduction htr hk' hd₀' hfv hnr pkg hφ hF hFL htriv hlin hfac hG
  refine ⟨?_, hrest⟩
  rw [hσ, brusselatorJacobian_zero_zero, trace_brusselatorJacobian]

end MathlibExt.Biology.Dynamics.TuringBrusselator
