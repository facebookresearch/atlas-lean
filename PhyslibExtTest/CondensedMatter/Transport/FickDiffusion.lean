/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Transport.FickDiffusion
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!

# Tests for continuum diffusion in one dimension

Concrete instances of the definitions and results of
`PhyslibExt.CondensedMatter.Transport.FickDiffusion`, in the order of its sections, the documented
values outside the physical domain, and the axioms used by every public declaration.

-/

@[expose] public section

open MeasureTheory Set Filter Topology CondensedMatter.Diffusion

namespace PhyslibExtTest.CondensedMatter.Diffusion

/-!

## A. Fick's first law and the diffusion equation

-/

/-- The Fick flux of `c(x, t) = x² + 2Dt` is `-2Dx`. -/
example (D x t : ℝ) : fickFlux D (fun x t => x ^ 2 + 2 * D * t) x t = -2 * D * x := by
  have h : deriv (fun x' => x' ^ 2 + 2 * D * t) x = 2 * x := by
    simp
  simp only [fickFlux, h]
  ring

/-- `c(x, t) = x² + 2Dt` satisfies the continuity equation with its Fick flux, so
`fick_continuity_imply_diffusion` gives `∂ₜc = D ∂ₓₓc = 2D`. -/
example (D x t : ℝ) : deriv (fun t' => x ^ 2 + 2 * D * t') t = D * 2 := by
  have hd : ∀ y, deriv (fun x' => x' ^ 2 + 2 * D * t) y = 2 * y := fun y => by
    simp
  have hflux : (fun x' => fickFlux D (fun x t => x ^ 2 + 2 * D * t) x' t)
      = fun x' => -D * (2 * x') := funext fun y => by simp only [fickFlux, hd]
  refine fick_continuity_imply_diffusion D (fun x t => x ^ 2 + 2 * D * t) x t 2 (2 * D) ?_ ?_ ?_
  · simp only [hd]
    simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
  · simpa using ((hasDerivAt_id' t).const_mul (2 * D)).const_add (x ^ 2)
  · rw [hflux, ((hasDerivAt_id' x).const_mul 2).const_mul (-D) |>.deriv]
    ring

/-!

## B. The Gaussian on the line

-/

/-- The Gaussian with `M = 1`, `D = 1` solves the diffusion equation at `(x, t) = (0, 1)`. -/
example : deriv (fun t => gauss 1 1 0 t) 1
    = 1 * deriv (fun x => deriv (fun x' => gauss 1 1 x' 1) x) 0 :=
  gauss_pde 1 1 0 1 (by norm_num) (by norm_num)

/-- At `(0, 1)` both sides of the diffusion equation for `gauss 1 1` equal
`-(1 / √(4π)) / 2`. -/
example : deriv (fun t => gauss 1 1 0 t) 1 = -(1 / Real.sqrt (4 * Real.pi)) / 2
    ∧ 1 * deriv (fun x => deriv (fun x' => gauss 1 1 x' 1) x) 0
      = -(1 / Real.sqrt (4 * Real.pi)) / 2 := by
  have ht := (gauss_tderiv_value 1 1 0 1 (by norm_num) (by norm_num)).deriv
  have hxx := (gauss_xxderiv_value 1 1 0 1 (by norm_num) (by norm_num)).deriv
  have hg : gauss 1 1 0 1 = 1 / Real.sqrt (4 * Real.pi) := by
    simp only [gauss]
    have he : (-(0 : ℝ) ^ 2 / (4 * 1 * 1)) = 0 := by norm_num
    rw [he, Real.exp_zero, mul_one]
    congr 1
    congr 1
    ring
  constructor
  · rw [ht, hg]
    ring
  · rw [hxx, hg]
    ring

/-- Total mass `2` at time `3` for `D = 1`. -/
example : ∫ x, gauss 2 1 x 3 = 2 :=
  gauss_mass 2 1 3 (by norm_num) (by norm_num)

/-- `gauss_mass` holds for every real `M`, including a negative one. -/
example : ∫ x, gauss (-1) 1 x 1 = -1 :=
  gauss_mass (-1) 1 1 (by norm_num) (by norm_num)

/-- The Gaussian is nonnegative for a positive mass. -/
example (x : ℝ) : 0 ≤ gauss 2 1 x 3 :=
  gauss_nonneg 2 1 x 3 (by norm_num) (by norm_num) (by norm_num)

/-- Outside the physical domain: for `D > 0` and `t = 0` the Gaussian is `0`. -/
example (M x : ℝ) : gauss M 1 x 0 = 0 := by
  simp [gauss]

/-- The initial limit against the bounded continuous test function `cos`:
`∫ gauss 1 1 x t · cos x dx → cos 0 = 1` as `t → 0⁺`. -/
example : Tendsto (fun t => ∫ x, gauss 1 1 x t * Real.cos x) (𝓝[>] 0) (𝓝 1) := by
  simpa using gauss_weak_limit 1 1 one_pos one_pos Real.cos Real.continuous_cos
    ⟨1, Real.abs_cos_le_one⟩

/-!

## C. The complementary error function profile

-/

/-- The profile with `cs = 2`, `D = 1` solves the diffusion equation at `(x, t) = (1, 1)`. -/
example : deriv (fun t => erfcProfile 2 1 1 t) 1
    = 1 * deriv (fun x => deriv (fun x' => erfcProfile 2 1 x' 1) x) 1 :=
  erfcProfile_pde 2 1 1 1 (by norm_num) (by norm_num)

/-- The surface value at concrete numbers. -/
example : erfcProfile 2 1 0 1 = 2 :=
  erfcProfile_surface 2 1 1 (by norm_num) (by norm_num)

/-- The interior value at depth `1` is below the surface value. -/
example : erfcProfile 2 1 1 1 < 2 := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have harg : (1 : ℝ) / Real.sqrt (4 * 1 * 1) = 1 / 2 := by
    have h4 : (4 : ℝ) * 1 * 1 = 4 := by ring
    rw [h4, hsqrt4]
  have hlt : erfc (1 / 2) < erfc 0 := by
    apply erfc_strictAnti
    all_goals (first | exact Set.mem_univ _ | norm_num)
  rw [erfc_zero] at hlt
  simp only [erfcProfile]
  rw [harg]
  calc (2 : ℝ) * erfc (1 / 2) < 2 * 1 := mul_lt_mul_of_pos_left hlt (by norm_num)
    _ = 2 := mul_one _

/-- The far-field limit at `t = 1`. -/
example : Tendsto (fun x => erfcProfile 2 1 x 1) atTop (𝓝 0) :=
  erfcProfile_farfield 2 1 1 (by norm_num) (by norm_num)

/-- The initial limit at depth `1`. -/
example : Tendsto (fun t => erfcProfile 2 1 1 t) (𝓝[>] 0) (𝓝 0) :=
  erfcProfile_initial 2 1 1 (by norm_num) (by norm_num)

/-- Outside the physical domain: at `t = 0` the profile is `cs` at every depth, not the initial
concentration `0`. -/
example (x : ℝ) : erfcProfile 2 1 x 0 = 2 := by
  simp [erfcProfile, erfc_zero]

/-- More has entered the half-line by `t = 2` than by `t = 1`. -/
example : ∫ x in Ioi 0, erfcProfile 1 1 x 1 < ∫ x in Ioi 0, erfcProfile 1 1 x 2 :=
  erfcProfile_mass_strictMono 1 1 one_pos one_pos (mem_Ioi.mpr one_pos) (mem_Ioi.mpr two_pos)
    one_lt_two

/-!

## D. Uniqueness for the Dirichlet problem

-/

/-- A use of `diffusion_unique_dirichlet` on a finite interval and a finite time horizon: on
`[0, L] × [0, T]`, a solution `c` with the linear initial profile and the constant boundary
values `u₀` and `u₁` is the steady profile. The hypotheses on `c` are those of a solution on the
rectangle only, and those on the difference `c - steadyProfile u₀ u₁ L` are derived from them and
from `steady_xderiv_value`, `steady_boundary_zero` and `steady_boundary_L`. -/
example (u₀ u₁ L T D : ℝ) (hL : 0 < L) (hD : 0 < D) (c cx cxx ct : ℝ → ℝ → ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2) (Icc 0 L ×ˢ Icc 0 T))
    (hcx : ContinuousOn (fun p : ℝ × ℝ => cx p.1 p.2) (Icc 0 L ×ˢ Ioo 0 T))
    (hcxx : ContinuousOn (fun p : ℝ × ℝ => cxx p.1 p.2) (Icc 0 L ×ˢ Ioo 0 T))
    (hct : ContinuousOn (fun p : ℝ × ℝ => ct p.1 p.2) (Icc 0 L ×ˢ Ioo 0 T))
    (ht : ∀ x ∈ Ioo 0 L, ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => c x τ) (ct x t) t)
    (hx : ∀ x ∈ Ioo 0 L, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => c u t) (cx x t) x)
    (hxx : ∀ x ∈ Ioo 0 L, ∀ t ∈ Ioo 0 T, HasDerivAt (fun u => cx u t) (cxx x t) x)
    (hpde : ∀ x ∈ Ioo 0 L, ∀ t ∈ Ioo 0 T, ct x t = D * cxx x t)
    (hbc : ∀ t ∈ Ioo 0 T, c 0 t = u₀ ∧ c L t = u₁)
    (hinit : ∀ x ∈ Icc 0 L, c x 0 = steadyProfile u₀ u₁ L x) :
    ∀ x ∈ Icc 0 L, ∀ t ∈ Icc 0 T, c x t = steadyProfile u₀ u₁ L x := by
  have hs : Continuous fun p : ℝ × ℝ => steadyProfile u₀ u₁ L p.1 := by
    unfold steadyProfile
    fun_prop
  refine diffusion_unique_dirichlet 0 L T D hL hD c (fun x _ => steadyProfile u₀ u₁ L x)
    (fun x t => c x t - steadyProfile u₀ u₁ L x) (fun x t => cx x t - (u₁ - u₀) / L * 1)
    cxx ct (fun _ _ _ _ => rfl) (fun x hx' t ht' => (ht x hx' t ht').sub_const _)
    (fun x hx' t ht' => (hx x hx' t ht').sub (steady_xderiv_value u₀ u₁ L x))
    (fun x hx' t ht' => (hxx x hx' t ht').sub_const _) (hc.sub hs.continuousOn)
    (hcx.sub continuousOn_const) hcxx hct hpde (fun t ht' => ?_) (fun x hx' => ?_)
  · simp [(hbc t ht').1, (hbc t ht').2, steady_boundary_zero, steady_boundary_L u₀ u₁ L hL]
  · simp [hinit x hx']

/-!

## E. Parabolic scaling

-/

/-- `similarity_pde` for the solution `c(x, t) = x² + 2Dt` on all of `ℝ × ℝ` and `λ = 2`. -/
example (D : ℝ) : ∀ x t, deriv (fun τ => scaledSol (fun x t => x ^ 2 + 2 * D * t) 2 x τ) t
    = D * deriv (fun x' => deriv (fun u => scaledSol (fun x t => x ^ 2 + 2 * D * t) 2 u t) x')
      x :=
  similarity_pde D 2 two_pos (fun x t => x ^ 2 + 2 * D * t) (fun x _ => 2 * x) (fun _ _ => 2)
    (fun _ _ => 2 * D)
    (fun X T => by simpa using ((hasDerivAt_id' T).const_mul (2 * D)).const_add (X ^ 2))
    (fun X T => by simpa using (hasDerivAt_pow 2 X).add_const (2 * D * T))
    (fun X _ => by simpa using (hasDerivAt_id' X).const_mul (2 : ℝ))
    (fun _ _ => by ring)

/-- `similarity_pde_at` applies to the Gaussian, a solution for `t > 0` only: its parabolic
rescaling solves the diffusion equation at every `(x, t)` with `t > 0`. -/
example (M D lam x t : ℝ) (hD : 0 < D) (hlam : 0 < lam) (ht : 0 < t) :
    deriv (fun τ => scaledSol (gauss M D) lam x τ) t
      = D * deriv (fun x' => deriv (fun u => scaledSol (gauss M D) lam u t) x') x := by
  have hT : 0 < lam ^ 2 * t := by positivity
  exact similarity_pde_at D lam (gauss M D) (fun X T => deriv (fun x' => gauss M D x' T) X)
    (fun X T => deriv (fun x' => deriv (fun x'' => gauss M D x'' T) x') X)
    (fun X T => deriv (fun τ => gauss M D X τ) T) x t
    (gauss_tderiv_value M D _ _ hD hT).differentiableAt.hasDerivAt
    (fun X => (gauss_xderiv_value M D X _ hD hT).differentiableAt.hasDerivAt)
    (gauss_xxderiv_value M D _ _ hD hT).differentiableAt.hasDerivAt
    (gauss_pde M D _ _ hD hT)

/-- The Gaussian is self-similar: doubling `x` and quadrupling `t` halves it. -/
example (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    gauss M D (2 * x) (4 * t) = (1 / 2) * gauss M D x t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hDt : (4 * D * t : ℝ) ≠ 0 := by positivity
  have h4D4t : (4 * D * (4 * t) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * D * (4 * t)) = 2 * Real.sqrt (4 * Real.pi * D * t) := by
    have hfactor : (4 * Real.pi * D * (4 * t) : ℝ) = 2 ^ 2 * (4 * Real.pi * D * t) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : (-(2 * x) ^ 2 / (4 * D * (4 * t)) : ℝ) = (-x ^ 2 / (4 * D * t)) := by
    field_simp
    ring
  simp only [gauss]
  rw [hsqrt, hexp]
  field_simp

/-- The similarity variable is unchanged by the scaling `x ↦ 2x`, `t ↦ 4t`. -/
example : simVar 1 (2 * 3) (2 ^ 2 * 5) = simVar 1 3 5 :=
  simVar_invariant 1 3 5 2 one_pos (by norm_num) two_pos

/-- Outside the physical domain: at `t = 0` the similarity variable is `0`. -/
example (D x : ℝ) : simVar D x 0 = 0 := by
  simp [simVar]

/-!

## F. The steady membrane profile

-/

/-- The steady profile with `c₁ = 3`, `c₂ = 1`, `L = 2` takes its boundary values. -/
example : steadyProfile 3 1 2 0 = 3 ∧ steadyProfile 3 1 2 2 = 1 :=
  ⟨steady_boundary_zero 3 1 2, steady_boundary_L 3 1 2 (by norm_num)⟩

/-- It solves the steady equation for `D = 5`. -/
example (x t : ℝ) : 5 * deriv (fun x' => deriv (fun u => steadyProfile 3 1 2 u) x') x = 0 :=
  (steady_pde 3 1 2 5 x t (by norm_num)).2

/-- The steady membrane flux for `c₁ = 3`, `c₂ = 1`, `L = 2`, `D = 5` is `5`. -/
example : -5 * deriv (fun x' => steadyProfile 3 1 2 x') 0 = 5 := by
  rw [steady_flux 3 1 2 5 (by norm_num) 0]
  norm_num

/-- Outside the physical domain: for `L = 0` the profile is the constant `c₁`. -/
example (x : ℝ) : steadyProfile 3 1 0 x = 3 := by
  simp [steadyProfile]

/-!

## G. The slab sine series

-/

/-- The first (odd) coefficient through `fourierCoeff_formula`:
`(2/L) ∫₀ᴸ c₀ sin(πx/L) dx = 4c₀ / π`. -/
example (c₀ L : ℝ) (hL : 0 < L) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin ((1 : ℕ) * Real.pi * x / L) = 4 * c₀ / Real.pi := by
  rw [fourierCoeff_formula c₀ L hL 1 le_rfl]
  simp only [fourierCoeff, one_ne_zero, ite_false, Nat.cast_one, one_mul, pow_one]
  ring

/-- The second (even) coefficient through `fourierCoeff_formula`:
`(2/L) ∫₀ᴸ c₀ sin(2πx/L) dx = 0`. -/
example (c₀ L : ℝ) (hL : 0 < L) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin ((2 : ℕ) * Real.pi * x / L) = 0 := by
  rw [fourierCoeff_formula c₀ L hL 2 (by norm_num)]
  norm_num [fourierCoeff]

/-- Every odd coefficient through `fourierCoeff_formula`:
`(2/L) ∫₀ᴸ c₀ sin((2k + 1)πx/L) dx = 4c₀ / ((2k + 1)π)`. -/
example (c₀ L : ℝ) (hL : 0 < L) (k : ℕ) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin ((2 * k + 1 : ℕ) * Real.pi * x / L)
      = 4 * c₀ / ((2 * k + 1) * Real.pi) := by
  rw [fourierCoeff_formula c₀ L hL (2 * k + 1) (by omega)]
  simp only [fourierCoeff, Nat.add_one_ne_zero, ite_false, pow_succ, pow_mul, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- Every even coefficient through `fourierCoeff_formula`:
`(2/L) ∫₀ᴸ c₀ sin(2kπx/L) dx = 0` for `k ≥ 1`. -/
example (c₀ L : ℝ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin ((2 * k : ℕ) * Real.pi * x / L) = 0 := by
  rw [fourierCoeff_formula c₀ L hL (2 * k) (by omega)]
  simp [fourierCoeff, pow_mul]

/-- Every term vanishes at the boundary `x = 0`. -/
example (c₀ L D t : ℝ) (n : ℕ) : fourierTerm c₀ L D n 0 t = 0 := by
  simp [fourierTerm]

/-- Outside the physical domain: for `L = 0` every term is `0`. -/
example (c₀ D x t : ℝ) (n : ℕ) : fourierTerm c₀ 0 D n x t = 0 := by
  simp [fourierTerm]

/-- The termwise bound for `c₀ = L = D = δ = 1` at `t = 2`. -/
example (n : ℕ) (x : ℝ) :
    ‖fourierTerm 1 1 1 n x 2‖ ≤ (4 * 1 / Real.pi + 1) * Real.exp (-1 * (Real.pi / 1) ^ 2 * 1) ^ n :=
  fourierTerm_bound 1 1 1 1 zero_le_one one_pos one_pos one_pos n x 2 one_le_two

/-- The series for `c₀ = L = D = 1` converges uniformly on `[0, 1] × [1, ∞)`. -/
example : TendstoUniformlyOn
    (fun N : ℕ => fun p : ℝ × ℝ => (Finset.range N).sum fun n => fourierTerm 1 1 1 n p.1 p.2)
    (fun p => ∑' n, fourierTerm 1 1 1 n p.1 p.2) atTop (Icc 0 1 ×ˢ Ici 1) :=
  fourier_uniform_convergent 1 1 1 1 zero_le_one one_pos one_pos one_pos

end PhyslibExtTest.CondensedMatter.Diffusion

#print axioms CondensedMatter.Diffusion.fickFlux
#print axioms CondensedMatter.Diffusion.fick_continuity_imply_diffusion
#print axioms CondensedMatter.Diffusion.gauss
#print axioms CondensedMatter.Diffusion.gauss_xderiv_value
#print axioms CondensedMatter.Diffusion.gauss_xxderiv_value
#print axioms CondensedMatter.Diffusion.gauss_tderiv_value
#print axioms CondensedMatter.Diffusion.gauss_pde
#print axioms CondensedMatter.Diffusion.gauss_nonneg
#print axioms CondensedMatter.Diffusion.gauss_mass
#print axioms CondensedMatter.Diffusion.gauss_weak_limit
#print axioms CondensedMatter.Diffusion.erfc
#print axioms CondensedMatter.Diffusion.erfcDeriv
#print axioms CondensedMatter.Diffusion.erfcDeriv2
#print axioms CondensedMatter.Diffusion.erfc_zero
#print axioms CondensedMatter.Diffusion.hasDerivAt_erfc
#print axioms CondensedMatter.Diffusion.hasDerivAt_erfcDeriv
#print axioms CondensedMatter.Diffusion.erfc_ode
#print axioms CondensedMatter.Diffusion.erfc_strictAnti
#print axioms CondensedMatter.Diffusion.erfc_tendsto_atTop
#print axioms CondensedMatter.Diffusion.erfc_tail
#print axioms CondensedMatter.Diffusion.erfc_nonneg
#print axioms CondensedMatter.Diffusion.erfc_le_gauss
#print axioms CondensedMatter.Diffusion.erfcProfile
#print axioms CondensedMatter.Diffusion.erfcProfile_xderiv_value
#print axioms CondensedMatter.Diffusion.erfcProfile_xxderiv_value
#print axioms CondensedMatter.Diffusion.erfcProfile_tderiv_value
#print axioms CondensedMatter.Diffusion.erfcProfile_pde
#print axioms CondensedMatter.Diffusion.erfcProfile_surface
#print axioms CondensedMatter.Diffusion.erfcProfile_farfield
#print axioms CondensedMatter.Diffusion.erfcProfile_initial
#print axioms CondensedMatter.Diffusion.erfcProfile_integrableOn
#print axioms CondensedMatter.Diffusion.profile_pointwise_lt
#print axioms CondensedMatter.Diffusion.erfcProfile_mass_strictMono
#print axioms CondensedMatter.Diffusion.continuousOn_energy
#print axioms CondensedMatter.Diffusion.energy_identity_deriv
#print axioms CondensedMatter.Diffusion.diffusion_unique_dirichlet
#print axioms CondensedMatter.Diffusion.scaledSol
#print axioms CondensedMatter.Diffusion.similarity_pde_at
#print axioms CondensedMatter.Diffusion.similarity_pde
#print axioms CondensedMatter.Diffusion.simVar
#print axioms CondensedMatter.Diffusion.simVar_invariant
#print axioms CondensedMatter.Diffusion.steadyProfile
#print axioms CondensedMatter.Diffusion.steady_boundary_zero
#print axioms CondensedMatter.Diffusion.steady_boundary_L
#print axioms CondensedMatter.Diffusion.steady_xderiv_value
#print axioms CondensedMatter.Diffusion.steady_pde
#print axioms CondensedMatter.Diffusion.steady_flux
#print axioms CondensedMatter.Diffusion.fourierCoeff
#print axioms CondensedMatter.Diffusion.fourierTerm
#print axioms CondensedMatter.Diffusion.fourierCoeff_formula
#print axioms CondensedMatter.Diffusion.fourierTerm_bound
#print axioms CondensedMatter.Diffusion.fourier_dominator_summable
#print axioms CondensedMatter.Diffusion.fourier_uniform_convergent

end
