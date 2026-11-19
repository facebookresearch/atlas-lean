/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import MathlibExt.Analysis.ODE.ContinuumBalances
public import PhyslibExt.Thermodynamics.ProcessPorts
import Mathlib.Analysis.Calculus.Deriv.Prod
import MathlibExt.Probability.Diffusion.FokkerPlanckFreeEnergy
import Mathlib.Tactic.Ring

/-!
# Control volumes: moving-endpoint transport, fixed-box balance, energy and momentum ports

## i. Overview

The Leibniz (moving-endpoint transport) identity in one space
dimension: for a field `u t x` with `u` and its time partial
`u_t` jointly continuous (no spatial derivative of `u` is
assumed) and endpoints `a, b` differentiable at the evaluation
time `t`,
`d/dt ∫_{a t}^{b t} u t x dx = ∫_{a t}^{b t} u_t dx
+ u(t, b t) b'(t) - u(t, a t) a'(t)`, and, when
`u_t = src - f_x`, the relative-flux form with endpoint terms
`f - u * endpointSpeed`. Joint continuity of `u` and `u_t` is
what the proof uses: slice-wise continuity plus fixed-limit
differentiation alone admit oscillating mass at the moving
endpoint. No general moving-domain Reynolds theorem is
claimed.

For a fixed nondegenerate rectangular box `[a, b]` in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, a jointly `C¹` density `u`, a flux `q`
that is `C¹` on an open neighbourhood of the box and the local law
`∂ₜu + div q = s`, the stored amount satisfies
`d/dt ∫_[a, b] u = ∫_[a, b] s - boxOutwardFlux a b (q t)`. The
outward flux is written face by face: the face `x i = b i` has
outward normal `+eᵢ` and the face `x i = a i` has `-eᵢ`, so a
positive `qᵢ` is outflow on the upper face and inflow on the lower
one. Mathlib's divergence theorem for boxes discharges the
boundary-divergence premise of
`MathlibExt.Analysis.ODE.ContinuumBalances.hasDerivAt_setIntegral_of_divergence`;
local conservation stays the model input. No general smooth-domain
trace or divergence theorem is claimed.

For a declared local total-energy law `∂ₜE + div (G + J) = q̇ + ẇ` on
the box, with `G = (E + p) v` the convective-plus-pressure flux, `J`
every other energy flux, `q̇` the volumetric heating and `ẇ` the shaft
power density delivered to the fluid, the storage rate is
`(∫ q̇ - Φ_J) - Ẇ_out - Φ_G`, where
`Ẇ_out = ProcessPorts.workOut (∫ ẇ)` is the engineering shaft work
out. On a face with uniform density `ρ ≠ 0`, specific internal energy
`e`, pressure `p`, velocity `v`, elevation `z` and outward normal
velocity `v_n`, the outward rate `A v_n (ρ (e + |v|² / 2 + g z) + p)`
equals `ṁ (h + |v|² / 2 + g z)` with `ṁ = ρ A v_n` and
`h = e + p / ρ`, so the flow work `p / ρ` is counted once, inside `h`;
adding it again overcounts the rate by `A v_n p`. With the inlet on
the face `x₀ = a₀`, the outlet on `x₀ = b₀` and zero normal component
of `G` on the side faces, the storage rate is
`Q̇ - Ẇ_out + ṁ_in θ_in - ṁ_out θ_out`, `θ = h + |v|² / 2 + g z`, where
each port's velocity is one vector of the box's space, giving both its
mass flow `ρ A₀ v₀` and its kinetic energy. The
side-face hypothesis constrains only the flux `G`: no wall velocity and
no relation `G = (E + p) v` enters the statement, so it is weaker than
impermeability. The energy law is a model input, not derived from mass
conservation.

For a fluid with density `ρ`, velocity `v`, Cauchy stress `σ` and body force density `f`, where
`σ x j i` is the `j`-th component of the traction on a surface of unit normal `eᵢ`, the declared
local momentum law is `∂ₜ(ρ vⱼ) + div (momentumFlux ρ v σ j) = fⱼ` for every component `j`; the
flux has the `i`-th component `ρ vⱼ vᵢ - σ x j i`, convective transport of `j`-momentum minus the
surface force. The fixed-box balance applied to each component gives the momentum rate as the body
force plus the resultant of the boundary traction `σ n` minus the momentum outflow. With the inlet
on `x₀ = a₀` (outward normal `-e₀`), the outlet on `x₀ = b₀` (`+e₀`), impermeable side walls,
uniform port density and velocity and pressure-only port tractions `σ e₀ = -p e₀`, the rate is
`ṁ_in v_in - ṁ_out v_out - ∑_ports p A n + F_body + F_wall` with `ṁ = ρ A₀ v₀`, where `F_wall`, the
traction resultant of the walls, includes the wall pressure and shear: pressure enters once, on the
ports through the port term and on the walls inside `F_wall`. A viscous port traction `τ`
(`σ e₀ = -p e₀ + τ`) adds the term `A₀ (τ_out - τ_in)`: the outlet face carries `τ_out`, and the
inlet face, whose outward normal is `-e₀`, carries `-τ_in`. The momentum law is a model input;
neither a constitutive law nor the symmetry of `σ` is used.

## ii. Key results

- `ControlVolumes.movingEndpoint_hasDerivAt`: the Leibniz
  identity in `HasDerivAt` form for oriented integrals (no
  endpoint ordering needed), with differentiation under the
  fixed-limit integral derived from the joint-continuity data.
- `ControlVolumes.movingEndpoint_deriv`: its `deriv` corollary.
- `ControlVolumes.movingEndpoint_hasDerivAt_flux` and
  `movingEndpoint_deriv_flux`: the relative-flux forms exposing
  `f - u * endpointSpeed` at both ends.
- `ControlVolumes.boxOutwardFlux`: the outward flux of a vector
  field through the faces of a box.
- `ControlVolumes.integral_divergence_box`: the divergence theorem
  on a box, `∫_[a, b] div F = boxOutwardFlux a b F`.
- `ControlVolumes.hasDerivAt_boxIntegral`: the fixed-box balance
  with explicit faces.
- `ControlVolumes.portEnergyRate_eq_massFlow` and
  `ControlVolumes.flowWork_double_count`: the port rate is
  `ṁ (h + |v|² / 2 + g z)`, and counting `p / ρ` twice overcounts it.
- `ControlVolumes.boxOutwardFlux_add` and
  `ControlVolumes.boxOutwardFlux_uniform`: additivity of the outward
  flux and its value for face-wise uniform normal components.
- `ControlVolumes.hasDerivAt_energy_box` and
  `ControlVolumes.hasDerivAt_energy_twoPort`: the energy balance of a
  fixed box and its two-port form.
- `ControlVolumes.momentumFlux` and `ControlVolumes.faceTractionResultant`: the flux of a momentum
  component and the traction resultant of a pair of opposite faces.
- `ControlVolumes.hasDerivAt_momentum_box` and `ControlVolumes.hasDerivAt_momentum_box_traction`:
  the fixed-box balance applied to each momentum component, and its form with the boundary
  traction and the momentum outflow.
- `ControlVolumes.hasDerivAt_momentum_twoPort` and
  `ControlVolumes.hasDerivAt_momentum_twoPort_viscous`: the two-port momentum balance with
  pressure-only port tractions, and the term a viscous port traction adds.

## iii. Table of contents

- A. Moving-endpoint transport
- B. Fixed-box balance with explicit faces
  - B.1. Faces and the divergence theorem
  - B.2. The balance
- C. Energy ports
  - C.1. Port rates and flow work
  - C.2. Uniform faces
  - C.3. The energy balance
- D. Momentum ports
  - D.1. Momentum flux and face tractions
  - D.2. The momentum balance
  - D.3. Two ports with pressure and viscous tractions

## iv. References

- The classical Leibniz integral rule; the statement is
  self-contained.
- Mathlib's divergence theorem for rectangular boxes,
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
- R. B. Bird, W. E. Stewart and E. N. Lightfoot, *Transport
  Phenomena*, 2nd ed., Wiley (2002), Section 19.1 (the equation of
  continuity for a fixed volume element), Section 11.1 (the equation
  of change for total energy), Section 3.2 (the equation of motion) and
  Section 7.2 (the macroscopic momentum balance).
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering
  Approach*, McGraw-Hill, ch. 5: flow work, enthalpy `h = u + p v` and
  the control-volume energy balance.
- F. M. White, *Fluid Mechanics*, McGraw-Hill, chapter 3: the linear momentum relation for a fixed
  control volume, with pressure on the inlet and outlet and the wall force.

## A. Moving-endpoint transport

-/

@[expose] public section

namespace ControlVolumes

private lemma slice_continuous {w : ℝ → ℝ → ℝ}
    (hjoint : Continuous fun p : ℝ × ℝ => w p.1 p.2) (τ : ℝ) :
    Continuous fun x : ℝ => w τ x :=
  hjoint.comp (continuous_const.prodMk continuous_id)

private lemma hasDerivAt_fixed_integral {u ut : ℝ → ℝ → ℝ}
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (t y : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
      (∫ x in (0 : ℝ)..y, ut t x) t :=
  MathlibExt.Probability.FokkerPlanck.integral_hasDerivAt u ut 0 y t
    hjoint hcont_ut hut

private lemma hasDerivAt_endpoint_integral {u ut : ℝ → ℝ → ℝ} {c c' : ℝ → ℝ}
    (t : ℝ) (hc : HasDerivAt c (c' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..c τ, u τ x)
      ((∫ x in (0 : ℝ)..c t, ut t x) + u t (c t) * c' t) t := by
  have hswap : ∀ t y : ℝ,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
        (∫ x in (0 : ℝ)..y, ut t x) t :=
    fun t y => hasDerivAt_fixed_integral hjoint hut hcont_ut t y
  have hslice : ∀ τ : ℝ, Continuous fun x : ℝ => u τ x :=
    fun τ => hjoint.comp (continuous_const.prodMk continuous_id)
  have hE1 : ∀ τ : ℝ,
      (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
        - u t (c t) * (c τ - c t)
        = ∫ x in c t..c τ, (u τ x - u t (c t)) := by
    intro τ
    have h1 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (c t) 0 :=
      (hslice τ).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume 0 (c τ) :=
      (hslice τ).intervalIntegrable _ _
    have h3 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (c t) (c τ) :=
      (hslice τ).intervalIntegrable _ _
    have h4 : IntervalIntegrable (fun _ : ℝ => u t (c t)) MeasureTheory.volume (c t) (c τ) :=
      intervalIntegrable_const
    have hadj : (∫ x in c t..(0 : ℝ), u τ x) + (∫ x in (0 : ℝ)..c τ, u τ x)
        = ∫ x in c t..c τ, u τ x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in c t..(0 : ℝ), u τ x) = -(∫ x in (0 : ℝ)..c t, u τ x) :=
      intervalIntegral.integral_symm 0 (c t)
    have hsub : (∫ x in c t..c τ, (u τ x - u t (c t)))
        = (∫ x in c t..c τ, u τ x) - (∫ x in c t..c τ, u t (c t)) :=
      intervalIntegral.integral_sub h3 h4
    have hconst : (∫ x in c t..c τ, u t (c t)) = (c τ - c t) * u t (c t) := by
      have hc0 := intervalIntegral.integral_const (a := c t) (b := c τ) (u t (c t))
      rwa [smul_eq_mul] at hc0
    have eA : (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
        = ∫ x in c t..c τ, u τ x := by
      rw [← hadj, hsymm]; ring
    rw [eA, hsub, hconst]; ring
  have hE1o : (fun τ : ℝ => (∫ x in (0 : ℝ)..c τ, u τ x)
      - (∫ x in (0 : ℝ)..c t, u τ x) - u t (c t) * (c τ - c t))
      =o[nhds t] fun τ : ℝ => τ - t := by
    refine Asymptotics.isLittleO_iff.mpr ?_
    intro c₀ hc₀
    have hK : (0 : ℝ) < ‖c' t‖ + 1 := by
      have hnn := norm_nonneg (c' t)
      linarith
    have hKne : (‖c' t‖ + 1 : ℝ) ≠ 0 := ne_of_gt hK
    have hε0 : (0 : ℝ) < c₀ / (‖c' t‖ + 1) := div_pos hc₀ hK
    have hcont_at : ContinuousAt (fun p : ℝ × ℝ => u p.1 p.2) (t, c t) :=
      hjoint.continuousAt
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont_at _ hε0
    have e1 : ∀ᶠ τ in nhds t, τ ∈ Metric.ball t δ :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds t hδ0) (fun _ h => h)
    have e2 : ∀ᶠ τ in nhds t, c τ ∈ Metric.ball (c t) δ :=
      hc.continuousAt.eventually_mem (Metric.ball_mem_nhds _ hδ0)
    have hco := HasDerivAt.isLittleO hc
    have eK : ∀ᶠ τ in nhds t, ‖c τ - c t - (τ - t) • c' t‖ ≤ 1 * ‖τ - t‖ :=
      hco.def zero_lt_one
    filter_upwards [e1, e2, eK] with τ hτ hcτ hKτ
    rw [Metric.mem_ball, Real.dist_eq] at hτ hcτ
    have hmem : ∀ x ∈ Set.uIoc (c t) (c τ),
        ‖u τ x - u t (c t)‖ ≤ c₀ / (‖c' t‖ + 1) := by
      intro x hx
      have hxcc : x ∈ Set.uIcc (c t) (c τ) := Set.uIoc_subset_uIcc hx
      have hxc : |x - c t| ≤ |c τ - c t| := Set.abs_sub_left_of_mem_uIcc hxcc
      have hdist : dist (τ, x) (t, c t) < δ := by
        rw [Prod.dist_eq]
        show max |τ - t| |x - c t| < δ
        exact max_lt hτ (lt_of_le_of_lt hxc hcτ)
      have hclose : |u τ x - u t (c t)| < c₀ / (‖c' t‖ + 1) := hδ hdist
      rw [Real.norm_eq_abs]
      exact le_of_lt hclose
    have hI : ‖∫ x in c t..c τ, (u τ x - u t (c t))‖
        ≤ (c₀ / (‖c' t‖ + 1)) * |c τ - c t| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hmem
    have hE1τ := hE1 τ
    have hKd : ‖c τ - c t‖ ≤ (‖c' t‖ + 1) * ‖τ - t‖ := by
      have hexpand : c τ - c t = (c τ - c t - (τ - t) • c' t) + (τ - t) * c' t := by
        rw [smul_eq_mul]; ring
      calc ‖c τ - c t‖
          = ‖(c τ - c t - (τ - t) • c' t) + (τ - t) * c' t‖ :=
            congrArg Norm.norm hexpand
        _ ≤ ‖c τ - c t - (τ - t) • c' t‖ + ‖(τ - t) * c' t‖ := norm_add_le _ _
        _ ≤ 1 * ‖τ - t‖ + ‖τ - t‖ * ‖c' t‖ := by
            rw [norm_mul]; exact add_le_add hKτ le_rfl
        _ = (‖c' t‖ + 1) * ‖τ - t‖ := by ring
    have hεK : c₀ / (‖c' t‖ + 1) * (‖c' t‖ + 1) = c₀ :=
      div_mul_cancel₀ _ hKne
    show ‖(∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
      - u t (c t) * (c τ - c t)‖ ≤ c₀ * ‖τ - t‖
    rw [hE1τ]
    calc ‖∫ x in c t..c τ, (u τ x - u t (c t))‖
        ≤ (c₀ / (‖c' t‖ + 1)) * |c τ - c t| := hI
      _ = (c₀ / (‖c' t‖ + 1)) * ‖c τ - c t‖ := by rw [Real.norm_eq_abs (c τ - c t)]
      _ ≤ (c₀ / (‖c' t‖ + 1)) * ((‖c' t‖ + 1) * ‖τ - t‖) :=
          mul_le_mul_of_nonneg_left hKd (le_of_lt hε0)
      _ = c₀ * ‖τ - t‖ := by rw [← mul_assoc, hεK]
  have hE2o : (fun τ : ℝ => (∫ x in (0 : ℝ)..c t, u τ x)
      - (∫ x in (0 : ℝ)..c t, u t x) - (τ - t) • (∫ x in (0 : ℝ)..c t, ut t x))
      =o[nhds t] fun τ : ℝ => τ - t :=
    HasDerivAt.isLittleO (hswap t (c t))
  have hCo : (fun τ : ℝ => c τ - c t - (τ - t) • c' t)
      =o[nhds t] fun τ : ℝ => τ - t :=
    HasDerivAt.isLittleO hc
  have hsum := (hE1o.add hE2o).add (hCo.const_mul_left (u t (c t)))
  refine HasDerivAt.of_isLittleO
    ((Asymptotics.isLittleO_congr ?hf Filter.EventuallyEq.rfl).mp hsum)
  filter_upwards with τ
  show ((∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
    - u t (c t) * (c τ - c t)
    + ((∫ x in (0 : ℝ)..c t, u τ x) - (∫ x in (0 : ℝ)..c t, u t x)
    - (τ - t) • (∫ x in (0 : ℝ)..c t, ut t x)))
    + u t (c t) * (c τ - c t - (τ - t) • c' t)
    = (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u t x)
    - (τ - t) • ((∫ x in (0 : ℝ)..c t, ut t x) + u t (c t) * c' t)
  simp only [smul_eq_mul]
  ring

/-- Moving-endpoint transport (Leibniz rule), `HasDerivAt` form:
for a field `u t x` with `u` and its actual time partial `ut`
jointly continuous and endpoints `a, b` differentiable at `t`,
the moving integral has derivative
`∫_{a t}^{b t} ut t x dx + u t (b t) * b' t - u t (a t) * a' t`
at `t`. Differentiation under the fixed-limit integral is derived
from the joint-continuity data, not assumed. No ordering
`a t < b t` is needed for the oriented-integral statement. -/
theorem movingEndpoint_hasDerivAt {u ut : ℝ → ℝ → ℝ} {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    HasDerivAt (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      ((∫ x in a t..b t, ut t x) + u t (b t) * b' t -
        u t (a t) * a' t) t := by
  have hslice : ∀ τ : ℝ, Continuous fun x : ℝ => u τ x :=
    fun τ => slice_continuous hjoint τ
  have hslice_ut : ∀ τ : ℝ, Continuous fun x : ℝ => ut τ x :=
    fun τ => slice_continuous hcont_ut τ
  have hGb : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..b τ, u τ x)
      ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t) t :=
    hasDerivAt_endpoint_integral t hb hjoint hut hcont_ut
  have hGa : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..a τ, u τ x)
      ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t) t :=
    hasDerivAt_endpoint_integral t ha hjoint hut hcont_ut
  have hsplit : ∀ τ : ℝ, (∫ x in a τ..b τ, u τ x)
      = (∫ x in (0 : ℝ)..b τ, u τ x) - (∫ x in (0 : ℝ)..a τ, u τ x) := by
    intro τ
    have h1 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (a τ) 0 :=
      (hslice τ).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume 0 (b τ) :=
      (hslice τ).intervalIntegrable _ _
    have hadj : (∫ x in a τ..(0 : ℝ), u τ x) + (∫ x in (0 : ℝ)..b τ, u τ x)
        = ∫ x in a τ..b τ, u τ x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in a τ..(0 : ℝ), u τ x) = -(∫ x in (0 : ℝ)..a τ, u τ x) :=
      intervalIntegral.integral_symm 0 (a τ)
    rw [← hadj, hsymm]; ring
  have hS : (∫ x in (0 : ℝ)..b t, ut t x) - (∫ x in (0 : ℝ)..a t, ut t x)
      = ∫ x in a t..b t, ut t x := by
    have h1 : IntervalIntegrable (fun x : ℝ => ut t x) MeasureTheory.volume (a t) 0 :=
      (hslice_ut t).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => ut t x) MeasureTheory.volume 0 (b t) :=
      (hslice_ut t).intervalIntegrable _ _
    have hadj : (∫ x in a t..(0 : ℝ), ut t x) + (∫ x in (0 : ℝ)..b t, ut t x)
        = ∫ x in a t..b t, ut t x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in a t..(0 : ℝ), ut t x) = -(∫ x in (0 : ℝ)..a t, ut t x) :=
      intervalIntegral.integral_symm 0 (a t)
    rw [← hadj, hsymm]; ring
  have hev : (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      =ᶠ[nhds t] (fun τ : ℝ => (∫ x in (0 : ℝ)..b τ, u τ x)
        - (∫ x in (0 : ℝ)..a τ, u τ x)) :=
    Filter.Eventually.of_forall hsplit
  have h := (hGb.sub hGa).congr_of_eventuallyEq hev
  have hval : ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t)
      - ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t)
      = (∫ x in a t..b t, ut t x) + u t (b t) * b' t - u t (a t) * a' t := by
    rw [← hS]; ring
  rwa [hval] at h

/-- Moving-endpoint transport, `deriv` form (corollary of
`movingEndpoint_hasDerivAt`). -/
theorem movingEndpoint_deriv {u ut : ℝ → ℝ → ℝ} {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, ut t x) + u t (b t) * b' t -
        u t (a t) * a' t := by
  exact (movingEndpoint_hasDerivAt t ha hb hjoint hut hcont_ut).deriv

/-- Relative-flux form, `HasDerivAt` version: if
`ut = src - fx` where `fx t` is the spatial derivative of a flux
`f t`, the endpoint terms combine into relative fluxes
`f - u * endpointSpeed`. -/
theorem movingEndpoint_hasDerivAt_flux {u ut f fx src : ℝ → ℝ → ℝ}
    {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hfx : ∀ x ∈ Set.uIcc (a t) (b t),
      HasDerivAt (fun y : ℝ => f t y) (fx t x) x)
    (hcont_fx : ContinuousOn (fun x : ℝ => fx t x)
      (Set.uIcc (a t) (b t)))
    (hPDE : ∀ x ∈ Set.uIcc (a t) (b t), ut t x = src t x - fx t x)
    (hint_src : IntervalIntegrable (fun x : ℝ => src t x)
      MeasureTheory.volume (a t) (b t)) :
    HasDerivAt (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      ((∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t)) t := by
  have hmain := movingEndpoint_hasDerivAt t ha hb hjoint hut hcont_ut
  have hFTC : (∫ x in a t..b t, fx t x) = f t (b t) - f t (a t) := by
    have hderiv : ∀ x ∈ Set.uIcc (a t) (b t),
        HasDerivAt (fun y : ℝ => f t y) (fx t x) x := hfx
    have hint : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      hcont_fx.intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsplit : (∫ x in a t..b t, ut t x)
      = (∫ x in a t..b t, src t x) - (∫ x in a t..b t, fx t x) := by
    have hfx_int : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      hcont_fx.intervalIntegrable
    have h : (∫ x in a t..b t, ut t x)
        = ∫ x in a t..b t, (src t x - fx t x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hPDE x hx
    rw [h]
    exact intervalIntegral.integral_sub hint_src hfx_int
  have hval : (∫ x in a t..b t, ut t x) + u t (b t) * b' t - u t (a t) * a' t
      = (∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t) := by
    rw [hsplit, hFTC]; ring
  rwa [hval] at hmain

/-- Relative-flux form, `deriv` version (corollary). -/
theorem movingEndpoint_deriv_flux {u ut f fx src : ℝ → ℝ → ℝ}
    {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hfx : ∀ x ∈ Set.uIcc (a t) (b t),
      HasDerivAt (fun y : ℝ => f t y) (fx t x) x)
    (hcont_fx : ContinuousOn (fun x : ℝ => fx t x)
      (Set.uIcc (a t) (b t)))
    (hPDE : ∀ x ∈ Set.uIcc (a t) (b t), ut t x = src t x - fx t x)
    (hint_src : IntervalIntegrable (fun x : ℝ => src t x)
      MeasureTheory.volume (a t) (b t)) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t) := by
  exact (movingEndpoint_hasDerivAt_flux t ha hb hjoint hut hcont_ut hfx hcont_fx hPDE
    hint_src).deriv


/-- Moving interior jump transport: for an interface curve
`s` differentiable at `t` inside the fixed interval `[a, b]`, with left and right
fields `uL`, `uR` (time partials `vL`, `vR`), the split integral
`(∫ x in a..s t, uL t x) + (∫ x in s t..b, uR t x)` has
derivative the two classical integrals plus the interface
contribution `s' t * (uL t (s t) - uR t (s t))`. This is the
two instantiations of `movingEndpoint_hasDerivAt` (moving right
endpoint on the left piece, moving left endpoint on the right
piece) added together. As stated this is an oriented-integral
identity with no ordering hypothesis on `s t`; in the physical
interior-interface case, where `s t` lies inside `[a, b]`, the two
integrals are the genuine left and right pieces of `[a, b]`. -/
theorem movingJumpTransport {uL uR vL vR : ℝ → ℝ → ℝ}
    {s s' : ℝ → ℝ} {a b : ℝ} (t : ℝ) (hs : HasDerivAt s (s' t) t)
    (hjL : Continuous fun p : ℝ × ℝ => uL p.1 p.2)
    (hvL : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => uL τ x) (vL t x) t)
    (hcvL : Continuous fun p : ℝ × ℝ => vL p.1 p.2)
    (hjR : Continuous fun p : ℝ × ℝ => uR p.1 p.2)
    (hvR : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => uR τ x) (vR t x) t)
    (hcvR : Continuous fun p : ℝ × ℝ => vR p.1 p.2) :
    HasDerivAt
      (fun τ : ℝ => (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x))
      ((∫ x in a..s t, vL t x) + (∫ x in s t..b, vR t x) +
        s' t * (uL t (s t) - uR t (s t))) t := by
  have hL := movingEndpoint_hasDerivAt (u := uL) (ut := vL)
    (a := fun _ : ℝ => a) (b := s) (a' := fun _ : ℝ => 0) (b' := s')
    t (hasDerivAt_const t a) hs hjL hvL hcvL
  have hR := movingEndpoint_hasDerivAt (u := uR) (ut := vR)
    (a := s) (b := fun _ : ℝ => b) (a' := s') (b' := fun _ : ℝ => 0)
    t hs (hasDerivAt_const t b) hjR hvR hcvR
  have hL' : HasDerivAt (fun τ : ℝ => ∫ x in a..s τ, uL τ x)
      ((∫ x in a..s t, vL t x) + s' t * uL t (s t)) t := by
    convert hL using 1
    ring
  have hR' : HasDerivAt (fun τ : ℝ => ∫ x in s τ..b, uR τ x)
      ((∫ x in s t..b, vR t x) - s' t * uR t (s t)) t := by
    convert hR using 1
    ring
  have h := hL'.add hR'
  convert h using 1
  ring


section FixedBox

open Set MeasureTheory
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## B. Fixed-box balance with explicit faces -/

/-! ### B.1. Faces and the divergence theorem -/

/-- The outward flux of a vector field `F` through the boundary of the box `[a, b]` in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, face by face: for each coordinate `i`, the integral of `Fᵢ` over the
upper face `x i = b i` (outward normal `+eᵢ`) minus its integral over the lower face
`x i = a i` (outward normal `-eᵢ`), both over the box `[a ∘ i.succAbove, b ∘ i.succAbove]` of the
remaining coordinates. -/
noncomputable def boxOutwardFlux {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

/-- **Divergence theorem on a box**, in the notation of the conditional balance: for a vector
field `F` of class `C¹` on an open set `U` containing the nondegenerate box `[a, b]`,
`∫_[a, b] div F = boxOutwardFlux a b F`. -/
lemma integral_divergence_box {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    {F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hF : ContDiffOn ℝ 1 F U) :
    ∫ x in Icc a b, divergence F x = boxOutwardFlux a b F := by
  have hle : a ≤ b := fun i => (hab i).le
  have hdiff : ∀ x ∈ U, HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    (((hF.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcont : ContinuousOn (fun x => fderiv ℝ F x) U :=
    hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiv : ∀ x ∈ U, divergence F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
    intro x hx
    unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((hasFDerivAt_pi'.1 (hdiff x hx)) i).fderiv]
    simp
  rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => hdiv x (hbox hx))]
  refine integral_divergence_of_hasFDerivAt_off_countable a b hle F (fderiv ℝ F) ∅
    countable_empty (hF.continuousOn.mono hbox) (fun x hx => hdiff x (hbox ?_)) ?_
  · exact ⟨fun i => (hx.1 i (Set.mem_univ i)).1.le, fun i => (hx.1 i (Set.mem_univ i)).2.le⟩
  · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp_continuousOn
      ((hcont.clm_apply continuousOn_const))).mono hbox

/-! ### B.2. The balance -/

/-- **Fixed-box balance with explicit faces.** For a nondegenerate box `[a, b]`, a jointly `C¹`
density `u`, a flux `q t` of class `C¹` on an open neighbourhood of the box, an integrable source
`s t` and the local law `∂ₜu + div q = s` on the box at time `t`,
`d/dt ∫_[a, b] u = ∫_[a, b] s - boxOutwardFlux a b (q t)`. -/
lemma hasDerivAt_boxIntegral {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {u s : ℝ → (Fin (n + 1) → ℝ) → ℝ} {q : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hq : ContDiffOn ℝ 1 (q t) U)
    (hs : IntegrableOn (s t) (Icc a b))
    (hlaw : ∀ x ∈ Icc a b, deriv (fun τ => u τ x) t + divergence (q t) x = s t x) :
    HasDerivAt (fun τ => ∫ x in Icc a b, u τ x)
      ((∫ x in Icc a b, s t x) - boxOutwardFlux a b (q t)) t := by
  have h := MathlibExt.Analysis.ODE.ContinuumBalances.hasDerivAt_setIntegral_of_divergence
    (Φ := fun _ => boxOutwardFlux a b (q t)) isCompact_Icc hu hs hlaw
    (integral_divergence_box hab hU hbox hq)
  rwa [neg_add_eq_sub] at h

end FixedBox

section EnergyPorts

open Set MeasureTheory
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## C. Energy ports -/

/-! ### C.1. Port rates and flow work -/

/-- The specific enthalpy `h = e + p / ρ` of a specific internal energy `e`, a pressure `p` and a
density `ρ`. -/
noncomputable def specificEnthalpy (e p ρ : ℝ) : ℝ := e + p / ρ

/-- The outward convective internal, kinetic and potential energy plus pressure power through a
uniform face of area `A` with outward normal velocity `vn`: `A vn (ρ (e + |v|² / 2 + g z) + p)`,
with `|v|² = v ⬝ᵥ v`. Physically `vn` is the component of the velocity `v` along the face's
outward unit normal; this definition and the two identities below take both as arguments and
hold for all values, and `hasDerivAt_energy_twoPort` takes the normal components from the port
velocity vectors. -/
noncomputable def portEnergyRate {m : ℕ} (ρ A vn e p g z : ℝ) (v : Fin m → ℝ) : ℝ :=
  A * vn * (ρ * (e + v ⬝ᵥ v / 2 + g * z) + p)

/-- **Flow work counted once**: with `ṁ = ρ A vn` and `h = e + p / ρ`, the port rate is
`ṁ (h + |v|² / 2 + g z)`. -/
lemma portEnergyRate_eq_massFlow {m : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) (A vn e p g z : ℝ)
    (v : Fin m → ℝ) :
    portEnergyRate ρ A vn e p g z v =
      ρ * A * vn * (specificEnthalpy e p ρ + v ⬝ᵥ v / 2 + g * z) := by
  unfold portEnergyRate specificEnthalpy
  field_simp
  ring

/-- Adding `p / ρ` again after using the enthalpy overcounts the port rate by the pressure power
`A vn p`. -/
lemma flowWork_double_count {m : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) (A vn e p g z : ℝ) (v : Fin m → ℝ) :
    ρ * A * vn * (specificEnthalpy e p ρ + p / ρ + v ⬝ᵥ v / 2 + g * z) =
      portEnergyRate ρ A vn e p g z v + A * vn * p := by
  unfold portEnergyRate specificEnthalpy
  field_simp
  ring

/-! ### C.2. Uniform faces -/

/-- The area `∏ⱼ (b - a)` of the two faces of the box `[a, b]` normal to `eᵢ`. -/
def faceArea {n : ℕ} (a b : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∏ j : Fin n, (b (i.succAbove j) - a (i.succAbove j))

/-- The outward flux is additive for fields continuous on a set containing the box. -/
lemma boxOutwardFlux_add {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin (n + 1) → ℝ)} (hbox : Icc a b ⊆ U)
    {F G : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hF : ContinuousOn F U)
    (hG : ContinuousOn G U) :
    boxOutwardFlux a b (F + G) = boxOutwardFlux a b F + boxOutwardFlux a b G := by
  have hface : ∀ (i : Fin (n + 1)) (c : ℝ), c ∈ Icc (a i) (b i) →
      ∀ H : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ, ContinuousOn H U →
      IntegrableOn (fun y => H (i.insertNth c y) i) (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro i c hc H hH
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    have hmaps : MapsTo (fun y : Fin n → ℝ => (i.insertNth c y : Fin (n + 1) → ℝ))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) U := fun y hy =>
      hbox (Fin.insertNth_mem_Icc.2 ⟨hc, hy⟩)
    have hcont : Continuous fun y : Fin n → ℝ => (i.insertNth c y : Fin (n + 1) → ℝ) := by
      fun_prop
    exact (continuous_apply i).comp_continuousOn (hH.comp hcont.continuousOn hmaps)
  have hbI : ∀ i, b i ∈ Icc (a i) (b i) := fun i => ⟨(hab i).le, le_rfl⟩
  have haI : ∀ i, a i ∈ Icc (a i) (b i) := fun i => ⟨le_rfl, (hab i).le⟩
  unfold boxOutwardFlux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  rw [integral_add (hface i _ (hbI i) F hF) (hface i _ (hbI i) G hG),
    integral_add (hface i _ (haI i) F hF) (hface i _ (haI i) G hG)]
  ring

/-- A flux whose normal component is the constant `cU i` on the face `x i = b i` and `cL i` on
the face `x i = a i` has outward flux `∑ᵢ Aᵢ (cU i - cL i)`. -/
lemma boxOutwardFlux_uniform {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {cU cL : Fin (n + 1) → ℝ}
    (hU : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i = cU i)
    (hL : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i = cL i) :
    boxOutwardFlux a b F = ∑ i, faceArea a b i * (cU i - cL i) := by
  unfold boxOutwardFlux faceArea
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : (a ∘ i.succAbove) ≤ (b ∘ i.succAbove) := fun j => (hab _).le
  rw [setIntegral_congr_fun measurableSet_Icc (hU i),
    setIntegral_congr_fun measurableSet_Icc (hL i),
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, measureReal_def,
    Real.volume_Icc_pi_toReal hle]
  simp only [Function.comp_apply]
  ring

/-! ### C.3. The energy balance -/

/-- **Energy balance of a fixed box** under the declared law `∂ₜE + div (G + J) = q̇ + ẇ`: the
storage rate is `(∫ q̇ - Φ_J) - workOut (∫ ẇ) - Φ_G`, heat in minus shaft work out minus the
outward convective-plus-pressure flux. -/
lemma hasDerivAt_energy_box {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {E qdot wdot : ℝ → (Fin (n + 1) → ℝ) → ℝ}
    {G J : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hE : ContDiff ℝ 1 (Function.uncurry E)) (hG : ContDiffOn ℝ 1 (G t) U)
    (hJ : ContDiffOn ℝ 1 (J t) U) (hq : IntegrableOn (qdot t) (Icc a b))
    (hw : IntegrableOn (wdot t) (Icc a b))
    (hlaw : ∀ x ∈ Icc a b,
      deriv (fun τ => E τ x) t + divergence (G t + J t) x = qdot t x + wdot t x) :
    HasDerivAt (fun τ => ∫ x in Icc a b, E τ x)
      (((∫ x in Icc a b, qdot t x) - boxOutwardFlux a b (J t)) -
        ProcessPorts.workOut (∫ x in Icc a b, wdot t x) - boxOutwardFlux a b (G t)) t := by
  have h := hasDerivAt_boxIntegral (u := E) (s := fun τ x => qdot τ x + wdot τ x)
    (q := fun τ => G τ + J τ) hab hU hbox hE (hG.add hJ) (hq.add hw) hlaw
  rw [integral_add hq hw, boxOutwardFlux_add hab hbox hG.continuousOn hJ.continuousOn] at h
  convert h using 1
  unfold ProcessPorts.workOut
  ring

/-- **Two-port energy balance**: inlet on the face `x₀ = a₀` and outlet on `x₀ = b₀`, with
uniform port states whose velocities `vi`, `vo` are vectors of the box's space, and zero normal
component of `G` on the side faces (`hwall`, a hypothesis on the flux `G` only, with no wall
velocity or relation `G = (E + p) v`; for that flux it holds on impermeable walls). Each port's
mass flow and kinetic energy come from its one velocity vector: the storage rate is
`Q̇ - Ẇ_out + ṁ_in θ_in - ṁ_out θ_out` with `ṁ = ρ A₀ v₀`, the component `v₀` of the port velocity
along `e₀`, and `θ = h + |v|² / 2 + g z`. -/
lemma hasDerivAt_energy_twoPort {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {E qdot wdot : ℝ → (Fin (n + 1) → ℝ) → ℝ}
    {G J : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hE : ContDiff ℝ 1 (Function.uncurry E)) (hG : ContDiffOn ℝ 1 (G t) U)
    (hJ : ContDiffOn ℝ 1 (J t) U) (hq : IntegrableOn (qdot t) (Icc a b))
    (hw : IntegrableOn (wdot t) (Icc a b))
    (hlaw : ∀ x ∈ Icc a b,
      deriv (fun τ => E τ x) t + divergence (G t + J t) x = qdot t x + wdot t x)
    {g ρi ei pi zi ρo eo po zo : ℝ} {vi vo : Fin (n + 1) → ℝ}
    (hρi : ρi ≠ 0) (hρo : ρo ≠ 0)
    (hin : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      G t ((0 : Fin (n + 1)).insertNth (a 0) y) 0 =
        vi 0 * (ρi * (ei + vi ⬝ᵥ vi / 2 + g * zi) + pi))
    (hout : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      G t ((0 : Fin (n + 1)).insertNth (b 0) y) 0 =
        vo 0 * (ρo * (eo + vo ⬝ᵥ vo / 2 + g * zo) + po))
    (hwall : ∀ i, i ≠ 0 → ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      G t (i.insertNth (b i) y) i = 0 ∧ G t (i.insertNth (a i) y) i = 0) :
    HasDerivAt (fun τ => ∫ x in Icc a b, E τ x)
      (((∫ x in Icc a b, qdot t x) - boxOutwardFlux a b (J t)) -
          ProcessPorts.workOut (∫ x in Icc a b, wdot t x) +
        ρi * faceArea a b 0 * vi 0 * (specificEnthalpy ei pi ρi + vi ⬝ᵥ vi / 2 + g * zi) -
        ρo * faceArea a b 0 * vo 0 * (specificEnthalpy eo po ρo + vo ⬝ᵥ vo / 2 + g * zo)) t := by
  have h := hasDerivAt_energy_box hab hU hbox hE hG hJ hq hw hlaw
  have hflux : boxOutwardFlux a b (G t) =
      faceArea a b 0 * (vo 0 * (ρo * (eo + vo ⬝ᵥ vo / 2 + g * zo) + po) -
        vi 0 * (ρi * (ei + vi ⬝ᵥ vi / 2 + g * zi) + pi)) := by
    rw [boxOutwardFlux_uniform hab
      (cU := fun i => if i = 0 then vo 0 * (ρo * (eo + vo ⬝ᵥ vo / 2 + g * zo) + po) else 0)
      (cL := fun i => if i = 0 then vi 0 * (ρi * (ei + vi ⬝ᵥ vi / 2 + g * zi) + pi) else 0)]
    · rw [Fin.sum_univ_succ]
      simp
    · intro i y hy
      by_cases hi : i = 0
      · subst hi; simp only [ite_true]; exact hout y hy
      · simp only [hi, ite_false]; exact (hwall i hi y hy).1
    · intro i y hy
      by_cases hi : i = 0
      · subst hi; simp only [ite_true]; exact hin y hy
      · simp only [hi, ite_false]; exact (hwall i hi y hy).2
  rw [hflux] at h
  convert h using 1
  unfold specificEnthalpy
  field_simp
  ring

end EnergyPorts

section MomentumPorts

open Set MeasureTheory
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## D. Momentum ports -/

/-! ### D.1. Momentum flux and face tractions -/

/-- The flux of the `j`-th momentum component for the density `ρ`, the velocity `v` and the Cauchy
stress `σ`, with `σ x j i` the `j`-th traction component on a surface of unit normal `eᵢ`: its
`i`-th component `ρ vⱼ vᵢ - σ x j i` is the convective transport of `j`-momentum across a face
normal to `eᵢ` minus the surface force on it. -/
noncomputable def momentumFlux {n : ℕ} (ρ : (Fin (n + 1) → ℝ) → ℝ)
    (v : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (σ : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ρ x * v x j * v x i - σ x j i

/-- The resultant of the traction `σ n` over the two faces of the box `[a, b]` normal to `eᵢ`: the
integral of the column `σ (·) (·) i` over the upper face `x i = b i` (outward normal `+eᵢ`) minus
its integral over the lower face `x i = a i` (outward normal `-eᵢ`), both over the box of the
remaining coordinates. -/
noncomputable def faceTractionResultant {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (σ : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  fun j => (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), σ (i.insertNth (b i) y) j i) -
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), σ (i.insertNth (a i) y) j i

/-! ### D.2. The momentum balance -/

/-- The momentum density components are jointly `C¹`. -/
private lemma contDiff_momentumDensity {n : ℕ} {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ}
    {v : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hρ : ContDiff ℝ 1 (Function.uncurry ρ))
    (hv : ContDiff ℝ 1 (Function.uncurry v)) (j : Fin (n + 1)) :
    ContDiff ℝ 1 (Function.uncurry fun τ x => ρ τ x * v τ x j) :=
  hρ.mul ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) j).comp hv)

/-- The slices of a jointly `C¹` field at a fixed time are `C¹`. -/
private lemma contDiff_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℝ → (Fin (n + 1) → ℝ) → E} (hw : ContDiff ℝ 1 (Function.uncurry w)) (t : ℝ) :
    ContDiff ℝ 1 (w t) :=
  hw.comp (contDiff_const.prodMk contDiff_id)

/-- The momentum flux is `C¹` on `U`. -/
private lemma contDiffOn_momentumFlux {n : ℕ} {ρ : (Fin (n + 1) → ℝ) → ℝ}
    {v : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {U : Set (Fin (n + 1) → ℝ)}
    (hρ : ContDiff ℝ 1 ρ) (hv : ContDiff ℝ 1 v) (hσ : ContDiffOn ℝ 1 σ U) (j : Fin (n + 1)) :
    ContDiffOn ℝ 1 (momentumFlux ρ v σ j) U := by
  refine contDiffOn_pi.2 fun i => ?_
  have h1 : ContDiffOn ℝ 1 (fun x => σ x j i) U := contDiffOn_pi.1 (contDiffOn_pi.1 hσ j) i
  have h2 : ContDiff ℝ 1 (fun x => ρ x * v x j * v x i) :=
    (hρ.mul ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) j).comp hv)).mul
      ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin (n + 1) => ℝ) i).comp hv)
  exact h2.contDiffOn.sub h1

/-- **The fixed-box balance applied to each momentum component.** For a nondegenerate box, jointly
`C¹` density `ρ` and velocity `v`, a stress `σ t` of class `C¹` on an open neighbourhood of the
box, integrable body force components and the local Cauchy law
`∂ₜ(ρ vⱼ) + div (momentumFlux ρ v σ j) = fⱼ` on the box at time `t`, the momentum
`P = ∫_[a, b] ρ v` satisfies
`P' = (∫_[a, b] fⱼ - boxOutwardFlux a b (momentumFlux (ρ t) (v t) (σ t) j))ⱼ`. -/
lemma hasDerivAt_momentum_box {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ} {v f : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hσ : ContDiffOn ℝ 1 (σ t) U) (hf : ∀ j, IntegrableOn (fun x => f t x j) (Icc a b))
    (hlaw : ∀ j, ∀ x ∈ Icc a b,
      deriv (fun τ => ρ τ x * v τ x j) t + divergence (momentumFlux (ρ t) (v t) (σ t) j) x =
        f t x j) :
    HasDerivAt (fun τ => fun j => ∫ x in Icc a b, ρ τ x * v τ x j)
      (fun j => (∫ x in Icc a b, f t x j) -
        boxOutwardFlux a b (momentumFlux (ρ t) (v t) (σ t) j)) t := by
  refine hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_boxIntegral (u := fun τ x => ρ τ x * v τ x j) (s := fun τ x => f τ x j)
    (q := fun τ => momentumFlux (ρ τ) (v τ) (σ τ) j) hab hU hbox
    (contDiff_momentumDensity hρ hv j)
    (contDiffOn_momentumFlux (contDiff_slice hρ t) (contDiff_slice hv t) hσ j) (hf j) (hlaw j)

/-- **Momentum balance with the boundary traction.** Under the hypotheses of
`hasDerivAt_momentum_box`, the momentum changes at the rate body force plus the resultant of the
boundary traction `σ n` over all faces minus the momentum outflow:
`P' = ∫ f + ∑ᵢ faceTractionResultant a b (σ t) i - (boxOutwardFlux a b (ρ vⱼ v))ⱼ`. -/
lemma hasDerivAt_momentum_box_traction {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ} {v f : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hσ : ContDiffOn ℝ 1 (σ t) U) (hf : ∀ j, IntegrableOn (fun x => f t x j) (Icc a b))
    (hlaw : ∀ j, ∀ x ∈ Icc a b,
      deriv (fun τ => ρ τ x * v τ x j) t + divergence (momentumFlux (ρ t) (v t) (σ t) j) x =
        f t x j) :
    HasDerivAt (fun τ => fun j => ∫ x in Icc a b, ρ τ x * v τ x j)
      ((fun j => ∫ x in Icc a b, f t x j) + ∑ i, faceTractionResultant a b (σ t) i -
        fun j => boxOutwardFlux a b (fun x i => ρ t x * v t x j * v t x i)) t := by
  have h := hasDerivAt_momentum_box hab hU hbox hρ hv hσ hf hlaw
  convert h using 1
  funext j
  have hρt : Continuous (ρ t) := (contDiff_slice hρ t).continuous
  have hvt : Continuous (v t) := (contDiff_slice hv t).continuous
  have hconv : ContinuousOn (fun x i => ρ t x * v t x j * v t x i) U := by
    refine Continuous.continuousOn (continuous_pi fun i => ?_)
    exact (hρt.mul ((continuous_apply j).comp hvt)).mul ((continuous_apply i).comp hvt)
  have hneg : ContinuousOn (fun x i => -σ t x j i) U :=
    continuousOn_pi.2 fun i => ((continuousOn_pi.1 (continuousOn_pi.1 hσ.continuousOn j)) i).neg
  have hsplit : momentumFlux (ρ t) (v t) (σ t) j =
      (fun x i => ρ t x * v t x j * v t x i) + (fun x i => -σ t x j i) := by
    funext x i
    simp [momentumFlux, sub_eq_add_neg]
  have hnegflux : boxOutwardFlux a b (fun x i => -σ t x j i) =
      -∑ i, faceTractionResultant a b (σ t) i j := by
    unfold boxOutwardFlux faceTractionResultant
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_neg, integral_neg]
    ring
  rw [hsplit, boxOutwardFlux_add hab hbox hconv hneg, hnegflux]
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  ring

/-! ### D.3. Two ports with pressure and viscous tractions -/

/-- **Two-port momentum balance with viscous port tractions.** Inlet on the face `x₀ = a₀`
(outward normal `-e₀`), outlet on the face `x₀ = b₀` (outward normal `+e₀`), impermeable side
walls (`hwall`: zero normal velocity on every face normal to `eᵢ`, `i ≠ 0`). On each port face the
density and velocity are uniform and the traction column is `σ e₀ = -p e₀ + τ`, a pressure `p` and
a uniform viscous traction `τ`. Then, with `ṁ = ρ A₀ v₀` at each port and `F_wall` the traction
resultant of the walls,
`P' = ṁ_in v_in - ṁ_out v_out - (p_in A₀ (-e₀) + p_out A₀ e₀) + F_body + F_wall`
`+ A₀ (τ_out - τ_in)`. The last term is where viscous port tractions enter: the vector `τ` is the
viscous part of the traction on a surface of unit normal `+e₀`, so the outlet face (outward normal
`+e₀`) carries the viscous traction `τ_out` and the inlet face (outward normal `-e₀`) carries
`-τ_in`. -/
lemma hasDerivAt_momentum_twoPort_viscous {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ} {v f : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hσ : ContDiffOn ℝ 1 (σ t) U) (hf : ∀ j, IntegrableOn (fun x => f t x j) (Icc a b))
    (hlaw : ∀ j, ∀ x ∈ Icc a b,
      deriv (fun τ => ρ τ x * v τ x j) t + divergence (momentumFlux (ρ t) (v t) (σ t) j) x =
        f t x j)
    {ρi ρo pi po : ℝ} {vi vo τi τo : Fin (n + 1) → ℝ}
    (hρi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (a 0) y) = ρi)
    (hvi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (a 0) y) = vi)
    (hσi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (a 0) y) j 0) = -(pi • Pi.single 0 1) + τi)
    (hρo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (b 0) y) = ρo)
    (hvo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (b 0) y) = vo)
    (hσo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (b 0) y) j 0) = -(po • Pi.single 0 1) + τo)
    (hwall : ∀ i, i ≠ 0 → ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      v t (i.insertNth (b i) y) i = 0 ∧ v t (i.insertNth (a i) y) i = 0) :
    HasDerivAt (fun τ => fun j => ∫ x in Icc a b, ρ τ x * v τ x j)
      ((ρi * faceArea a b 0 * vi 0) • vi - (ρo * faceArea a b 0 * vo 0) • vo -
          ((pi * faceArea a b 0) • -(Pi.single 0 1 : Fin (n + 1) → ℝ) +
            (po * faceArea a b 0) • (Pi.single 0 1 : Fin (n + 1) → ℝ)) +
          (fun j => ∫ x in Icc a b, f t x j) + ∑ i : Fin n, faceTractionResultant a b (σ t) i.succ +
        faceArea a b 0 • (τo - τi)) t := by
  have h := hasDerivAt_momentum_box_traction hab hU hbox hρ hv hσ hf hlaw
  have hle : a ≤ b := fun i => (hab i).le
  have hface0 : (a ∘ (0 : Fin (n + 1)).succAbove) ≤ (b ∘ (0 : Fin (n + 1)).succAbove) :=
    fun k => hle _
  have hvol : volume.real (Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove))
      = faceArea a b 0 := by
    rw [measureReal_def, Real.volume_Icc_pi_toReal hface0]
    simp [faceArea]
  have hT0 : faceTractionResultant a b (σ t) 0 =
      faceArea a b 0 • ((-(po • Pi.single 0 1) + τo) - (-(pi • Pi.single 0 1) + τi)) := by
    funext j
    unfold faceTractionResultant
    rw [setIntegral_congr_fun measurableSet_Icc (fun y hy => congrFun (hσo y hy) j),
      setIntegral_congr_fun measurableSet_Icc (fun y hy => congrFun (hσi y hy) j),
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, hvol]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hout : (fun j => boxOutwardFlux a b (fun x i => ρ t x * v t x j * v t x i)) =
      (ρo * faceArea a b 0 * vo 0) • vo - (ρi * faceArea a b 0 * vi 0) • vi := by
    funext j
    rw [boxOutwardFlux_uniform hab
      (cU := fun i => if i = 0 then ρo * vo j * vo 0 else 0)
      (cL := fun i => if i = 0 then ρi * vi j * vi 0 else 0)]
    · rw [Fin.sum_univ_succ]
      simp only [ite_true, Fin.succ_ne_zero, ite_false, sub_self, mul_zero,
        Finset.sum_const_zero, add_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro i y hy
      by_cases hi : i = 0
      · subst hi
        simp only [ite_true]
        rw [hρo y hy, hvo y hy]
      · simp only [hi, ite_false]
        rw [(hwall i hi y hy).1, mul_zero]
    · intro i y hy
      by_cases hi : i = 0
      · subst hi
        simp only [ite_true]
        rw [hρi y hy, hvi y hy]
      · simp only [hi, ite_false]
        rw [(hwall i hi y hy).2, mul_zero]
  rw [Fin.sum_univ_succ, hT0, hout] at h
  convert h using 1
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- **Two-port momentum balance with pressure-only port tractions.** Under the hypotheses of
`hasDerivAt_momentum_twoPort_viscous` with `σ e₀ = -p e₀` on both port faces,
`P' = ṁ_in v_in - ṁ_out v_out - ∑_ports p A n + F_body + F_wall`, where `n_in = -e₀`,
`n_out = +e₀`, `ṁ = ρ A₀ v₀` at each port and `F_wall`, the traction resultant of the walls,
includes the wall pressure and shear. -/
lemma hasDerivAt_momentum_twoPort {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {ρ : ℝ → (Fin (n + 1) → ℝ) → ℝ} {v f : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hv : ContDiff ℝ 1 (Function.uncurry v))
    (hσ : ContDiffOn ℝ 1 (σ t) U) (hf : ∀ j, IntegrableOn (fun x => f t x j) (Icc a b))
    (hlaw : ∀ j, ∀ x ∈ Icc a b,
      deriv (fun τ => ρ τ x * v τ x j) t + divergence (momentumFlux (ρ t) (v t) (σ t) j) x =
        f t x j)
    {ρi ρo pi po : ℝ} {vi vo : Fin (n + 1) → ℝ}
    (hρi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (a 0) y) = ρi)
    (hvi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (a 0) y) = vi)
    (hσi : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (a 0) y) j 0) = -(pi • Pi.single 0 1))
    (hρo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      ρ t ((0 : Fin (n + 1)).insertNth (b 0) y) = ρo)
    (hvo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      v t ((0 : Fin (n + 1)).insertNth (b 0) y) = vo)
    (hσo : ∀ y ∈ Icc (a ∘ (0 : Fin (n + 1)).succAbove) (b ∘ (0 : Fin (n + 1)).succAbove),
      (fun j => σ t ((0 : Fin (n + 1)).insertNth (b 0) y) j 0) = -(po • Pi.single 0 1))
    (hwall : ∀ i, i ≠ 0 → ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      v t (i.insertNth (b i) y) i = 0 ∧ v t (i.insertNth (a i) y) i = 0) :
    HasDerivAt (fun τ => fun j => ∫ x in Icc a b, ρ τ x * v τ x j)
      ((ρi * faceArea a b 0 * vi 0) • vi - (ρo * faceArea a b 0 * vo 0) • vo -
          ((pi * faceArea a b 0) • -(Pi.single 0 1 : Fin (n + 1) → ℝ) +
            (po * faceArea a b 0) • (Pi.single 0 1 : Fin (n + 1) → ℝ)) +
          (fun j => ∫ x in Icc a b, f t x j) +
        ∑ i : Fin n, faceTractionResultant a b (σ t) i.succ) t := by
  have h := hasDerivAt_momentum_twoPort_viscous (τi := 0) (τo := 0) hab hU hbox hρ hv hσ hf hlaw
    hρi hvi (fun y hy => by rw [hσi y hy, add_zero]) hρo hvo
    (fun y hy => by rw [hσo y hy, add_zero]) hwall
  rw [sub_self, smul_zero, add_zero] at h
  exact h

end MomentumPorts

end ControlVolumes
