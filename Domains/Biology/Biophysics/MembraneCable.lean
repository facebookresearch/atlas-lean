/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.SteadyCableTransfer
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Nernst equilibrium potential and the steady-state passive cable

Two classical results of membrane biophysics, with the physical constants kept as parameters:
gas constant `R`, absolute temperature `T`, ion valence `z` and Faraday constant `F`.

## Nernst equilibrium

The Nernst potential (`nernstPotential`) of one ion species with inside concentration `c_in` and
outside concentration `c_out` is

  `E = (R T / (z F)) log (c_out / c_in)`,

the inside-minus-outside voltage. It is derived in two ways:

* `electrochemicalPotential_eq_iff`: the molar electrochemical potentials
  `μ̃ = μ₀ + R T log c + z F φ` inside and outside agree iff `φ_in - φ_out = E`;
* `sub_eq_nernstPotential_of_flux_eq_zero`: across a membrane `[0, L]` (inside at `0`), zero
  one-dimensional Nernst–Planck flux `J = -D (c' + (z F / (R T)) c φ')` forces `φ 0 - φ L = E`.

Further: `nernstPotential_self`, `nernstPotential_swap`, `nernstPotential_neg_valence`,
`nernstPotential_pos_iff` (sign), and the Boltzmann form `div_eq_exp_nernstPotential`.

## Steady-state passive cable

`IsSteadyState rm ri s V I` is the steady-state core-conductor system `V' = -ri I`,
`I' = -V / rm` on a set of positions `s`, with membrane resistance `rm` (times unit length),
axial resistance `ri` (per unit length), membrane voltage `V` measured from rest and axial current
`I`. With length constant `λ = sqrt (rm / ri)` (`lengthConstant`) and characteristic resistance
`r∞ = sqrt (rm ri) = ri λ` (`charResistance`):

* `IsSteadyState.hasDerivWithinAt_voltage_deriv`: eliminating `I` gives `λ² V'' = V`;
* `isSteadyState_cable`, `IsSteadyState.eq_cable_Icc`: on `[0, L]` the steady states are exactly
  `V x = V₀ cosh (x/λ) - r∞ I₀ sinh (x/λ)`, `I x = I₀ cosh (x/λ) - (V₀/r∞) sinh (x/λ)`;
* `exists_isSteadyState_exp_iff`: an exponential profile `c e^{-a x}` (`c ≠ 0`, `a > 0`) is a
  steady state iff `a = 1/λ`, which derives the length constant;
* boundary conditions:
  - semi-infinite cable `[0, ∞)` with bounded voltage (`IsSteadyState.eq_exp_of_bounded`):
    `V x = V 0 e^{-x/λ}`, `I x = I 0 e^{-x/λ}`, input resistance `V 0 = r∞ I 0`;
    current injection `I 0 = I₀` gives `V x = r∞ I₀ e^{-x/λ}`
    (`IsSteadyState.voltage_eq_of_current_injection`), and `V (x + λ) = e⁻¹ V x`
    (`IsSteadyState.voltage_add_lengthConstant`);
  - finite cable `[0, L]` with a sealed end `I L = 0` (`IsSteadyState.sealedEnd`):
    `V x = V 0 cosh ((L - x)/λ) / cosh (L/λ)`, input relation `V 0 = r∞ coth (L/λ) I 0`
    (`IsSteadyState.sealedEnd_input`), end attenuation `V L = V 0 / cosh (L/λ)`.

Only the steady state is treated: the time-dependent cable equation `λ² V_xx = τ V_t + V`, the
Goldman–Hodgkin–Katz equation for several species and active (Hodgkin–Huxley) membranes are out
of scope of this file.

## References

* B. Hille, *Ion Channels of Excitable Membranes*, 3rd ed., Sinauer (2001), ch. 1 and 14.
* C. Koch, *Biophysics of Computation*, Oxford University Press (1999), ch. 2.
* J. Keener and J. Sneyd, *Mathematical Physiology I*, 2nd ed., Springer (2009), §3.1 and §4.1.
-/

@[expose] public section

open Real Set Filter Topology

namespace MathlibExt.Biology.Biophysics.MembraneCable

/-! ### Nernst equilibrium potential -/

/-- Nernst potential `E = (R T / (z F)) log (c_out / c_in)` of one ion species of valence `z`,
with gas constant `R`, absolute temperature `T`, Faraday constant `F`, inside concentration
`cIn` and outside concentration `cOut`. It is the inside-minus-outside membrane voltage at which
the species is in electrochemical equilibrium (`electrochemicalPotential_eq_iff`,
`sub_eq_nernstPotential_of_flux_eq_zero`), in the model with `R, T, F, cIn, cOut > 0` and `z ≠ 0`.
The formula is total: with `u / 0 = 0`, `log 0 = 0` and `log u = log |u|`, it is `0` when
`z F = 0`, `cIn = 0` or `cOut = 0`. -/
noncomputable def nernstPotential (R T z F cIn cOut : ℝ) : ℝ := R * T / (z * F) * log (cOut / cIn)

/-- Molar electrochemical potential `μ̃ = μ₀ + R T log c + z F φ` of an ion species of valence `z`
at concentration `c` and electric potential `φ`, with standard chemical potential `μ₀`. With
`log 0 = 0` it is `μ₀ + z F φ` at `c = 0`; in the model `c > 0`. -/
noncomputable def electrochemicalPotential (R T z F μ₀ c φ : ℝ) : ℝ :=
  μ₀ + R * T * log c + z * F * φ

/-- One-dimensional Nernst–Planck flux `J = -D (c' + (z F / (R T)) c φ')` of an ion species with
diffusion coefficient `D`, at a point where the concentration is `c`, its gradient is `dc` and the
electric-potential gradient is `dφ`: Fickian diffusion plus electrical drift. With `u / 0 = 0`
the drift term vanishes when `R T = 0`. -/
noncomputable def nernstPlanckFlux (D R T z F c dc dφ : ℝ) : ℝ :=
  -D * (dc + z * F / (R * T) * c * dφ)

/-- For `z F ≠ 0` and positive concentrations `cIn`, `cOut`, equal electrochemical potentials
inside (`cIn`, `φIn`) and outside (`cOut`, `φOut`), with the same `μ₀`, is equivalent to the
membrane voltage `φIn - φOut` being the Nernst potential. -/
theorem electrochemicalPotential_eq_iff {R T z F μ₀ cIn cOut φIn φOut : ℝ} (hzF : z * F ≠ 0)
    (hIn : 0 < cIn) (hOut : 0 < cOut) :
    electrochemicalPotential R T z F μ₀ cIn φIn = electrochemicalPotential R T z F μ₀ cOut φOut ↔
      φIn - φOut = nernstPotential R T z F cIn cOut := by
  unfold electrochemicalPotential nernstPotential
  rw [log_div hOut.ne' hIn.ne', div_mul_eq_mul_div, eq_div_iff hzF]
  constructor <;> intro h <;> linear_combination h

/-- **Nernst equilibrium from zero Nernst–Planck flux.** Let `D ≠ 0`, `R T ≠ 0`, `z F ≠ 0` and
`L ≥ 0`. Across a membrane `[0, L]` with the
inside at `x = 0` and the outside at `x = L`, if the concentration `c > 0` and the potential `φ`
have derivatives `c'`, `φ'` within `[0, L]` and the Nernst–Planck flux vanishes throughout, then
the membrane voltage `φ 0 - φ L` is the Nernst potential of the boundary concentrations. -/
theorem sub_eq_nernstPotential_of_flux_eq_zero {D R T z F L : ℝ} {c c' φ φ' : ℝ → ℝ}
    (hD : D ≠ 0) (hRT : R * T ≠ 0) (hzF : z * F ≠ 0) (hL : 0 ≤ L)
    (hc : ∀ x ∈ Icc 0 L, 0 < c x) (hc' : ∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x)
    (hφ' : ∀ x ∈ Icc 0 L, HasDerivWithinAt φ (φ' x) (Icc 0 L) x)
    (hJ : ∀ x ∈ Icc 0 L, nernstPlanckFlux D R T z F (c x) (c' x) (φ' x) = 0) :
    φ 0 - φ L = nernstPotential R T z F (c 0) (c L) := by
  set k := z * F / (R * T) with hk
  have hderiv : ∀ x ∈ Icc 0 L,
      HasDerivWithinAt (fun x ↦ log (c x) + k * φ x) 0 (Icc 0 L) x := by
    intro x hx
    have hJx : c' x + k * c x * φ' x = 0 := by
      have := hJ x hx
      unfold nernstPlanckFlux at this
      simpa [hD] using this
    have h := ((hc' x hx).log (hc x hx).ne').add ((hφ' x hx).const_mul k)
    convert h using 1
    field_simp [(hc x hx).ne']
    linear_combination -hJx
  have hconst := eq_of_hasDerivWithinAt_zero hderiv L ⟨hL, le_rfl⟩
  have h0 := hc 0 ⟨le_rfl, hL⟩
  have hL' := hc L ⟨hL, le_rfl⟩
  unfold nernstPotential
  rw [log_div hL'.ne' h0.ne']
  have hkne : k ≠ 0 := div_ne_zero hzF hRT
  have : R * T / (z * F) = k⁻¹ := by rw [hk, inv_div]
  rw [this]
  field_simp
  linear_combination -hconst

/-- Equal concentrations give zero Nernst potential, for every real `c` (at `c = 0` because
`0 / 0 = 0` and `log 0 = 0`). -/
@[simp] theorem nernstPotential_self (R T z F c : ℝ) : nernstPotential R T z F c c = 0 := by
  by_cases hc : c = 0 <;> simp [nernstPotential, hc]

/-- Exchanging the inside and outside concentrations reverses the sign of the Nernst potential,
for all real arguments (`log (1 / u) = -log u` also at `u = 0` under the conventions). -/
theorem nernstPotential_swap (R T z F cIn cOut : ℝ) :
    nernstPotential R T z F cOut cIn = -nernstPotential R T z F cIn cOut := by
  unfold nernstPotential
  rw [show cIn / cOut = (cOut / cIn)⁻¹ from (inv_div _ _).symm, log_inv]; ring

/-- Reversing the valence reverses the sign of the Nernst potential, for all real arguments (at
`z F = 0` both sides are `0`). -/
theorem nernstPotential_neg_valence (R T z F cIn cOut : ℝ) :
    nernstPotential R T (-z) F cIn cOut = -nernstPotential R T z F cIn cOut := by
  unfold nernstPotential
  rw [neg_mul, div_neg, neg_mul]

/-- With `R T > 0` and `z F > 0` (a cation, positive Faraday constant) and positive
concentrations, the Nernst potential is positive exactly when the outside concentration exceeds
the inside one. -/
theorem nernstPotential_pos_iff {R T z F cIn cOut : ℝ} (hRT : 0 < R * T) (hzF : 0 < z * F)
    (hIn : 0 < cIn) (hOut : 0 < cOut) :
    0 < nernstPotential R T z F cIn cOut ↔ cIn < cOut := by
  unfold nernstPotential
  rw [mul_pos_iff_of_pos_left (div_pos hRT hzF), log_pos_iff (div_pos hOut hIn).le,
    one_lt_div hIn]

/-- **Boltzmann form.** For `R T ≠ 0`, `z F ≠ 0` and positive concentrations, at the Nernst
potential `E` the concentration ratio is `c_out / c_in = exp (z F E / (R T))`. -/
theorem div_eq_exp_nernstPotential {R T z F cIn cOut : ℝ} (hRT : R * T ≠ 0) (hzF : z * F ≠ 0)
    (hIn : 0 < cIn) (hOut : 0 < cOut) :
    cOut / cIn = exp (z * F / (R * T) * nernstPotential R T z F cIn cOut) := by
  unfold nernstPotential
  rw [← mul_assoc, div_mul_div_comm, mul_comm (z * F), div_self (mul_ne_zero hRT hzF), one_mul,
    exp_log (div_pos hOut hIn)]

/-! ### Steady-state passive cable

A passive cylindrical cable has membrane resistance `rm` (resistance times length) and axial
(core) resistance `ri` (resistance per unit length). With `V(x)` the membrane voltage measured
from rest and `I(x)` the axial current in the direction of increasing `x`, the steady-state
core-conductor equations are

  `V' = -ri I`   (Ohm's law along the core),
  `I' = -V / rm` (the axial current decreases by the passive membrane current `V / rm`).

Eliminating `I` gives the steady-state cable equation `λ² V'' = V` with length constant
`λ = sqrt (rm / ri)`. -/

section Cable

variable {rm ri : ℝ}

/-- Time constant `tau = rm * cm` of a passive cable with membrane
resistance `rm` (resistance times length) and membrane
capacitance `cm` per unit length, so the product has units of
time. -/
noncomputable def timeConstant (rm cm : ℝ) : ℝ := rm * cm

/-- The cable time constant is positive for positive parameters. -/
theorem timeConstant_pos {cm : ℝ} (hm : 0 < rm) (hcm : 0 < cm) :
    0 < timeConstant rm cm :=
  mul_pos hm hcm

/-- **Sealed end.** For `ri ≠ 0`, at a point of the cable with unique spatial
derivative within the cable set, the axial current vanishes
exactly when the within-set voltage spatial derivative vanishes:
a sealed end is the zero-derivative boundary condition. -/
theorem sealed_end_iff {s : Set ℝ} {V I : ℝ → ℝ} (h : IsSteadyState rm ri s V I)
    (hri : ri ≠ 0) {x : ℝ} (hx : x ∈ s)
    (hu : UniqueDiffWithinAt ℝ s x) :
    I x = 0 ↔ derivWithin V s x = 0 := by
  have hv := h.hasDerivWithinAt_voltage x hx
  have hderiv : derivWithin V s x = -(ri * I x) := hv.derivWithin hu
  rw [hderiv]
  constructor
  · intro hI
    rw [hI, mul_zero, neg_zero]
  · intro h0
    have h2 : ri * I x = 0 := by linarith [h0]
    exact (mul_eq_zero.mp h2).resolve_left hri

/-- `r∞ = rm / λ` for `rm, ri > 0` (the same value as `r∞ = ri λ`, as `λ² = rm / ri`). -/
theorem charResistance_eq_div (hm : 0 < rm) (hi : 0 < ri) :
    charResistance rm ri = rm / lengthConstant rm ri := by
  have hl := (lengthConstant_pos hm hi).ne'
  rw [charResistance_eq hm hi, eq_div_iff hl]
  linear_combination mul_lengthConstant_sq hm hi

/-- **The steady-state cable equation.** For `rm, ri > 0`, eliminating the axial current: the
voltage gradient
`V' = -ri I` has derivative `V / λ²`, i.e. `λ² V'' = V`. -/
theorem IsSteadyState.hasDerivWithinAt_voltage_deriv {s : Set ℝ} {V I : ℝ → ℝ}
    (h : IsSteadyState rm ri s V I) (hm : 0 < rm) (hi : 0 < ri) {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt (fun y ↦ -(ri * I y)) (V x / lengthConstant rm ri ^ 2) s x := by
  convert ((h.hasDerivWithinAt_current x hx).const_mul ri).neg using 1
  rw [lengthConstant_sq hm hi]; field_simp

/-- A steady state on `s` restricts to a steady state on any `t ⊆ s`. -/
theorem IsSteadyState.mono {s t : Set ℝ} {V I : ℝ → ℝ} (h : IsSteadyState rm ri s V I)
    (hts : t ⊆ s) : IsSteadyState rm ri t V I :=
  ⟨fun x hx ↦ (h.hasDerivWithinAt_voltage x (hts hx)).mono hts,
    fun x hx ↦ (h.hasDerivWithinAt_current x (hts hx)).mono hts⟩

/-- With `V₀ = r∞ I₀` the transfer-form voltage is the pure decaying exponential
`r∞ I₀ e^{-x/λ}`. -/
theorem cableVoltage_charResistance_mul (I₀ x : ℝ) :
    cableVoltage rm ri (charResistance rm ri * I₀) I₀ x =
      charResistance rm ri * I₀ * exp (-(x / lengthConstant rm ri)) := by
  rw [cableVoltage, ← cosh_sub_sinh]; ring

/-- For `rm, ri > 0`, with `V₀ = r∞ I₀` the transfer-form current is the pure decaying
exponential `I₀ e^{-x/λ}`. -/
theorem cableCurrent_charResistance_mul (hm : 0 < rm) (hi : 0 < ri) (I₀ x : ℝ) :
    cableCurrent rm ri (charResistance rm ri * I₀) I₀ x =
      I₀ * exp (-(x / lengthConstant rm ri)) := by
  rw [cableCurrent, ← cosh_sub_sinh, mul_div_cancel_left₀ _ (charResistance_pos hm hi).ne']; ring

/-- **Semi-infinite cable (bounded at infinity).** For `rm, ri > 0`, a steady state on `[0, ∞)`
whose voltage is bounded satisfies the input relation `V 0 = r∞ I 0` and decays exponentially
with length constant `λ`: `V x = V 0 e^{-x/λ}` and `I x = I 0 e^{-x/λ}` for `x ≥ 0`. -/
theorem IsSteadyState.eq_exp_of_bounded {V I : ℝ → ℝ} (h : IsSteadyState rm ri (Ici 0) V I)
    (hm : 0 < rm) (hi : 0 < ri) (hB : ∃ M, ∀ x, 0 ≤ x → |V x| ≤ M) :
    V 0 = charResistance rm ri * I 0 ∧ ∀ x, 0 ≤ x →
      V x = V 0 * exp (-(x / lengthConstant rm ri)) ∧
        I x = I 0 * exp (-(x / lengthConstant rm ri)) := by
  obtain ⟨M, hM⟩ := hB
  have hl := lengthConstant_pos hm hi
  have hsol : ∀ x, 0 ≤ x →
      V x = cableVoltage rm ri (V 0) (I 0) x ∧ I x = cableCurrent rm ri (V 0) (I 0) x :=
    fun x hx ↦ (h.mono Icc_subset_Ici_self).eq_cable_Icc hm hi ⟨hx, le_rfl⟩
  set l := lengthConstant rm ri with hl_def
  set c := V 0 - charResistance rm ri * I 0
  set d := V 0 + charResistance rm ri * I 0
  have hform : ∀ x, 0 ≤ x → 2 * V x = c * exp (x / l) + d * exp (-(x / l)) := by
    intro x hx
    have hVx := (hsol x hx).1
    rw [cableVoltage, cosh_eq, sinh_eq, ← hl_def] at hVx
    linear_combination 2 * hVx
  have hc : c = 0 := by
    by_contra hc
    have hc' : 0 < |c| := abs_pos.2 hc
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
    have key : ∀ x, 0 ≤ x → |c| * exp (x / l) ≤ 2 * M + |d| := by
      intro x hx
      have hE' : exp (-(x / l)) ≤ 1 := exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hx hl.le))
      have h1 : c * exp (x / l) = 2 * V x - d * exp (-(x / l)) := by
        linear_combination -(hform x hx)
      calc |c| * exp (x / l) = |c * exp (x / l)| := by rw [abs_mul, abs_of_pos (exp_pos _)]
        _ ≤ |2 * V x| + |d * exp (-(x / l))| := by rw [h1]; exact abs_sub _ _
        _ ≤ 2 * M + |d| * 1 := by
          rw [abs_mul, abs_mul, abs_two, abs_of_pos (exp_pos _)]
          gcongr
          exact hM x hx
        _ = 2 * M + |d| := by ring
    set K := (2 * M + |d|) / |c|
    have hK : 0 ≤ K := div_nonneg (by positivity) hc'.le
    have hx0 := key (l * K) (mul_nonneg hl.le hK)
    rw [mul_div_cancel_left₀ _ hl.ne'] at hx0
    have hexp := add_one_le_exp K
    have : |c| * (K + 1) ≤ 2 * M + |d| := hx0.trans' (by gcongr)
    have hcK : |c| * K = 2 * M + |d| := mul_div_cancel₀ _ hc'.ne'
    linarith
  have hV0 : V 0 = charResistance rm ri * I 0 := sub_eq_zero.1 hc
  refine ⟨hV0, fun x hx ↦ ⟨?_, ?_⟩⟩
  · rw [(hsol x hx).1, hV0, cableVoltage_charResistance_mul]
  · rw [(hsol x hx).2, hV0, cableCurrent_charResistance_mul hm hi]

/-- **Current injection into a semi-infinite cable.** If a current `I₀` is injected at `x = 0`
(`I 0 = I₀`) and the voltage stays bounded, then `V x = r∞ I₀ e^{-x/λ}` for `x ≥ 0`
(`rm, ri > 0`). -/
theorem IsSteadyState.voltage_eq_of_current_injection {V I : ℝ → ℝ} {I₀ : ℝ}
    (h : IsSteadyState rm ri (Ici 0) V I) (hm : 0 < rm) (hi : 0 < ri)
    (hB : ∃ M, ∀ x, 0 ≤ x → |V x| ≤ M) (hI₀ : I 0 = I₀) {x : ℝ} (hx : 0 ≤ x) :
    V x = charResistance rm ri * I₀ * exp (-(x / lengthConstant rm ri)) := by
  obtain ⟨hV0, hsol⟩ := h.eq_exp_of_bounded hm hi hB
  rw [(hsol x hx).1, hV0, hI₀]

/-- For `rm, ri > 0`, on a bounded semi-infinite steady state the voltage falls by the factor `e`
over each length constant: `V (x + λ) = e⁻¹ V x` for `x ≥ 0`. -/
theorem IsSteadyState.voltage_add_lengthConstant {V I : ℝ → ℝ}
    (h : IsSteadyState rm ri (Ici 0) V I) (hm : 0 < rm) (hi : 0 < ri)
    (hB : ∃ M, ∀ x, 0 ≤ x → |V x| ≤ M) {x : ℝ} (hx : 0 ≤ x) :
    V (x + lengthConstant rm ri) = exp (-1) * V x := by
  have hl := lengthConstant_pos hm hi
  obtain ⟨-, hsol⟩ := h.eq_exp_of_bounded hm hi hB
  rw [(hsol _ (add_nonneg hx hl.le)).1, (hsol x hx).1, add_div, div_self hl.ne', neg_add,
    exp_add]
  ring

/-- **Sealed-end input resistance.** For `rm, ri, L > 0` and a steady state on `[0, L]` with
`I L = 0`, `V 0 = r∞ coth (L / λ) I 0`. -/
theorem IsSteadyState.sealedEnd_input {L : ℝ} {V I : ℝ → ℝ}
    (h : IsSteadyState rm ri (Icc 0 L) V I) (hm : 0 < rm) (hi : 0 < ri) (hL : 0 < L)
    (hsealed : I L = 0) :
    V 0 = charResistance rm ri * I 0 * cosh (L / lengthConstant rm ri) /
      sinh (L / lengthConstant rm ri) := by
  have hs : 0 < sinh (L / lengthConstant rm ri) :=
    sinh_pos_iff.2 (div_pos hL (lengthConstant_pos hm hi))
  rw [eq_div_iff hs.ne']
  exact (h.sealedEnd hm hi hL hsealed).1

/-- **Sealed-end attenuation.** For `rm, ri, L > 0` and a steady state on `[0, L]` with `I L = 0`,
the voltage at the sealed end is `V L = V 0 / cosh (L / λ)`. -/
theorem IsSteadyState.sealedEnd_voltage_end {L : ℝ} {V I : ℝ → ℝ}
    (h : IsSteadyState rm ri (Icc 0 L) V I) (hm : 0 < rm) (hi : 0 < ri) (hL : 0 < L)
    (hsealed : I L = 0) : V L = V 0 / cosh (L / lengthConstant rm ri) := by
  rw [(h.sealedEnd hm hi hL hsealed).2 L ⟨hL.le, le_rfl⟩, sub_self, zero_div, cosh_zero, mul_one]

/-- **Derivation of the length constant.** For `rm, ri > 0`, a nonzero exponential profile
`V x = c e^{-a x}`,
`a > 0`, is the voltage of a steady state of the core-conductor equations on the whole line
exactly when its decay rate is `a = 1 / λ`, `λ = sqrt (rm / ri)`. -/
theorem exists_isSteadyState_exp_iff (hm : 0 < rm) (hi : 0 < ri) {a c : ℝ} (ha : 0 < a)
    (hc : c ≠ 0) :
    (∃ I, IsSteadyState rm ri univ (fun x ↦ c * exp (-(a * x))) I) ↔
      a = (lengthConstant rm ri)⁻¹ := by
  have hl := lengthConstant_pos hm hi
  have hV : ∀ x, HasDerivAt (fun x ↦ c * exp (-(a * x))) (c * (exp (-(a * x)) * -(a * 1))) x :=
    fun x ↦ ((((hasDerivAt_id x).const_mul a).neg).exp).const_mul c
  constructor
  · rintro ⟨I, h⟩
    have hIx : ∀ x, I x = a * c / ri * exp (-(a * x)) := by
      intro x
      have := (hV x).unique (hasDerivWithinAt_univ.1 (h.hasDerivWithinAt_voltage x trivial))
      field_simp
      linear_combination this
    have hIfun : I = fun x ↦ a * c / ri * exp (-(a * x)) := funext hIx
    have h1 := hasDerivWithinAt_univ.1 (h.hasDerivWithinAt_current 0 trivial)
    rw [hIfun] at h1
    have h2 : HasDerivAt (fun x ↦ a * c / ri * exp (-(a * x)))
        (a * c / ri * (exp (-(a * 0)) * -(a * 1))) 0 :=
      ((((hasDerivAt_id 0).const_mul a).neg).exp).const_mul _
    have h3 := h1.unique h2
    simp only [mul_zero, neg_zero, exp_zero, mul_one] at h3
    have hsq : a ^ 2 = (lengthConstant rm ri)⁻¹ ^ 2 := by
      rw [inv_pow, lengthConstant_sq hm hi, inv_div]
      field_simp at h3
      rw [eq_div_iff hm.ne']
      linear_combination h3
    exact (pow_left_inj₀ ha.le (inv_nonneg.2 hl.le) two_ne_zero).1 hsq
  · rintro rfl
    refine ⟨cableCurrent rm ri (charResistance rm ri * (c / charResistance rm ri))
      (c / charResistance rm ri), ?_⟩
    have hV' : (fun x ↦ c * exp (-((lengthConstant rm ri)⁻¹ * x))) =
        cableVoltage rm ri (charResistance rm ri * (c / charResistance rm ri))
          (c / charResistance rm ri) := by
      funext x
      rw [cableVoltage_charResistance_mul, mul_div_cancel₀ _ (charResistance_pos hm hi).ne',
        div_eq_inv_mul]
    rw [hV']
    exact isSteadyState_cable hm hi univ _ _

end Cable

end MathlibExt.Biology.Biophysics.MembraneCable
