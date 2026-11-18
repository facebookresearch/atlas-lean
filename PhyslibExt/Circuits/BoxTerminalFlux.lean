/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.UniformOhmicBar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Six-face box terminal flux and charge continuity

## i. Overview

An axis-aligned box `Set.Icc a b` in `Fin 3 → ℝ` has six oriented
faces, indexed by `Fin 6`. The enclosed charge is the integral of
a time-dependent charge density over the box, and the outward
current of a face is the flux integral of the outward-normal
component of the current density over that face. From the local
continuity law `∂ρ/∂t + div J = 0` and Mathlib's divergence
theorem on boxes, the enclosed charge changes at minus the total
outward flux of the six faces. When the enclosed charge is
constant, the six outward currents sum to zero; otherwise the
nonzero rate term is kept.

Sections A to C give the face-level interface: each face has a
parameter domain in `ℝ × ℝ` and a scalar outward-normal current
density on it, and the outward current of the face is the flux
integral of that density, using `terminalCurrent` from
`PhyslibExt.Circuits.UniformOhmicBar`. The current density obeys
the local Ohm law from the same module: its normal component is
the conductivity times the outward-normal electric-field
component. `chargeContinuity` names the statement that six
outward fluxes sum to minus a charge rate; section B only
transfers it to terminal currents. Section D embeds the actual
box faces in space with outward orientation signs, derives the
balance, and discharges `chargeContinuity` for the transported
box faces. A uniform through-flow gives opposite currents on the
two end faces, and omitting a face or accumulating charge breaks
the zero-sum conclusion.

## ii. Key results

- `hasDerivAt_enclosedCharge_eq_neg_sum_boxOutwardFlux`: under
  local continuity, the enclosed charge changes at minus the
  total outward flux of the six faces.
- `boxTerminalCurrents_sum_eq_neg_chargeRate`: terminal outward
  currents of the six box faces sum to minus the integral of the
  charge-density rate, the enclosed-charge rate.
- `boxTerminalCurrents_sum_eq_zero_of_constantCharge`: when the
  enclosed charge is constant, the six terminal outward currents
  sum to zero.
- `sum_boxOutwardFlux_eq_integral_divergence`: the six outward
  face fluxes of the box sum to the integral of the divergence.
- `faceFlux_ohmicDensity`: the flux of an ohmic density is the
  conductivity times the flux of the normal field component,
  proved by pulling the constant conductivity out of the face
  integral.
- `faceFlux_of_const`: the flux of a constant density over a
  face is the face area times the constant.

## iii. Table of contents

- A. Faces, flux, and the ohmic density
- B. Transfer of charge continuity to terminal currents
- C. Constant densities, through-flow, and witnesses
- D. The axis-aligned box in three-dimensional space: charge
  continuity derived

## iv. References

- D. J. Griffiths, *Introduction to Electrodynamics*, fourth
  edition, Cambridge University Press, 2017: the continuity
  equation relating current flux through a closed surface to
  the rate of change of the enclosed charge, and Ohm's law
  `J = σE`.

## A. Faces, flux, and the ohmic density

## B. Transfer of charge continuity to terminal currents

## C. Constant densities, through-flow, and witnesses

## D. The axis-aligned box in three-dimensional space: charge
   continuity derived
-/

@[expose] public section

open MeasureTheory

namespace PhyslibExt.Circuits.BoxTerminalFlux

/-! ### A. Faces, flux, and the ohmic density -/

/-- The outward flux through face `f`: the flux integral of the
outward-normal current density over the face domain. -/
noncomputable def faceFlux (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) : ℝ :=
  PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent (D f) (density f)

/-- The ohmic face density: conductivity times the outward-normal
electric-field component, pointwise by the local Ohm law. -/
def ohmicDensity (σ : ℝ) (eDensity : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) :
    (ℝ × ℝ) → ℝ :=
  fun p => PhyslibExt.Circuits.UniformOhmicBar.ohmCurrentDensity σ (eDensity f p)

/-- The charge-continuity statement for six face fluxes: their sum
equals minus `chargeRate`. Results that take it as a premise assume
it; `chargeContinuity_boxOutwardFlux` proves it for the actual box. -/
def chargeContinuity (flux : Fin 6 → ℝ) (chargeRate : ℝ) : Prop :=
  ∑ f : Fin 6, flux f = -chargeRate

/-- The flux of an ohmic density is the conductivity times the flux of
the normal field component. -/
theorem faceFlux_ohmicDensity (σ : ℝ) (D : Fin 6 → Set (ℝ × ℝ))
    (eDensity : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) :
    faceFlux D (ohmicDensity σ eDensity) f = σ * faceFlux D eDensity f := by
  unfold faceFlux ohmicDensity
    PhyslibExt.Circuits.UniformOhmicBar.ohmCurrentDensity
    PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent
  exact MeasureTheory.integral_const_mul _ _

/-! ### B. Transfer of charge continuity to terminal currents -/

/-- Identification of terminal currents with face fluxes transfers the
continuity sum to the terminal currents. -/
lemma sum_terminalCurrent_eq_neg_chargeRate (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (I : Fin 6 → ℝ) (chargeRate : ℝ)
    (hI : ∀ f : Fin 6, I f = faceFlux D density f)
    (hcont : chargeContinuity (faceFlux D density) chargeRate) :
    ∑ f : Fin 6, I f = -chargeRate := by
  have h : ∑ f : Fin 6, I f = ∑ f : Fin 6, faceFlux D density f :=
    Finset.sum_congr rfl fun f _ => hI f
  rw [h]
  exact hcont

/-- With insulating side faces (zero outward flux on faces other than
the two end faces `0` and `1`, a premise and not a default), the balance
reduces to the two end-face currents. -/
lemma endFaceCurrents_add_eq_neg_chargeRate_of_sideFaces_zero
    (I : Fin 6 → ℝ) (chargeRate : ℝ) (hsum : ∑ f : Fin 6, I f = -chargeRate)
    (hside : ∀ f : Fin 6, f ≠ 0 → f ≠ 1 → I f = 0) :
    I 0 + I 1 = -chargeRate := by
  have h2 : I 2 = 0 := hside 2 (by decide) (by decide)
  have h3 : I 3 = 0 := hside 3 (by decide) (by decide)
  have h4 : I 4 = 0 := hside 4 (by decide) (by decide)
  have h5 : I 5 = 0 := hside 5 (by decide) (by decide)
  rw [Fin.sum_univ_six, h2, h3, h4, h5] at hsum
  simpa using hsum

/-! ### C. Constant densities, through-flow, and witnesses -/

/-- The flux of a constant density over a face is `volume.real (D f)`
times the constant. Without finite measure both sides may be junk
zeros (`volume.real` of an infinite measure is `0`, and so is the
integral of a nonintegrable function); `faceFlux_of_const_of_measure_ne_top`
adds finite area, integrability, and the area identity. -/
theorem faceFlux_of_const (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) (k : ℝ)
    (hD : MeasurableSet (D f)) (hk : ∀ p ∈ D f, density f p = k) :
    faceFlux D density f = volume.real (D f) * k := by
  unfold faceFlux PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent
  have hae : (density f) =ᵐ[volume.restrict (D f)] (fun _ => k) := by
    filter_upwards [ae_restrict_mem hD] with p hp using hk p hp
  rw [integral_congr_ae hae, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]

/-- For a face of finite area, a constant density is integrable over
the face, `volume.real (D f)` is the face area, and the flux is that
area times the constant. -/
theorem faceFlux_of_const_of_measure_ne_top (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) (k : ℝ)
    (hD : MeasurableSet (D f)) (hfin : volume (D f) ≠ ⊤)
    (hk : ∀ p ∈ D f, density f p = k) :
    IntegrableOn (density f) (D f) volume ∧
      ENNReal.ofReal (volume.real (D f)) = volume (D f) ∧
      faceFlux D density f = volume.real (D f) * k := by
  refine ⟨?_, ENNReal.ofReal_toReal hfin, faceFlux_of_const D density f k hD hk⟩
  exact (integrableOn_const hfin).congr_fun (fun p hp => (hk p hp).symm) hD

/-- Uniform through-flow: with two end faces of equal finite area and
constant normal densities `-c` on face `0` and `c` on face `1` (uniform
flow in the positive axis direction), the end-face outward currents are
opposite. Finite area makes both densities integrable and
`volume.real` the face area, so both fluxes are genuine integrals. -/
lemma uniformThroughFlow_endFlux_opposite (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (c : ℝ)
    (hD0 : MeasurableSet (D 0)) (hD1 : MeasurableSet (D 1))
    (hfin0 : volume (D 0) ≠ ⊤) (hfin1 : volume (D 1) ≠ ⊤)
    (harea : volume.real (D 0) = volume.real (D 1))
    (hk0 : ∀ p ∈ D 0, density 0 p = -c) (hk1 : ∀ p ∈ D 1, density 1 p = c) :
    faceFlux D density 1 = -faceFlux D density 0 := by
  obtain ⟨-, -, h1⟩ := faceFlux_of_const_of_measure_ne_top D density 1 c hD1 hfin1 hk1
  obtain ⟨-, -, h0⟩ := faceFlux_of_const_of_measure_ne_top D density 0 (-c) hD0 hfin0 hk0
  rw [h1, h0, harea]
  ring

/-- Through-flow witness: outward currents `(-3, 3, 0, 0, 0, 0)` on the
six faces sum to zero. -/
lemma throughFlow_currents_sum_example :
    ∑ f : Fin 6, (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f = 0 := by
  simp [Fin.sum_univ_six]

/-- Accumulating-charge witness: with enclosed-charge rate `2`, the six
outward currents sum to `-2`, not to zero; the nonzero rate term is
kept. -/
lemma accumulatingCharge_currents_sum_example :
    ∑ f : Fin 6, (![-2, 0, 0, 0, 0, 0] : Fin 6 → ℝ) f = -2 := by
  simp [Fin.sum_univ_six]

/-- Omitted-face witness: dropping the entering end face from the sum
leaves `3`, not zero; all six faces are needed for the balance. -/
lemma omittedFace_currents_sum_example :
    ∑ f : Fin 6, (![0, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f ≠ 0 := by
  simp [Fin.sum_univ_six]

/-! ### D. The axis-aligned box in three-dimensional space: charge continuity derived

Here the faces are the actual faces of the box `Set.Icc a b` in
`Fin 3 → ℝ`. Face `f` has normal axis `faceAxis f`; its parameter
rectangle `boxFaceDomain a b f` lives in the two tangential axes and is
embedded into space by inserting the face level at the normal axis.
Each embedding is a translate of a coordinate rectangle, so surface
measure is two-dimensional Lebesgue measure on parameters, and the
outward normal is `faceSign f` times the normal coordinate vector.
Charge continuity is derived here, not assumed: from the local law
`∂ρ/∂t + div J = 0` and the divergence theorem on boxes, the six
outward fluxes sum to minus the enclosed-charge rate. -/

/-- Normal axis of face `f`: faces `0, 1` are normal to axis `0`,
faces `2, 3` to axis `1`, and faces `4, 5` to axis `2`. -/
def faceAxis : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

/-- Whether face `f` is the upper face of its axis (outward normal
`+eₖ`); even faces are lower faces (outward normal `-eₖ`). -/
def faceIsUpper : Fin 6 → Bool := ![false, true, false, true, false, true]

/-- Outward orientation sign of face `f`. -/
def faceSign (f : Fin 6) : ℝ := if faceIsUpper f then 1 else -1

/-- Coordinate of face `f` of the box `Set.Icc a b` along its normal
axis. -/
def faceLevel (a b : Fin 3 → ℝ) (f : Fin 6) : ℝ :=
  if faceIsUpper f then b (faceAxis f) else a (faceAxis f)

/-- Parameter rectangle of face `f`: the extent of the box in the two
tangential axes. -/
def boxFaceDomain (a b : Fin 3 → ℝ) (f : Fin 6) : Set (Fin 2 → ℝ) :=
  Set.Icc (a ∘ (faceAxis f).succAbove) (b ∘ (faceAxis f).succAbove)

/-- Embedding of the parameter rectangle of face `f` into space: the
face level is inserted at the normal axis. -/
def boxFaceEmbed (a b : Fin 3 → ℝ) (f : Fin 6) (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  (faceAxis f).insertNth (faceLevel a b f) x

/-- Outward-normal component, on face `f`, of an ambient current
density `J`. -/
def boxNormalDensity (a b : Fin 3 → ℝ) (J : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (f : Fin 6) (x : Fin 2 → ℝ) : ℝ :=
  faceSign f * J (boxFaceEmbed a b f x) (faceAxis f)

/-- Outward flux of an ambient current density through face `f` of the
box `Set.Icc a b`. -/
noncomputable def boxOutwardFlux (a b : Fin 3 → ℝ) (J : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (f : Fin 6) : ℝ :=
  ∫ x in boxFaceDomain a b f, boxNormalDensity a b J f x

/-- Divergence of a vector field whose derivative is `J'`. -/
def fderivDivergence (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    ℝ :=
  ∑ i, J' x (Pi.single i 1) i

/-- Face parameter rectangles are compact, so every face has finite
area. -/
lemma volume_boxFaceDomain_ne_top (a b : Fin 3 → ℝ) (f : Fin 6) :
    volume (boxFaceDomain a b f) ≠ ⊤ :=
  isCompact_Icc.measure_lt_top.ne

/-- **Divergence theorem for the six faces.** The six outward face
fluxes of a current density, continuous on the box and differentiable
in its interior, sum to the integral of its divergence. -/
theorem sum_boxOutwardFlux_eq_integral_divergence (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (hi : IntegrableOn (fderivDivergence J') (Set.Icc a b)) :
    ∑ f : Fin 6, boxOutwardFlux a b J f = ∫ x in Set.Icc a b, fderivDivergence J' x := by
  have h := integral_divergence_of_hasFDerivAt_off_countable a b hle J J' ∅
    Set.countable_empty hc (fun x hx => hd x hx.1) hi
  unfold fderivDivergence at h ⊢
  rw [h, Fin.sum_univ_three, Fin.sum_univ_six]
  simp only [boxOutwardFlux, boxNormalDensity, boxFaceDomain, boxFaceEmbed, faceLevel,
    faceSign, faceAxis, faceIsUpper]
  simp [integral_neg]
  ring

/-- **Box charge continuity, derived.** If the current density and the
charge-density rate `ρdot` obey the local continuity law
`ρdot + div J = 0` on the box, the six outward fluxes satisfy
`chargeContinuity` with rate the integral of `ρdot` over the box. -/
theorem chargeContinuity_boxOutwardFlux (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (ρdot : (Fin 3 → ℝ) → ℝ) (hρdot : IntegrableOn ρdot (Set.Icc a b))
    (hlocal : ∀ x ∈ Set.Icc a b, ρdot x + fderivDivergence J' x = 0) :
    chargeContinuity (boxOutwardFlux a b J) (∫ x in Set.Icc a b, ρdot x) := by
  have heq : Set.EqOn (fderivDivergence J') (fun x => -ρdot x) (Set.Icc a b) := fun x hx => by
    linarith [hlocal x hx]
  have hi : IntegrableOn (fderivDivergence J') (Set.Icc a b) :=
    hρdot.neg.congr_fun heq.symm measurableSet_Icc
  unfold chargeContinuity
  rw [sum_boxOutwardFlux_eq_integral_divergence a b hle J J' hc hd hi,
    setIntegral_congr_fun measurableSet_Icc heq, integral_neg]

/-- Charge enclosed by the box `Set.Icc a b` at time `t`, for a
time-dependent charge density `ρ`. -/
noncomputable def enclosedCharge (a b : Fin 3 → ℝ) (ρ : ℝ → (Fin 3 → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Set.Icc a b, ρ t x

/-- The enclosed charge is differentiable in time, with derivative the
integral of the charge-density rate, for a continuous density with a
continuous time derivative. -/
theorem hasDerivAt_enclosedCharge (a b : Fin 3 → ℝ) (ρ ρdot : ℝ → (Fin 3 → ℝ) → ℝ)
    (hρ : Continuous (Function.uncurry ρ)) (hρdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ s x, HasDerivAt (fun s => ρ s x) (ρdot s x) s) (t : ℝ) :
    HasDerivAt (enclosedCharge a b ρ) (∫ x in Set.Icc a b, ρdot t x) t := by
  have hK : IsCompact (Metric.closedBall t 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall t 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hρdot.continuousOn
  have hcont : ∀ s, Continuous (ρ s) := fun s =>
    hρ.comp (Continuous.prodMk_right s)
  have hcont' : ∀ s, Continuous (ρdot s) := fun s =>
    hρdot.comp (Continuous.prodMk_right s)
  have : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    ((hcont t).integrableOn_Icc) (hcont' t).aestronglyMeasurable ?_
    (integrable_const C) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx s hs
    exact hC (s, x) ⟨hs, hx⟩
  · exact Filter.Eventually.of_forall fun x s _ => hderiv s x

/-- **Enclosed-charge balance.** Under the local continuity law at time
`t`, the enclosed charge changes at minus the total outward flux of the
six faces. -/
theorem hasDerivAt_enclosedCharge_eq_neg_sum_boxOutwardFlux (a b : Fin 3 → ℝ)
    (hle : a ≤ b) (ρ ρdot : ℝ → (Fin 3 → ℝ) → ℝ)
    (hρ : Continuous (Function.uncurry ρ)) (hρdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ s x, HasDerivAt (fun s => ρ s x) (ρdot s x) s) (t : ℝ)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (hlocal : ∀ x ∈ Set.Icc a b, ρdot t x + fderivDivergence J' x = 0) :
    HasDerivAt (enclosedCharge a b ρ) (-∑ f : Fin 6, boxOutwardFlux a b J f) t := by
  have hcont' : Continuous (ρdot t) := hρdot.comp (Continuous.prodMk_right t)
  have h := chargeContinuity_boxOutwardFlux a b hle J J' hc hd (ρdot t)
    hcont'.integrableOn_Icc hlocal
  unfold chargeContinuity at h
  rw [h, neg_neg]
  exact hasDerivAt_enclosedCharge a b ρ ρdot hρ hρdot hderiv t

/-- **Constant enclosed charge, derived.** If the charge enclosed by the
box is constant in time and the local continuity law holds at time `t`,
the six outward fluxes sum to zero. -/
theorem sum_boxOutwardFlux_eq_zero_of_enclosedCharge_const (a b : Fin 3 → ℝ)
    (hle : a ≤ b) (ρ ρdot : ℝ → (Fin 3 → ℝ) → ℝ)
    (hρ : Continuous (Function.uncurry ρ)) (hρdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ s x, HasDerivAt (fun s => ρ s x) (ρdot s x) s) (t : ℝ)
    (hconst : ∀ s, enclosedCharge a b ρ s = enclosedCharge a b ρ t)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (hlocal : ∀ x ∈ Set.Icc a b, ρdot t x + fderivDivergence J' x = 0) :
    ∑ f : Fin 6, boxOutwardFlux a b J f = 0 := by
  have h := hasDerivAt_enclosedCharge_eq_neg_sum_boxOutwardFlux a b hle ρ ρdot hρ hρdot
    hderiv t J J' hc hd hlocal
  have hQ : enclosedCharge a b ρ = fun _ => enclosedCharge a b ρ t := funext hconst
  rw [hQ] at h
  have h0 := h.unique (hasDerivAt_const t (enclosedCharge a b ρ t))
  linarith

/-- Face domains of the box transported to `ℝ × ℝ`, the parameter space
of the interface in sections A and B. -/
def boxFaceSets (a b : Fin 3 → ℝ) (f : Fin 6) : Set (ℝ × ℝ) :=
  MeasurableEquiv.finTwoArrow '' boxFaceDomain a b f

/-- Outward-normal densities of the box transported to `ℝ × ℝ`. -/
def boxFaceDensities (a b : Fin 3 → ℝ) (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (f : Fin 6)
    (p : ℝ × ℝ) : ℝ :=
  boxNormalDensity a b J f (MeasurableEquiv.finTwoArrow.symm p)

/-- The interface face flux of the transported box data is the outward
flux through the actual box face. -/
lemma faceFlux_boxFaceSets (a b : Fin 3 → ℝ) (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (f : Fin 6) :
    faceFlux (boxFaceSets a b) (boxFaceDensities a b J) f = boxOutwardFlux a b J f := by
  unfold faceFlux PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent boxFaceSets
    boxFaceDensities boxOutwardFlux
  rw [(volume_preserving_finTwoArrow ℝ).setIntegral_image_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding]
  have hx : ∀ x : Fin 2 → ℝ, MeasurableEquiv.finTwoArrow.symm
      (MeasurableEquiv.finTwoArrow x) = x := fun x =>
    MeasurableEquiv.finTwoArrow.symm_apply_apply x
  simp only [hx]

/-- **Box terminal flux balance.** Terminal outward currents identified
with the six outward face fluxes of the box `Set.Icc a b` sum to minus
the integral of the charge-density rate `ρdot` over the box, which is the
enclosed-charge rate by `hasDerivAt_enclosedCharge`, under the local
continuity law `ρdot + div J = 0`. The `chargeContinuity` premise of
`sum_terminalCurrent_eq_neg_chargeRate` is discharged by the divergence
theorem rather than assumed. -/
theorem boxTerminalCurrents_sum_eq_neg_chargeRate (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (ρdot : (Fin 3 → ℝ) → ℝ) (hρdot : IntegrableOn ρdot (Set.Icc a b))
    (hlocal : ∀ x ∈ Set.Icc a b, ρdot x + fderivDivergence J' x = 0)
    (I : Fin 6 → ℝ) (hI : ∀ f : Fin 6, I f = boxOutwardFlux a b J f) :
    ∑ f : Fin 6, I f = -∫ x in Set.Icc a b, ρdot x := by
  have hflux : faceFlux (boxFaceSets a b) (boxFaceDensities a b J) = boxOutwardFlux a b J :=
    funext (faceFlux_boxFaceSets a b J)
  refine sum_terminalCurrent_eq_neg_chargeRate (boxFaceSets a b) (boxFaceDensities a b J) I _
    (fun f => by rw [hI f, faceFlux_boxFaceSets]) ?_
  rw [hflux]
  exact chargeContinuity_boxOutwardFlux a b hle J J' hc hd ρdot hρdot hlocal

/-- **Constant enclosed charge.** Terminal outward currents identified
with the six outward face fluxes of the box sum to zero when the charge
enclosed by the box is constant in time and the local continuity law
holds at time `t`. -/
theorem boxTerminalCurrents_sum_eq_zero_of_constantCharge (a b : Fin 3 → ℝ)
    (hle : a ≤ b) (ρ ρdot : ℝ → (Fin 3 → ℝ) → ℝ)
    (hρ : Continuous (Function.uncurry ρ)) (hρdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ s x, HasDerivAt (fun s => ρ s x) (ρdot s x) s) (t : ℝ)
    (hconst : ∀ s, enclosedCharge a b ρ s = enclosedCharge a b ρ t)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc a b))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (a i) (b i), HasFDerivAt J (J' x) x)
    (hlocal : ∀ x ∈ Set.Icc a b, ρdot t x + fderivDivergence J' x = 0)
    (I : Fin 6 → ℝ) (hI : ∀ f : Fin 6, I f = boxOutwardFlux a b J f) :
    ∑ f : Fin 6, I f = 0 := by
  rw [Finset.sum_congr rfl fun f _ => hI f]
  exact sum_boxOutwardFlux_eq_zero_of_enclosedCharge_const a b hle ρ ρdot hρ hρdot hderiv t
    hconst J J' hc hd hlocal

end PhyslibExt.Circuits.BoxTerminalFlux
