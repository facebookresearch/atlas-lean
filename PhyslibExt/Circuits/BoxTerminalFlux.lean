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

/-!
# Six-face box terminal flux and charge continuity

## i. Overview

An axis-aligned box has six oriented faces, indexed by `Fin 6`,
whose parametrized domains partition its boundary. On each face
the outward-normal component of the current density is a scalar
density on a two-dimensional parameter domain, and the terminal
outward current of the face is the flux integral of that density
over the face domain, using `terminalCurrent` from
`PhyslibExt.Circuits.UniformOhmicBar`. The current density obeys
the local Ohm law from the same module: its normal component is
the conductivity times the outward-normal electric-field
component. Charge continuity is recorded by `chargeContinuity`:
the sum of the six outward fluxes equals minus the rate of
change of the enclosed charge. When the enclosed charge is
constant, that rate is zero and the six terminal outward
currents sum to zero; otherwise the nonzero rate term is kept.
A uniform through-flow gives opposite currents on the two end
faces, and omitting a face or accumulating charge breaks the
zero-sum conclusion. No canonical box charge-conservation
theorem is used: continuity enters through the
`chargeContinuity` hypothesis in the balance results below.

## ii. Key results

- `boxTerminalCurrents_sum_eq_neg_chargeRate`: the six terminal
  currents sum to minus the enclosed-charge rate.
- `boxTerminalCurrents_sum_eq_zero_of_constantCharge`: with
  charge rate zero, the six terminal currents sum to zero.
- `faceFlux_ohmicDensity`: the flux of an ohmic density is the
  conductivity times the flux of the normal field component,
  proved by pulling the constant conductivity out of the face
  integral.
- `faceFlux_of_const`: the flux of a constant density over a
  face is the face area times the constant.

## iii. Table of contents

- A. Faces, flux, and the ohmic density
- B. Charge continuity and terminal-current balance
- C. Constant densities, through-flow, and witnesses

## iv. References

- D. J. Griffiths, *Introduction to Electrodynamics*, fourth
  edition, Cambridge University Press, 2017: the continuity
  equation relating current flux through a closed surface to
  the rate of change of the enclosed charge, and Ohm's law
  `J = σE`.

## A. Faces, flux, and the ohmic density

## B. Charge continuity and terminal-current balance

## C. Constant densities, through-flow, and witnesses
-/

@[expose] public section

open MeasureTheory

namespace PhyslibExt.Circuits.BoxTerminalFlux

/-! ### A. Faces, flux, and the ohmic density -/

/-- The six oriented faces partition the boundary: their parametrized
domains cover the boundary and are pairwise disjoint. Insulating or
nonterminal faces are included; no face is dropped. -/
def FacesPartitionBoundary (D : Fin 6 → Set (ℝ × ℝ)) (boundary : Set (ℝ × ℝ)) :
    Prop :=
  (⋃ f : Fin 6, D f) = boundary ∧ Pairwise fun f g => Disjoint (D f) (D g)

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

/-- Charge continuity for the box: the sum of the six outward
fluxes equals minus the enclosed-charge rate. -/
def chargeContinuity (flux : Fin 6 → ℝ) (chargeRate : ℝ) : Prop :=
  ∑ f : Fin 6, flux f = -chargeRate

/-- The flux of an ohmic density is the conductivity times the flux of
the normal field component. -/
theorem faceFlux_ohmicDensity (σ : ℝ) (D : Fin 6 → Set (ℝ × ℝ))
    (eDensity : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6)
    (hInt : IntegrableOn (eDensity f) (D f) volume) :
    faceFlux D (ohmicDensity σ eDensity) f = σ * faceFlux D eDensity f := by
  unfold faceFlux ohmicDensity
    PhyslibExt.Circuits.UniformOhmicBar.ohmCurrentDensity
    PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent
  exact MeasureTheory.integral_const_mul _ _

/-! ### B. Charge continuity and terminal-current balance -/

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

/-- **Box terminal flux balance.** For six oriented faces partitioning
the boundary, with terminal outward currents identified with the
current-density flux integrals and charge continuity in force, the six
terminal currents sum to minus the enclosed-charge rate. -/
theorem boxTerminalCurrents_sum_eq_neg_chargeRate (D : Fin 6 → Set (ℝ × ℝ))
    (boundary : Set (ℝ × ℝ)) (density : Fin 6 → (ℝ × ℝ) → ℝ) (I : Fin 6 → ℝ)
    (chargeRate : ℝ) (hpart : FacesPartitionBoundary D boundary)
    (hI : ∀ f : Fin 6, I f = faceFlux D density f)
    (hcont : chargeContinuity (faceFlux D density) chargeRate) :
    ∑ f : Fin 6, I f = -chargeRate := by
  exact sum_terminalCurrent_eq_neg_chargeRate D density I chargeRate hI hcont

/-- **Constant enclosed charge.** When the enclosed charge is constant,
its rate is zero and the six terminal outward currents sum to zero. -/
lemma boxTerminalCurrents_sum_eq_zero_of_constantCharge
    (D : Fin 6 → Set (ℝ × ℝ)) (boundary : Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (I : Fin 6 → ℝ)
    (hpart : FacesPartitionBoundary D boundary)
    (hI : ∀ f : Fin 6, I f = faceFlux D density f)
    (hcont : chargeContinuity (faceFlux D density) 0) :
    ∑ f : Fin 6, I f = 0 := by
  have h := boxTerminalCurrents_sum_eq_neg_chargeRate D boundary density I 0
    hpart hI hcont
  rwa [neg_zero] at h

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

/-- The flux of a constant density over a face is the face area times
the constant. -/
theorem faceFlux_of_const (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (f : Fin 6) (k : ℝ)
    (hD : MeasurableSet (D f)) (hk : ∀ p ∈ D f, density f p = k) :
    faceFlux D density f = volume.real (D f) * k := by
  unfold faceFlux PhyslibExt.Circuits.UniformOhmicBar.terminalCurrent
  have hae : (density f) =ᵐ[volume.restrict (D f)] (fun _ => k) := by
    filter_upwards [ae_restrict_mem hD] with p hp using hk p hp
  rw [integral_congr_ae hae, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]

/-- Uniform through-flow: with equal end-face areas and constant normal
densities `-c` on face `0` and `c` on face `1` (uniform flow in the
positive axis direction), the end-face outward currents are opposite. -/
lemma uniformThroughFlow_endFlux_opposite (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (c : ℝ)
    (hD0 : MeasurableSet (D 0)) (hD1 : MeasurableSet (D 1))
    (harea : volume.real (D 0) = volume.real (D 1))
    (hk0 : ∀ p ∈ D 0, density 0 p = -c) (hk1 : ∀ p ∈ D 1, density 1 p = c) :
    faceFlux D density 1 = -faceFlux D density 0 := by
  rw [faceFlux_of_const D density 1 c hD1 hk1,
    faceFlux_of_const D density 0 (-c) hD0 hk0, harea]
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

end PhyslibExt.Circuits.BoxTerminalFlux
