/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge

@[expose] public section

open Electromagnetism
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
open MathlibExt.Analysis.Numerical.PeriodicYeeResidual
open PhyslibExt.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge

namespace PhyslibExtTest.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge

/-- The polarized travelling wave satisfies the component Maxwell equations. -/
example (𝓕 : FreeSpace) (A k : ℝ) :
    sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField (travellingWaveE 𝓕 A k))
      (polarizedMagneticField 𝓕 (travellingWaveH 𝓕 A k)) :=
  (travellingWave_sourceFreeVacuumMaxwell 𝓕 A k).1

/-- The unit-amplitude travelling wave is nonzero at the origin. -/
example (𝓕 : FreeSpace) (k : ℝ) : travellingWaveE 𝓕 1 k 0 0 ≠ 0 :=
  (travellingWave_sourceFreeVacuumMaxwell 𝓕 1 k).2 one_ne_zero

/-- The same wave satisfies the reduced component equations. -/
example (𝓕 : FreeSpace) (A k t x : ℝ) :
    deriv (fun s => travellingWaveE 𝓕 A k s x) t =
      -(1 / 𝓕.ε₀) * deriv (fun y => travellingWaveH 𝓕 A k t y) x :=
  ((sourceFreeVacuumMaxwell_polarized_iff 𝓕 _ _).mp
    (travellingWave_sourceFreeVacuumMaxwell 𝓕 A k).1 t x).1

/-- Its energy coordinates satisfy the first-order wave system at the speed of light. -/
example (𝓕 : FreeSpace) (A k : ℝ) :
    satisfiesWaveSystem (𝓕.c : ℝ) (energyU 𝓕 (travellingWaveE 𝓕 A k))
      (energyV 𝓕 (travellingWaveH 𝓕 A k)) :=
  polarizedVacuumMaxwell_waveSystem 𝓕 _ _ (travellingWave_sourceFreeVacuumMaxwell 𝓕 A k).1

/-- For the travelling wave the magnetic energy coordinate is the negated electric one. -/
example (𝓕 : FreeSpace) (A k t x : ℝ) :
    energyV 𝓕 (travellingWaveH 𝓕 A k) t x = -energyU 𝓕 (travellingWaveE 𝓕 A k) t x :=
  congrFun (congrFun (travellingWave_minusSign 𝓕 A k).1 t) x

/-- With the opposite sign in `v` the unit travelling wave violates the wave system. -/
example (𝓕 : FreeSpace) :
    ¬ satisfiesWaveSystem (𝓕.c : ℝ) (energyU 𝓕 (travellingWaveE 𝓕 1 1))
      (fun t x => Real.sqrt 𝓕.μ₀ * travellingWaveH 𝓕 1 1 t x) :=
  (travellingWave_minusSign 𝓕 1 1).2 one_ne_zero one_ne_zero

/-- Three periods of the wave fit in a domain of length `2`. -/
example (𝓕 : FreeSpace) (A : ℝ) :
    isSpatiallyPeriodic 2 (travellingWaveE 𝓕 A (2 * Real.pi * (3 : ℤ) / 2))
      (travellingWaveH 𝓕 A (2 * Real.pi * (3 : ℤ) / 2)) :=
  travellingWave_isSpatiallyPeriodic 𝓕 A 2 3 two_ne_zero

/-- A wave whose wavelength does not divide the period is not periodic. -/
example (𝓕 : FreeSpace) :
    ¬ isSpatiallyPeriodic 1 (travellingWaveE 𝓕 1 1) (travellingWaveH 𝓕 1 1) :=
  travellingWave_not_isSpatiallyPeriodic 𝓕

/-- The squared pair norm of the grid energy coordinates is twice the discrete energy. -/
example (𝓕 : FreeSpace) (h : ℝ) (E H : Fin 4 → ℝ) :
    MathlibExt.Analysis.Numerical.PeriodicYeeEnergy.pairNormSq h
        (gridEnergyCoordinates 𝓕 E H).1 (gridEnergyCoordinates 𝓕 E H).2 =
      2 * gridFieldEnergy 𝓕 h E H :=
  pairNormSq_gridEnergyCoordinates 𝓕 h E H

/-- One physical Yee step is one generic leapfrog step in energy coordinates. -/
example (𝓕 : FreeSpace) (h dt : ℝ) (E H : Fin 4 → ℝ) :
    gridEnergyCoordinates 𝓕 (physicalYeeStep 𝓕 h dt E H).1 (physicalYeeStep 𝓕 h dt E H).2 =
      MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil.leapfrogStep h (𝓕.c : ℝ) dt
        (gridEnergyCoordinates 𝓕 E H).1 (gridEnergyCoordinates 𝓕 E H).2 :=
  gridEnergyCoordinates_physicalYeeStep 𝓕 h dt E H

/-- At step zero the normalized error is the normalized initial mismatch. -/
example (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ) (h dt : ℝ) (E0 H0 : Fin 4 → ℝ) :
    normalizedFieldError 𝓕 Ey Hz h dt E0 H0 0 = normalizedInitialMismatch 𝓕 Ey Hz h dt E0 H0 :=
  rfl

end PhyslibExtTest.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge
