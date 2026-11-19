/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import PhyslibExt.Thermodynamics.ExergyAndLosses

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Thermodynamics.ExergyAndLosses`

Two steady open systems in kW, kJ/kg, kJ/(kg K) and K, with `T₀ = 300 K`:

* a mixing chamber with heat loss whose supplied entropy production is `0.01 kW/K > 0`, so its
  destroyed exergy is `3 kW` for every dead-state enthalpy and entropy;
* a reverse throttle that satisfies the steady first law and the mass balance but has entropy
  generation `-0.4 kW/K` and destroyed exergy `-120 kW`: energy conservation alone does not
  establish the second law.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.ExergyAndLosses

open _root_.ExergyAndLosses

/-- A mixing chamber with heat loss (two inlets, one outlet, one heat port, no shaft work), in
kW, kJ/kg, kJ/(kg K) and K: liquid water at `1 kg/s` with `θ = 100`, `s = 0.35` and at
`1 kg/s` with `θ = 300`, `s = 0.98` leaves as `2 kg/s` with `θ = 197`, `s = 0.66`, losing
`6 kW` (`Q̇ = -6`) through a boundary at `300 K`, with `T₀ = 300 K`. The steady first law and
mass balance hold, the supplied entropy production is `0.01 kW/K > 0`, and the destroyed exergy
is `3 kW = T₀ Ṡ_gen` for every dead-state enthalpy and entropy. -/
lemma fixture_mixing_chamber (h0 s0 : ℝ) :
    energyResidual ![(-6 : ℝ)] 0 ![1, 1] ![100, 300] ![2] ![197] = 0 ∧
      ∑ i, (![1, 1] : Fin 2 → ℝ) i = ∑ o, (![2] : Fin 1 → ℝ) o ∧
      entropyGen ![(-6 : ℝ)] ![300] ![1, 1] ![0.35, 0.98] ![2] ![0.66] = 0.01 ∧
      exergyDestroyed 300 h0 s0 ![(-6 : ℝ)] ![300] 0 ![1, 1] ![100, 300] ![0.35, 0.98]
        ![2] ![197] ![0.66] = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold energyResidual ProcessPorts.workOut
    simp [Fin.sum_univ_two]
    norm_num
  · simp [Fin.sum_univ_two]
    norm_num
  · unfold entropyGen
    simp [Fin.sum_univ_two]
    norm_num
  · unfold exergyDestroyed flowExergy ProcessPorts.workOut
    simp [Fin.sum_univ_two]
    ring

/-- Energy conservation alone does not establish the second law: an adiabatic, workless
reverse throttle of air (`2 kg/s`, `θ = 300 kJ/kg` in and out, `s` falling from `1.9` to
`1.7 kJ/(kg K)`, as for a pressure rise from `100 kPa` to `200 kPa` at `300 K`) satisfies the
steady first law and the mass balance, yet its entropy generation is `-0.4 kW/K` and its
destroyed exergy is `-120 kW` at `T₀ = 300 K`. -/
lemma fixture_energy_without_second_law (h0 s0 : ℝ) :
    energyResidual (![] : Fin 0 → ℝ) 0 ![(2 : ℝ)] ![300] ![(2 : ℝ)] ![300] = 0 ∧
      ∑ i, (![2] : Fin 1 → ℝ) i = ∑ o, (![2] : Fin 1 → ℝ) o ∧
      entropyGen (![] : Fin 0 → ℝ) ![] ![(2 : ℝ)] ![1.9] ![(2 : ℝ)] ![1.7] = -0.4 ∧
      exergyDestroyed 300 h0 s0 (![] : Fin 0 → ℝ) ![] 0 ![(2 : ℝ)] ![300] ![1.9] ![(2 : ℝ)]
        ![300] ![1.7] = -120 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold energyResidual ProcessPorts.workOut
    simp
  · simp
  · unfold entropyGen
    simp
    norm_num
  · unfold exergyDestroyed flowExergy ProcessPorts.workOut
    simp
    ring

end PhyslibExtTest.Thermodynamics.ExergyAndLosses
