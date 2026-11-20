/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.OSSS.GrandCoupling

open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS.GrandCoupling

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls









theorem oc3_uniformFactor_univ :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num


theorem oc3_uniformFactor_isProbabilityMeasure :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨oc3_uniformFactor_univ⟩





theorem oc3_vcube_eq_pi (n : ℕ) :
    Vcube n = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  rfl



theorem oc3_vcube_univ_prod (n : ℕ) :
    (Vcube n) Set.univ
      = ∏ _i : Fin n, (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ := by
  rw [oc3_vcube_eq_pi, Measure.pi_univ]



theorem oc3_vcube_univ (n : ℕ) : (Vcube n) Set.univ = 1 := by
  rw [oc3_vcube_univ_prod]
  simp only [oc3_uniformFactor_univ, Finset.prod_const_one]





theorem oc3_vcube_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (Vcube n) :=
  ⟨oc3_vcube_univ n⟩




theorem oc3_vcube_isProbabilityMeasure_consistent (n : ℕ) :
    (oc3_vcube_isProbabilityMeasure n).measure_univ
      = (inferInstance : IsProbabilityMeasure (Vcube n)).measure_univ :=
  rfl

end Walls
end StatMech
