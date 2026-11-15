/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# Nonzero ordinary de Rham wedge consumer

The actual dx0 wedge dx1 form in Q[x0,x1] has dual coordinate one.
Reversing its two one-forms negates the native exterior product.
No Wanted algebra constructor is used by this consumer.
-/

@[expose] noncomputable section

namespace MathlibExtTest.RingTheory.OrdinaryDeRhamAlgebraModels

open CategoryTheory
open MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels

abbrev P := MvPolynomial (Fin 2) ℚ

def basis := KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2)

def twoForm : ⋀[P]^2 (Ω[P⁄ℚ]) :=
  exteriorPower.ιMulti P 2 (fun i => basis i)

def area : Module.Dual P (⋀[P]^2 (Ω[P⁄ℚ])) :=
  exteriorPower.pairingDual P (Ω[P⁄ℚ]) 2
    (exteriorPower.ιMulti P 2 (fun i => basis.coord i))

theorem area_twoForm : area twoForm = 1 := by
  simp [area, twoForm, Matrix.det_fin_two]

theorem twoForm_ne_zero : twoForm ≠ 0 := by
  intro h
  have ha := area_twoForm
  rw [h, map_zero] at ha
  exact zero_ne_one ha

theorem native_wedge :
    wedge ℚ P 1 1 (exteriorPower.ιMulti P 1 (fun _ => basis 0))
      (exteriorPower.ιMulti P 1 (fun _ => basis 1)) = twoForm := by
  apply Subtype.ext
  simp [wedge, twoForm, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail]

theorem reversed_wedge :
    wedge ℚ P 1 1 (exteriorPower.ιMulti P 1 (fun _ => basis 1))
      (exteriorPower.ιMulti P 1 (fun _ => basis 0)) = -twoForm := by
  apply Subtype.ext
  have h := ExteriorAlgebra.ι_add_mul_swap (R := P) (basis 1) (basis 0)
  have hs := eq_neg_of_add_eq_zero_left h
  simpa [wedge, twoForm, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecTail] using hs

end MathlibExtTest.RingTheory.OrdinaryDeRhamAlgebraModels
