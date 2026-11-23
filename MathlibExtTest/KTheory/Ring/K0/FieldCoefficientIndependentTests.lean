/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.K0.FieldCoefficientIndependent
import Mathlib.Algebra.Field.ULift
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Native coefficient and image clients in independent field universes. -/

noncomputable section

open AlgebraicKTheory FGProjectiveCat

universe uF uG uH u

namespace AlgebraicKTheory.RingK0

variable {F : Type uF} {G : Type uG} {H : Type uH} [Field F] [Field G] [Field H]

example (f : F →+* G) (z : ℤ) :
    fieldRankEquiv G (scalarExtensionK0 f ((fieldRankEquiv F).symm z)) = z := by
  simp only [fieldRankEquiv_symm_apply,
    scalarExtensionK0_intCast, map_intCast, Int.cast_id]

example (f : F →+* G) (z : ℤ) :
    scalarExtensionK0 f ((fieldRankEquiv F).symm z) = (fieldRankEquiv G).symm z :=
  DFunLike.congr_fun (scalarExtensionK0_fieldRankEquiv_symm f) z

example (f : F →+* G) (P : FGProjectiveCat.{uF} F) :
    Module.finrank G ((ringScalarExtension f).obj P) = Module.finrank F P :=
  finrank_ringScalarExtension f P

example (f : F →+* G) (g : G →+* H) (x : RingK0 F) :
    fieldRank H (scalarExtensionK0 g (scalarExtensionK0 f x)) = fieldRank F x := by
  simp only [fieldRank_scalarExtensionK0_apply]

example (f : F →+* G) : Function.Bijective (scalarExtensionK0 f) :=
  scalarExtensionK0_bijective_of_field f

example (f : F →+* G) :
    fieldRank G (scalarExtensionK0 f
      (K0.mk (standardFreeProjective F 2) - K0.mk (standardFreeProjective F 5))) = -3 := by
  rw [fieldRank_scalarExtensionK0_apply, map_sub, fieldRank_mk, fieldRank_mk]
  change (Module.finrank F (Fin 2 → F) : ℤ) - (Module.finrank F (Fin 5 → F) : ℤ) = -3
  norm_num

-- A low-universe real source and a genuinely larger native coefficient field.
example :
    let f : ℝ →+* ULift.{u} ℂ :=
      (ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).symm.toRingHom.comp Complex.ofRealHom
    fieldRank (ULift.{u} ℂ)
        (scalarExtensionK0 f (K0.mk (FGProjectiveCat.of (R := ℝ) (Fin 2 → ℝ)))) = 2 := by
  dsimp only
  rw [fieldRank_scalarExtensionK0_apply, fieldRank_mk]
  change (Module.finrank ℝ (Fin 2 → ℝ) : ℤ) = 2
  norm_num

#print axioms fieldRank_scalarExtensionK0
#print axioms scalarExtensionK0_eq_fieldRank
#print axioms scalarExtensionK0_fieldRankEquiv_symm
#print axioms scalarExtensionK0_coefficient_dictionary
#print axioms scalarExtensionK0_bijective_of_field
#print axioms FGProjectiveCat.finrank_ringScalarExtension

end AlgebraicKTheory.RingK0
