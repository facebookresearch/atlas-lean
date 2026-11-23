/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.K0.FieldCoefficient
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum

/-! Consumer checks for the original algebraic field coefficient equivalence. -/

open AlgebraicKTheory

noncomputable section

universe u

namespace AlgebraicKTheory.RingK0

example : RingK0 ℝ ≃+* ℤ := fieldRankEquiv ℝ

example : RingK0 ℂ ≃+* ℤ := fieldRankEquiv ℂ

example : (fieldRankEquiv ℂ).symm (-3) = (-3 : RingK0 ℂ) := by
  simp

example : fieldRank ℝ (K0.mk (FGProjectiveCat.of (R := ℝ) (Fin 0 → ℝ))) = 0 := by
  simp

example : fieldRank ℂ (K0.mk (FGProjectiveCat.of (R := ℂ) (Fin 2 → ℂ))) = 2 := by
  rw [fieldRank_mk]
  change (Module.finrank ℂ (Fin 2 → ℂ) : ℤ) = 2
  norm_num

example : fieldRank ℂ
    (K0.mk (standardFreeProjective ℂ 2) - K0.mk (standardFreeProjective ℂ 5)) = -3 := by
  rw [map_sub, fieldRank_mk, fieldRank_mk]
  change (Module.finrank ℂ (Fin 2 → ℂ) : ℤ) - (Module.finrank ℂ (Fin 5 → ℂ) : ℤ) = -3
  norm_num

example (P : FGProjectiveCat.{0} ℝ) :
    rank ℝ (K0.mk P) (default : PrimeSpectrum ℝ) = (Module.finrank ℝ P : ℤ) :=
  fieldRank_mk ℝ P

example : reducedIdeal ℂ = ⊥ := reducedIdeal_field_eq_bot ℂ

example {F G : Type u} [Field F] [Field G] (f : F →+* G) (z : ℤ) :
    fieldRankEquiv G (mapRingHom f ((fieldRankEquiv F).symm z)) = z := by
  simp

example {F G : Type u} [Field F] [Field G] (f g : F →+* G) :
    mapRingHom f = mapRingHom g :=
  mapRingHom_eq_of_field f g

#print axioms mk_eq_finrank_natCast
#print axioms fieldRankEquiv
#print axioms fieldRank_naturality
#print axioms mapRingHom_eq_fieldRank
#print axioms reducedIdeal_field_eq_bot

end AlgebraicKTheory.RingK0
