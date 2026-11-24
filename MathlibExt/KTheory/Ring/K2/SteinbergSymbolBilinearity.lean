/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol
import MathlibExt.GroupTheory.CentralExtensionCommutator
import MathlibExt.KTheory.Ring.K2.StableSteinbergExtension
import MathlibExt.KTheory.Ring.K2.SteinbergSymbolCommutator
import MathlibExt.KTheory.Ring.K2.SteinbergSymbolIndexIndependence

/-! # Bilinearity of the field-valued Steinberg symbol

Multiplicativity of the torus cocycle and the induced Steinberg symbol
in each argument via the central extension commutator calculus.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory.StableSteinberg

open scoped commutatorElement

variable {F : Type u} [Field F]

private theorem toStableE_torus_mul (i j : ℕ) (hij : i ≠ j) (u v : Fˣ) :
    toStableE (torus (R := F) i j hij (u * v)) =
      toStableE (torus (R := F) i j hij u) * toStableE (torus (R := F) i j hij v) := by
  have h0 : toStableE (torusCocycleAt (F := F) i j hij u v) = (1 : StableE F) := by
    rw [torusCocycleAt_eq_torusCocycle, toStableE_torusCocycle]
  have h : toStableE (torus (R := F) i j hij u) * toStableE (torus (R := F) i j hij v) *
      (toStableE (torus (R := F) i j hij (u * v)))⁻¹ = (1 : StableE F) := by
    simpa only [torusCocycleAt, map_mul, map_inv] using h0
  exact (eq_of_mul_inv_eq_one h).symm

private theorem toStableE_torus_comm (u v : Fˣ) :
    Commute (toStableE (torus (R := F) 0 1 (by omega) u))
      (toStableE (torus (R := F) 0 2 (by omega) v)) := by
  have h : ⁅toStableE (torus (R := F) 0 1 (by omega) u),
      toStableE (torus (R := F) 0 2 (by omega) v)⁆ = (1 : StableE F) := by
    simp only [← map_commutatorElement, ← torusCocycle_eq_commutatorElement,
      toStableE_torusCocycle]
  exact (commutatorElement_eq_one_iff_mul_comm.mp h)

private theorem torusCocycle_eq_liftCommutator (u v : Fˣ) :
    torusCocycle (F := F) u v =
      (steinbergExtension (R := F)).liftCommutator
        (toStableE (torus (R := F) 0 1 (by omega) u))
        (toStableE (torus (R := F) 0 2 (by omega) v)) := by
  rw [torusCocycle_eq_commutatorElement (F := F) u v]
  exact GroupExtension.IsCentral.liftCommutator_eq
    (S := steinbergExtension (R := F)) ker_toStableE_le_center rfl rfl

/-- Multiplicativity of the torus cocycle in its first argument. -/
theorem torusCocycle_mul_left (u v w : Fˣ) :
    torusCocycle (F := F) (u * v) w = torusCocycle (F := F) u w * torusCocycle (F := F) v w := by
  have h : (steinbergExtension (R := F)).liftCommutator
      (toStableE (torus (R := F) 0 1 (by omega) (u * v)))
      (toStableE (torus (R := F) 0 2 (by omega) w)) =
      (steinbergExtension (R := F)).liftCommutator
        (toStableE (torus (R := F) 0 1 (by omega) u))
        (toStableE (torus (R := F) 0 2 (by omega) w)) *
      (steinbergExtension (R := F)).liftCommutator
        (toStableE (torus (R := F) 0 1 (by omega) v))
        (toStableE (torus (R := F) 0 2 (by omega) w)) := by
    rw [toStableE_torus_mul 0 1 (by omega) u v]
    exact GroupExtension.IsCentral.liftCommutator_mul_left
      (S := steinbergExtension (R := F)) ker_toStableE_le_center
      (toStableE_torus_comm v w)
  simpa only [← torusCocycle_eq_liftCommutator] using h

/-- Multiplicativity of the torus cocycle in its second argument. -/
theorem torusCocycle_mul_right (u v w : Fˣ) :
    torusCocycle (F := F) u (v * w) = torusCocycle (F := F) u v * torusCocycle (F := F) u w := by
  have h : (steinbergExtension (R := F)).liftCommutator
      (toStableE (torus (R := F) 0 1 (by omega) u))
      (toStableE (torus (R := F) 0 2 (by omega) (v * w))) =
      (steinbergExtension (R := F)).liftCommutator
        (toStableE (torus (R := F) 0 1 (by omega) u))
        (toStableE (torus (R := F) 0 2 (by omega) v)) *
      (steinbergExtension (R := F)).liftCommutator
        (toStableE (torus (R := F) 0 1 (by omega) u))
        (toStableE (torus (R := F) 0 2 (by omega) w)) := by
    rw [toStableE_torus_mul 0 2 (by omega) v w]
    exact GroupExtension.IsCentral.liftCommutator_mul_right
      (S := steinbergExtension (R := F)) ker_toStableE_le_center
      (toStableE_torus_comm u w)
  simpa only [← torusCocycle_eq_liftCommutator] using h

end AlgebraicKTheory.StableSteinberg

namespace AlgebraicKTheory.K2

/-- Bilinearity of the Steinberg symbol in its first argument. -/
theorem steinbergSymbol_mul_left {F : Type u} [Field F] (u v w : Fˣ) :
    steinbergSymbol (F := F) (u * v) w =
      steinbergSymbol (F := F) u w * steinbergSymbol (F := F) v w := by
  apply K2.ext
  simp only [inclusion_steinbergSymbol,
    AlgebraicKTheory.StableSteinberg.torusCocycle_mul_left, map_mul]
  rfl

/-- Bilinearity of the Steinberg symbol in its second argument. -/
theorem steinbergSymbol_mul_right {F : Type u} [Field F] (u v w : Fˣ) :
    steinbergSymbol (F := F) u (v * w) =
      steinbergSymbol (F := F) u v * steinbergSymbol (F := F) u w := by
  apply K2.ext
  simp only [inclusion_steinbergSymbol,
    AlgebraicKTheory.StableSteinberg.torusCocycle_mul_right, map_mul]
  rfl

end AlgebraicKTheory.K2

end
