/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.LieModuleCat.CoefficientULift
public import MathlibExt.Algebra.Category.LieModuleCat.RightUniversalEnveloping

/-!
# Original right UEA representations and actual coefficient carrier lifts

The representation of the lifted native Lie coefficient is actually
equivalent to the original representation by native down. Equivariance
follows from the original representation law for the actual down Lie map.
No identification between independent carrier worlds or action dictionaries
is assumed. This provider has no CE, PBW or derived-functor dependency.
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory
open scoped ModuleCat.Algebra

namespace LieModuleCat.RightUniversalEnveloping

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  (M : LieModuleCat.{w} R L)

local notation "U" => UniversalEnvelopingAlgebra R L

/-- Actual down/up equivalence between the right UEA representations of the
lifted original Lie coefficient and the original raw Lie coefficient. -/
def coefficientULiftEquiv :
    representObj R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M) ≃ₗ[Uᵐᵒᵖ]
      representObj R L M :=
  { (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).toAddEquiv with
    map_smul' := by
      intro a m
      let h : LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M →ₗ⁅R,L⁆
          LieModuleCat.restrictObj (LieHom.id : L →ₗ⁅R⁆ L) M :=
        { toLinearMap := (LieModuleCat.CoefficientULift.down.{u, v, w, z} R L M).toLinearMap
          map_lie' := by
            intro x m
            exact (LieModuleCat.CoefficientULift.down.{u, v, w, z} R L M).map_lie x m }
      change h (representation R L
        (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M) a m) =
          representation R L M a (h m)
      simpa only [UniversalEnvelopingAlgebra.map_id, AlgHom.id_apply,
        MulOpposite.op_unop] using
        representation_lieMap R L (LieHom.id : L →ₗ⁅R⁆ L) h a.unop m }

@[simp]
theorem coefficientULiftEquiv_up (m : M) : coefficientULiftEquiv.{u, v, w, z} R L M (ULift.up m) = m :=
  rfl

@[simp]
theorem coefficientULiftEquiv_symm_apply (m : representObj R L M) :
    (coefficientULiftEquiv.{u, v, w, z} R L M).symm m = ULift.up m := rfl

/-- The actual coefficient equivalence in the native scalar restrictions
used by the original ground-linear balanced quotient. -/
def coefficientULiftGroundEquiv :
    (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
      (representObj R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj (representObj R L M) :=
  (coefficientULiftEquiv.{u, v, w, z} R L M).restrictScalars R

end LieModuleCat.RightUniversalEnveloping
