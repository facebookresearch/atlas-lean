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
# Right enveloping actions commute with coefficient universe lifts

Let R be a commutative ring, L an R-Lie algebra and M a left Lie module
in carrier world w. Give M its right enveloping action
m·ι(x) = −[x,m]. The Lie coefficient lift ULift^z M has the inherited
bracket [x,up(m)] = up([x,m]).

Removing the lift gives a U_R(L)ᵒᵖ-linear equivalence from the represented
lifted module to the represented module M. Its inverse is m ↦ up(m).
Restricting both modules along R → U_R(L)ᵒᵖ gives the same equivalence
over R. The scalar, Lie, coefficient and extra-height universes are
independent.
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

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, the down map from the represented ULift^z M to the
represented M is U_R(L)ᵒᵖ-linear. Its inverse is the up map,
and both right generator actions are m·ι(x) = −[x,m]. -/
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

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, restrict the right representations of ULift^z M and M
along R → U_R(L)ᵒᵖ. The coefficient down/up equivalence is then
R-linear between these scalar restrictions, with the given
ground action on M. -/
def coefficientULiftGroundEquiv :
    (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj
      (representObj R L (LieModuleCat.CoefficientULift.obj.{u, v, w, z} R L M)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj (representObj R L M) :=
  (coefficientULiftEquiv.{u, v, w, z} R L M).restrictScalars R

end LieModuleCat.RightUniversalEnveloping
