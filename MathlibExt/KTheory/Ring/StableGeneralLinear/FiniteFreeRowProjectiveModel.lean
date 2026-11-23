/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentModelTransport
public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel
public import MathlibExt.Algebra.Category.FGProjectiveCat.UniverseEquivalence

/-!
# The actual row-idempotent and full projective zero categories

The established row-range equivalence is additive and covers all finitely
generated projectives. Restricting its original Pair equivalence to zero
therefore transports the actual finite-row model to the full projective
zero category, retaining the original Ring and both zero coordinates.
No category equivalence, space model, or comparison witness is supplied.
-/

noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The SAME actual small row model is equivalent to the ORIGINAL full
projective zero category; the projective object universe is larger. -/
public def finiteFreeRowProjectiveZeroEquivalence :
    SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
      SInverseS.ZeroComponent (C := FGProjectiveCat.{u} R) :=
  SInverseS.zeroComponentEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)

/-- The original zero point comparison uses BOTH original additive zero
isomorphisms of the actual row-range functor. -/
public def finiteFreeRowProjectiveZeroPointIso :
    (finiteFreeRowProjectiveZeroEquivalence R).functor.obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{u} R) :=
  SInverseS.zeroComponentEquivalencePointIso
    (FGProjectiveCat.IdempotentModel.equivalence R)

/-- The WHOLE model triangle retains the actual Pair equivalence induced
by the original row-range equivalence, before any realization. -/
public def finiteFreeRowProjectiveZeroInclusionIso :
    (finiteFreeRowProjectiveZeroEquivalence R).functor ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{u} R)).ι ≅
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        (SInverseS.pairEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)).functor :=
  SInverseS.zeroComponentEquivalenceInclusionIso
    (FGProjectiveCat.IdempotentModel.equivalence R)

/-- The actual row-range and inverse universe functors have an additive composite. -/
public instance finiteFreeRowProjectiveUniverseFunctorAdditive :
    ((FGProjectiveCat.IdempotentModel.equivalence R).trans
      (FGProjectiveCat.universeEquivalence.{u, v} R).symm).functor.Additive := by
  change ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    (FGProjectiveCat.universeEquivalence.{u, v} R).inverse).Additive
  infer_instance

/-- The ORIGINAL Ring is retained while the full projective carrier is
independently enlarged. The existing finite-generation Shrink/ULift
equivalence supplies the actual additive model equivalence internally. -/
public def finiteFreeRowProjectiveUniverseZeroEquivalence :
    SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
      SInverseS.ZeroComponent (C := FGProjectiveCat.{max u v} R) :=
  SInverseS.zeroComponentEquivalence
    ((FGProjectiveCat.IdempotentModel.equivalence R).trans
      (FGProjectiveCat.universeEquivalence.{u, v} R).symm)

/-- Its actual original zero points are compared through BOTH canonical
zero isomorphisms of the unchanged-Ring row-range/lift composite. -/
public def finiteFreeRowProjectiveUniverseZeroPointIso :
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R).functor.obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max u v} R) :=
  SInverseS.zeroComponentEquivalencePointIso
    ((FGProjectiveCat.IdempotentModel.equivalence R).trans
      (FGProjectiveCat.universeEquivalence.{u, v} R).symm)

/-- The entire independent-carrier triangle is the actual additive Pair
functor of the original row-range/lift equivalence. -/
public def finiteFreeRowProjectiveUniverseZeroInclusionIso :
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R).functor ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max u v} R)).ι ≅
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        (SInverseS.pairEquivalence
          ((FGProjectiveCat.IdempotentModel.equivalence R).trans
            (FGProjectiveCat.universeEquivalence.{u, v} R).symm)).functor :=
  SInverseS.zeroComponentEquivalenceInclusionIso
    ((FGProjectiveCat.IdempotentModel.equivalence R).trans
      (FGProjectiveCat.universeEquivalence.{u, v} R).symm)

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory

universe uProjectiveValueRing uProjectiveValueCarrier

namespace AlgebraicKTheory.StableGL

variable (R : Type uProjectiveValueRing) [Ring R]

private theorem finiteFreeRowProjectiveUniverseZeroEquivalenceValueComputed :
    finiteFreeRowProjectiveUniverseZeroEquivalence.{uProjectiveValueRing,
      uProjectiveValueCarrier} R =
      SInverseS.zeroComponentEquivalence
        ((FGProjectiveCat.IdempotentModel.equivalence R).trans
          (FGProjectiveCat.universeEquivalence.{uProjectiveValueRing,
            uProjectiveValueCarrier} R).symm) := by
  rfl

/-- The entire original universe zero equivalence is the SAME prescribed
row-range/lift composite, including its original categorical inverse data. -/
public theorem finiteFreeRowProjectiveUniverseZeroEquivalence_value :
    finiteFreeRowProjectiveUniverseZeroEquivalence.{uProjectiveValueRing,
      uProjectiveValueCarrier} R =
      SInverseS.zeroComponentEquivalence
        ((FGProjectiveCat.IdempotentModel.equivalence R).trans
          (FGProjectiveCat.universeEquivalence.{uProjectiveValueRing,
            uProjectiveValueCarrier} R).symm) :=
  finiteFreeRowProjectiveUniverseZeroEquivalenceValueComputed R

private theorem finiteFreeRowProjectiveUniverseZeroPointIsoValueComputed :
    finiteFreeRowProjectiveUniverseZeroPointIso.{uProjectiveValueRing,
      uProjectiveValueCarrier} R =
      eqToIso (congrArg
        (fun e : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
          SInverseS.ZeroComponent
            (C := FGProjectiveCat.{max uProjectiveValueRing uProjectiveValueCarrier} R) =>
          e.functor.obj
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))
        (finiteFreeRowProjectiveUniverseZeroEquivalence_value.{uProjectiveValueRing,
          uProjectiveValueCarrier} R)) ≪≫
        SInverseS.zeroComponentEquivalencePointIso
          ((FGProjectiveCat.IdempotentModel.equivalence R).trans
            (FGProjectiveCat.universeEquivalence.{uProjectiveValueRing,
              uProjectiveValueCarrier} R).symm) := by
  let E := (FGProjectiveCat.IdempotentModel.equivalence R).trans
    (FGProjectiveCat.universeEquivalence.{uProjectiveValueRing,
      uProjectiveValueCarrier} R).symm
  let z := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)
  change SInverseS.zeroComponentEquivalencePointIso E =
    eqToIso (rfl : (SInverseS.zeroComponentEquivalence E).functor.obj z =
      (SInverseS.zeroComponentEquivalence E).functor.obj z) ≪≫
        SInverseS.zeroComponentEquivalencePointIso E
  simp only [eqToIso_refl, Iso.refl_trans]

/-- The actual original model point Iso keeps the SAME canonical selected
zero comparison, with only its proved whole-equivalence object transport. -/
public theorem finiteFreeRowProjectiveUniverseZeroPointIso_value :
    finiteFreeRowProjectiveUniverseZeroPointIso.{uProjectiveValueRing,
      uProjectiveValueCarrier} R =
      eqToIso (congrArg
        (fun e : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
          SInverseS.ZeroComponent
            (C := FGProjectiveCat.{max uProjectiveValueRing uProjectiveValueCarrier} R) =>
          e.functor.obj
            (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)))
        (finiteFreeRowProjectiveUniverseZeroEquivalence_value.{uProjectiveValueRing,
          uProjectiveValueCarrier} R)) ≪≫
        SInverseS.zeroComponentEquivalencePointIso
          ((FGProjectiveCat.IdempotentModel.equivalence R).trans
            (FGProjectiveCat.universeEquivalence.{uProjectiveValueRing,
              uProjectiveValueCarrier} R).symm) :=
  finiteFreeRowProjectiveUniverseZeroPointIsoValueComputed R

end AlgebraicKTheory.StableGL

end
