/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace
public import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# The actual full-projective zero-space model

The existing row-range and finite-generation universe equivalences give
the actual zero-category equivalence. Its original functor is realized
through the existing category/value lifts, with both whole inverse
homotopies on the original spaces. Its selected zero-point comparison is
the realized original Iso in BOTH Pair coordinates, not a given path.
-/

noncomputable section

open CategoryTheory Topology

universe u v

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The actual small row zero realization is homotopy equivalent to the
ORIGINAL full projective zero realization in independent module carriers. -/
public def finiteFreeRowProjectiveZeroHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R))
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)) :=
  CategoryTheory.realizedNerveEquivalence (finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R)

/-- The actual row-zero point reaches the ORIGINAL full-projective zero
point through the realized canonical additive zero Iso in BOTH coordinates. -/
public def finiteFreeRowProjectiveZeroUnitPath :
    Path ((finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)) := by
  let E := finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R
  let e := finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R
  let x := SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)
  let p := SSet.realizedEdgePath
    (CategoryTheory.nerve.edgeMk (finiteFreeRowProjectiveUniverseZeroPointIso.{u, v} R).hom)
  have hSource : e.toFun (SInverseS.ComponentTranslation.zeroSpacePoint
      (C := FGProjectiveCat.IdempotentModel R)) =
      SSet.realizedVertex (ComposableArrows.mk₀ (E.functor.obj x)) :=
    (congrArg e.toFun (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.IdempotentModel R))).trans
        (CategoryTheory.realizedNerveEquivalence_vertex E x)
  exact TopCat.pathEquiv (p.cast hSource
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.{max u v} R)))

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory

universe uModelUnitValueRing uModelUnitValueCarrier

namespace AlgebraicKTheory.StableGL

variable (R : Type uModelUnitValueRing) [Ring R]

private theorem finiteFreeRowProjectiveZeroUnitPathValueComputed (t : unitInterval) :
    finiteFreeRowProjectiveZeroUnitPath.{uModelUnitValueRing, uModelUnitValueCarrier} R t =
      (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk
        (finiteFreeRowProjectiveUniverseZeroPointIso.{uModelUnitValueRing,
          uModelUnitValueCarrier} R).hom))) t := by
  rfl

/-- EVERY time of the SAME original model-unit path is the actual chosen
model zero-Iso edge value; its existing endpoint casts and clocks are retained. -/
public theorem finiteFreeRowProjectiveZeroUnitPath_value (t : unitInterval) :
    finiteFreeRowProjectiveZeroUnitPath.{uModelUnitValueRing, uModelUnitValueCarrier} R t =
      (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk
        (finiteFreeRowProjectiveUniverseZeroPointIso.{uModelUnitValueRing,
          uModelUnitValueCarrier} R).hom))) t :=
  finiteFreeRowProjectiveZeroUnitPathValueComputed R t

end AlgebraicKTheory.StableGL

end

noncomputable section

universe uModelEquivValueRing uModelEquivValueCarrier

namespace AlgebraicKTheory.StableGL

variable (R : Type uModelEquivValueRing) [Ring R]

private theorem finiteFreeRowProjectiveZeroHomotopyEquivValueComputed :
    finiteFreeRowProjectiveZeroHomotopyEquiv.{uModelEquivValueRing,
      uModelEquivValueCarrier} R =
      CategoryTheory.realizedNerveEquivalence
        (finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelEquivValueRing,
          uModelEquivValueCarrier} R) := by
  rfl

/-- The whole SAME original unbased model HE is the realized prescribed
universe zero equivalence, with BOTH original inverse choices retained. -/
public theorem finiteFreeRowProjectiveZeroHomotopyEquiv_value :
    finiteFreeRowProjectiveZeroHomotopyEquiv.{uModelEquivValueRing,
      uModelEquivValueCarrier} R =
      CategoryTheory.realizedNerveEquivalence
        (finiteFreeRowProjectiveUniverseZeroEquivalence.{uModelEquivValueRing,
          uModelEquivValueCarrier} R) :=
  finiteFreeRowProjectiveZeroHomotopyEquivValueComputed R

end AlgebraicKTheory.StableGL

end
