/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.UniverseEquivalence
public import MathlibExt.KTheory.Exact.K0.Equivalence
public import MathlibExt.KTheory.Exact.K0.Split
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.KTheory.Ring.K0.Projective

/-!
# Independent carrier universes for projective-module K₀

Shrinking finite projectives induces an additive equivalence from `K₀` of
`FGProjectiveCat.{max u v} R` to the existing ring-universe `RingK0 R`.
The generator law is the exact-equivalence generator law for the actual
shrink functor. In particular, lifting an original ring-universe module
preserves its original class, including the regular module. The component
dictionary is the existing positive-first Grothendieck invariant followed by
these same maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Algebra

universe u v

namespace AlgebraicKTheory.RingK0

variable (R : Type u) [Ring R]

/-- Projective-module K₀ at carrier universe `max u v`, identified with fixed `RingK0 R`. -/
def projectiveUniverseEquiv :
    K0 (FGProjectiveCat.{max u v} R) ≃+ RingK0 R :=
  K0.equivOfEquivalence (FGProjectiveCat.universeEquivalence.{u, v} R)

/-- Every original finite-projective generator maps to the class of its actual shrink. -/
@[simp]
theorem projectiveUniverseEquiv_mk (M : FGProjectiveCat.{max u v} R) :
    projectiveUniverseEquiv.{u, v} R (K0.mk M) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R M) :=
  K0.equivOfEquivalence_mk (FGProjectiveCat.universeEquivalence.{u, v} R) M

/-- The inverse K₀ map is induced by the actual lift functor on every generator. -/
@[simp]
theorem projectiveUniverseEquiv_symm_mk (M : FGProjectiveCat.{u} R) :
    (projectiveUniverseEquiv.{u, v} R).symm (K0.mk M) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M) := by
  change K0.map (FGProjectiveCat.universeEquivalence.{u, v} R).inverse
    (K0.mk M) = _
  exact K0.map_mk _ M

/-- Shrinking the actual lifted module preserves its original projective class. -/
@[simp]
theorem mk_shrink_lift (M : FGProjectiveCat.{u} R) :
    K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R
      (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M)) = K0.mk M :=
  K0.mk_congr_of_iso ((FGProjectiveCat.universeEquivalence.{u, v} R).counitIso.app M)

/-- A lifted module has the same original `RingK0` generator after resizing. -/
theorem projectiveUniverseEquiv_mk_lift (M : FGProjectiveCat.{u} R) :
    projectiveUniverseEquiv.{u, v} R
        (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M)) =
      K0.mk M := by
  calc
    projectiveUniverseEquiv.{u, v} R
        (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M)) =
        K0.mk ((FGProjectiveCat.universeEquivalence.{u, v} R).functor.obj
          ((FGProjectiveCat.universeEquivalence.{u, v} R).inverse.obj M)) :=
      K0.equivOfEquivalence_mk (FGProjectiveCat.universeEquivalence.{u, v} R) _
    _ = K0.mk M := K0.mk_congr_of_iso
      ((FGProjectiveCat.universeEquivalence.{u, v} R).counitIso.app M)

/-- The regular module is representable in the large category and maps to its usual class. -/
theorem projectiveUniverseEquiv_regular :
    projectiveUniverseEquiv.{u, v} R
        (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R
          (FGProjectiveCat.of (R := R) R))) =
      K0.mk (FGProjectiveCat.of (R := R) R) :=
  projectiveUniverseEquiv_mk_lift.{u, v} R _

/-- The existing positive-first `S⁻¹S` component invariant, with independent module universe. -/
def sInverseSComponentsUniverseEquiv :
    ConnectedComponents (SInverseS.Pair (FGProjectiveCat.{max u v} R)) ≃ RingK0 R :=
  ((SInverseS.connectedComponentsEquivGrothendieck
      (C := FGProjectiveCat.{max u v} R)).trans
    (K0.splitIso (FGProjectiveCat.{max u v} R)).addCommGroupIsoToAddEquiv.toEquiv).trans
    (projectiveUniverseEquiv.{u, v} R).toEquiv

/-- Every original pair `(P,Q)` maps to the usual difference of its resized projective classes. -/
@[simp]
theorem sInverseSComponentsUniverseEquiv_mk
    (M : SInverseS.Pair (FGProjectiveCat.{max u v} R)) :
    sInverseSComponentsUniverseEquiv.{u, v} R (ConnectedComponents.mk M) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R M.fst) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R M.snd) := by
  change projectiveUniverseEquiv.{u, v} R
    (K0.grothendieckToK0 (FGProjectiveCat.{max u v} R)
      (GrothendieckAddGroup.of (toSkeleton M.fst) -
        GrothendieckAddGroup.of (toSkeleton M.snd))) = _
  simp only [map_sub, K0.grothendieckToK0_of_toSkeleton, projectiveUniverseEquiv_mk]

end AlgebraicKTheory.RingK0
