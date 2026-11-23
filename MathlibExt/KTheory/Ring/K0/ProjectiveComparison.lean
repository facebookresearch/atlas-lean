/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.ProjectiveClass
public import MathlibExt.KTheory.Ring.K0.Projective
public import MathlibExt.KTheory.Exact.K0.SplitRing

/-!
# Projective-class and exact-category `K₀` comparison

The projective-class Grothendieck-ring functor is naturally isomorphic to
`RingK0.functor`, and the additive comparison is obtained by forgetting
multiplication.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory
namespace RingK0

/-- Canonical natural isomorphism from the projective-class Grothendieck ring
functor to the exact-category `K₀` ring functor, with component at `R`
`K0.splitRingIso (FGProjectiveCat.{u} (R : Type u))`. -/
noncomputable def projectiveClassRingIso :
    (projectiveClassRingFunctor : CommRingCat.{u} ⥤ CommRingCat.{u + 1}) ≅
      (functor : CommRingCat.{u} ⥤ CommRingCat.{u + 1}) :=
  NatIso.ofComponents
    (fun R => K0.splitRingIso (FGProjectiveCat.{u} (R : Type u)))
    (fun {R S} f => by
      ext : 1
      exact (K0.grothendieckToK0Ring_natural (F := FGProjectiveCat.baseChange f.hom)).symm)

/-- The forward component of `projectiveClassRingIso` sends
`GrothendieckAddGroup.of (toSkeleton P)` to `K0.mk P`. -/
@[simp]
lemma projectiveClassRingIso_hom_of_toSkeleton (R : CommRingCat.{u})
    (P : FGProjectiveCat.{u} (R : Type u)) :
    (projectiveClassRingIso : (projectiveClassRingFunctor : CommRingCat.{u} ⥤ _) ≅ _).hom.app R
        (Algebra.GrothendieckAddGroup.of (toSkeleton P)) =
      K0.mk P := by
  change (K0.splitRingIso (FGProjectiveCat.{u} (R : Type u))).hom
      (Algebra.GrothendieckAddGroup.of (toSkeleton P)) = K0.mk P
  exact K0.splitRingIso_hom_of_toSkeleton (FGProjectiveCat.{u} (R : Type u)) P

/-- The inverse component of `projectiveClassRingIso` sends `K0.mk P` to
`GrothendieckAddGroup.of (toSkeleton P)`. -/
@[simp]
lemma projectiveClassRingIso_inv_mk (R : CommRingCat.{u})
    (P : FGProjectiveCat.{u} (R : Type u)) :
    (projectiveClassRingIso : (projectiveClassRingFunctor : CommRingCat.{u} ⥤ _) ≅ _).inv.app R
        (K0.mk P) =
      Algebra.GrothendieckAddGroup.of (toSkeleton P) := by
  change (K0.splitRingIso (FGProjectiveCat.{u} (R : Type u))).inv (K0.mk P) = _
  exact K0.splitRingIso_inv_mk (FGProjectiveCat.{u} (R : Type u)) P

/-- Canonical natural isomorphism from the group-completed projective-class
functor to the exact-category `K₀` additive functor, defined as the image of
`projectiveClassRingIso` under
`forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat`. -/
noncomputable def projectiveClassGroupIso :
    (projectiveClassGroupFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1}) ≅
      (addCommGrpFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1}) :=
  Functor.isoWhiskerRight projectiveClassRingIso
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- The component of the additive comparison `projectiveClassGroupIso` at `R` is
`K0.splitIso (FGProjectiveCat R)`, because it is obtained by forgetting the
`CommRingCat` structure from the `K0.splitRingIso` component of
`projectiveClassRingIso`. -/
@[simp]
theorem projectiveClassGroupIso_app (R : CommRingCat.{u}) :
    (projectiveClassGroupIso :
      (projectiveClassGroupFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1}) ≅
        (addCommGrpFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1})).app R =
      K0.splitIso (FGProjectiveCat.{u} (R : Type u)) := by
  change (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
      (K0.splitRingIso (FGProjectiveCat.{u} (R : Type u))) = _
  exact K0.splitRingIso_forget _

end RingK0
end AlgebraicKTheory
