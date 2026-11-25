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

public import MathlibExt.Algebra.Category.FGProjectiveCat.Pseudofunctor
public import MathlibExt.Algebra.Category.Ring.GrothendieckRing
public import MathlibExt.CategoryTheory.Monoidal.Preadditive.Skeleton

/-!
# Functorial projective-class semiring and Grothendieck ring

For a commutative ring `R`, `Skeleton (FGProjectiveCat R)` is a commutative
semiring with addition by biproduct and multiplication by tensor product.
Base change along a ring homomorphism induces a semiring homomorphism via
`Skeleton.ringHom`, giving `projectiveClassSemiringFunctor :
CommRingCat ⥤ CommSemiRingCat`.

Its Grothendieck ring is `projectiveClassRingFunctor :
CommRingCat ⥤ CommRingCat` via `CommSemiRingCat.grothendieckRing`, and its
underlying additive group is `projectiveClassGroupFunctor :
CommRingCat ⥤ AddCommGrpCat` via the standard forgetful functors.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory
namespace RingK0

/-- Functorial projective-class semiring via skeleton and base change. -/
noncomputable def projectiveClassSemiringFunctor :
    CommRingCat.{u} ⥤ CommSemiRingCat.{u + 1} where
  obj R := CommSemiRingCat.of (Skeleton (FGProjectiveCat.{u} (R : Type u)))
  map {R S} f :=
    CommSemiRingCat.ofHom (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom))
  map_id R := by
    calc
      CommSemiRingCat.ofHom
            (Skeleton.ringHom (FGProjectiveCat.baseChange (𝟙 R : R ⟶ R).hom))
          = CommSemiRingCat.ofHom
              (Skeleton.ringHom
                (FGProjectiveCat.baseChange (RingHom.id (R : Type u)))) := by
            rw [CommRingCat.hom_id]
      _ = CommSemiRingCat.ofHom
            (Skeleton.ringHom (𝟭 (FGProjectiveCat.{u} (R : Type u)))) := by
            rw [Skeleton.ringHom_eq_of_iso (FGProjectiveCat.baseChangeId (R : Type u))]
      _ = CommSemiRingCat.ofHom
            (RingHom.id (Skeleton (FGProjectiveCat.{u} (R : Type u)))) := by
            rw [Skeleton.ringHom_id]
      _ = 𝟙 (CommSemiRingCat.of (Skeleton (FGProjectiveCat.{u} (R : Type u)))) := by
            rw [CommSemiRingCat.ofHom_id]
  map_comp {R S T} f g := by
    have hfg : (f ≫ g).hom = g.hom.comp f.hom := CommRingCat.hom_comp f g
    calc
      CommSemiRingCat.ofHom
            (Skeleton.ringHom (FGProjectiveCat.baseChange (f ≫ g).hom))
          = CommSemiRingCat.ofHom
              (Skeleton.ringHom
                (FGProjectiveCat.baseChange (g.hom.comp f.hom))) := by
            rw [hfg]
      _ = CommSemiRingCat.ofHom
            (Skeleton.ringHom
              (FGProjectiveCat.baseChange f.hom ⋙ FGProjectiveCat.baseChange g.hom)) := by
            rw [Skeleton.ringHom_eq_of_iso (FGProjectiveCat.baseChangeComp f.hom g.hom)]
      _ = CommSemiRingCat.ofHom
            ((Skeleton.ringHom (FGProjectiveCat.baseChange g.hom)).comp
              (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom))) := by
            rw [Skeleton.ringHom_comp]
      _ = CommSemiRingCat.ofHom (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom)) ≫
            CommSemiRingCat.ofHom (Skeleton.ringHom (FGProjectiveCat.baseChange g.hom)) := by
            rw [CommSemiRingCat.ofHom_comp]

@[simp]
lemma projectiveClassSemiringFunctor_obj (R : CommRingCat.{u}) :
    projectiveClassSemiringFunctor.obj R =
      CommSemiRingCat.of (Skeleton (FGProjectiveCat.{u} (R : Type u))) :=
  rfl

@[simp]
lemma projectiveClassSemiringFunctor_map_hom {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (projectiveClassSemiringFunctor.map f).hom =
      Skeleton.ringHom (FGProjectiveCat.baseChange f.hom) :=
  rfl

@[simp]
lemma projectiveClassSemiringFunctor_map_toSkeleton {R S : CommRingCat.{u}}
    (f : R ⟶ S) (M : FGProjectiveCat.{u} (R : Type u)) :
    (projectiveClassSemiringFunctor.map f) (toSkeleton M) =
      toSkeleton ((FGProjectiveCat.baseChange f.hom).obj M) := by
  change (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom)) (toSkeleton M) =
    toSkeleton ((FGProjectiveCat.baseChange f.hom).obj M)
  rw [Skeleton.ringHom_toSkeleton]

/-- Grothendieck ring of the projective-class semiring. -/
noncomputable def projectiveClassRingFunctor : CommRingCat.{u} ⥤ CommRingCat.{u + 1} :=
  projectiveClassSemiringFunctor ⋙ CommSemiRingCat.grothendieckRing

@[simp]
lemma projectiveClassRingFunctor_obj (R : CommRingCat.{u}) :
    projectiveClassRingFunctor.obj R =
      CommRingCat.of
        (Algebra.GrothendieckAddGroup (Skeleton (FGProjectiveCat.{u} (R : Type u)))) :=
  rfl

@[simp]
lemma projectiveClassRingFunctor_map_hom {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (projectiveClassRingFunctor.map f).hom =
      Algebra.GrothendieckAddGroup.mapRing
        (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom)) :=
  rfl

@[simp]
lemma projectiveClassRingFunctor_map_of_toSkeleton {R S : CommRingCat.{u}}
    (f : R ⟶ S) (M : FGProjectiveCat.{u} (R : Type u)) :
    (projectiveClassRingFunctor.map f)
        (Algebra.GrothendieckAddGroup.of (toSkeleton M)) =
      Algebra.GrothendieckAddGroup.of
        (toSkeleton ((FGProjectiveCat.baseChange f.hom).obj M)) := by
  change (Algebra.GrothendieckAddGroup.mapRing
      (Skeleton.ringHom (FGProjectiveCat.baseChange f.hom)))
      (Algebra.GrothendieckAddGroup.of (toSkeleton M)) =
    Algebra.GrothendieckAddGroup.of
      (toSkeleton ((FGProjectiveCat.baseChange f.hom).obj M))
  rw [Algebra.GrothendieckAddGroup.mapRing_of, Skeleton.ringHom_toSkeleton]

/-- Additive group underlying the projective-class ring functor. -/
noncomputable def projectiveClassGroupFunctor :
    CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  projectiveClassRingFunctor ⋙
    forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat

end RingK0
end AlgebraicKTheory
