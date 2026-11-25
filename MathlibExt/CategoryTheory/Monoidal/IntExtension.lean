/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntRigid
public import MathlibExt.CategoryTheory.Monoidal.IntMapMonoidal

/-!
# Extending traced functors to compact targets

A trace-preserving strong symmetric monoidal functor from a traced category to a
symmetric right-rigid category extends along the canonical Int embedding. The
extension is strong symmetric monoidal and its factorization isomorphism is
monoidal. On objects, it is isomorphic to the positive image tensored with the
right dual of the negative image.

This is the existence clause of Joyal, Street and Verity, Traced monoidal
categories (1996), Proposition 5.2, https://doi.org/10.1017/S0305004100074338,
in the symmetric specialization. Uniqueness up to monoidal natural isomorphism
and the full bicategorical universal property are not asserted here.
-/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  [RightRigidCategory D]
namespace IntConstruction
variable (T : SymmetricTrace C) (F : C ⥤ D) [F.Braided]
variable (hF : T.Preserves (symmetricTraceOfRigid D) F)

/-- Extend a traced functor by mapping formal pairs and recovering the rigid target. -/
def extend : IntConstruction T ⥤ D :=
  map T (symmetricTraceOfRigid D) F hF ⋙ (rigidEquivalence (symmetricTraceOfRigid D)).inverse

/-- The compact-target extension retains the induced strong symmetric monoidal structure. -/
instance extendBraided : (extend T F hF).Braided :=
  inferInstanceAs ((map T (symmetricTraceOfRigid D) F hF ⋙
    (rigidEquivalence (symmetricTraceOfRigid D)).inverse).Braided)

/-- The extension represents a formal pair by its positive image and dual negative image. -/
def extendObjIso (X : IntConstruction T) :
    (extend T F hF).obj X ≅ F.obj X.positive ⊗ (F.obj X.negative)ᘁ :=
  rigidInverseObjIso (symmetricTraceOfRigid D) ((map T (symmetricTraceOfRigid D) F hF).obj X)

/-- Restriction of the extension to the original category recovers the given functor. -/
def extensionIso : embedding T ⋙ extend T F hF ≅ F :=
  (Functor.associator (embedding T) (map T (symmetricTraceOfRigid D) F hF)
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse).symm ≪≫
    Functor.isoWhiskerRight (embeddingMapIso T (symmetricTraceOfRigid D) F hF)
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse ≪≫
    Functor.associator F (embedding (symmetricTraceOfRigid D))
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse ≪≫
    Functor.isoWhiskerLeft F (rigidEquivalence (symmetricTraceOfRigid D)).unitIso.symm ≪≫
    F.rightUnitor

set_option backward.defeqAttrib.useBackward true in
/-- The factorization isomorphism respects the strong monoidal structures. -/
instance extensionIso_hom_isMonoidal : NatTrans.IsMonoidal (extensionIso T F hF).hom := by
  let : NatTrans.IsMonoidal (rigidEquivalence (symmetricTraceOfRigid D)).unitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (rigidEquivalence (symmetricTraceOfRigid D)).unit)
  exact inferInstanceAs (NatTrans.IsMonoidal (
    (Functor.associator (embedding T) (map T (symmetricTraceOfRigid D) F hF)
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse).inv ≫
    Functor.whiskerRight (embeddingMapIso T (symmetricTraceOfRigid D) F hF).hom
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse ≫
    (Functor.associator F (embedding (symmetricTraceOfRigid D))
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse).hom ≫
    Functor.whiskerLeft F (rigidEquivalence (symmetricTraceOfRigid D)).unitIso.inv ≫
    F.rightUnitor.hom))

/-- The extension preserves the canonical compact traces. -/
theorem extend_preserves_trace :
    (symmetricTraceOfRigid (IntConstruction T)).Preserves (symmetricTraceOfRigid D)
      (extend T F hF) := SymmetricTrace.preserves_of_rigid _

end IntConstruction
end CategoryTheory
