/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
public import Batteries.Util.ProofWanted

/-!
# Pointed marked first-order class existence on the actual cotangent cone

This is a pointed class-level construction on actual square-zero marked
families. The vector is H0 of the computed marked cotangent deformation
cone; the target is the actual family-isomorphism quotient. The origin
is the genuine Cartesian constant deformation. This only requests a
pointed set equivalence; it does not determine a canonical cotangent
class map, its linearity, or its naturality. The actual evaluation of
these classes is defined separately in MarkedFirstOrderFamilies, and
the normalized universal fixed-Hom derivative comparison is recorded
in MarkedHomEvaluationDifferentialsWanted.

Generic cotangent/square-zero classes are completed source integration;
the native marked-family/cone comparison is the requested bridge.
References: Behrend--Fantechi alg-geom/9601010 §4;
Graber--Harris--Starr math/0109220v1 §2.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.MarkedFirstOrderFamilies
attribute [local instance] HasDerivedCategory.standard

def_wanted markedFirstOrderPointedClassEquivalence
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    {V S : Scheme.{0}} {q : V ⟶ S} {n g : ℕ}
    {Ω : Type} [Field Ω] {b : Spec (.of Ω) ⟶ S}
    (F : Family q n g (Spec (.of Ω)) b) (stable : IsGeometricallyStable F)
    (P : CotangentNormalization F.curve.π)
    (Q : CotangentNormalization (pullback.snd q b))
    (D : RelativeDifferential (mapToRelativeTarget F) (pullback.lift_snd _ _ _) P Q)
    [((derivedTensor F.curve.X).obj (DerivedCategory.Q.obj P.complex)).IsLeftAdjoint]
    [((derivedTensor F.curve.X).obj
      ((derivedPullback (mapToRelativeTarget F)).obj
        (DerivedCategory.Q.obj Q.complex))).IsLeftAdjoint]
    (C : ConeModel (markedArrow F P Q D)) (T : TrivialDeformation F) :
    {e : GenericSectionMaps.Sections (Over.mk (𝟙 (Spec (.of Ω))))
        ((DerivedCategory.homologyFunctor (Spec (.of Ω)).Modules 0).obj
          (markedDeformation F P Q D C)) ≃ DeformationClasses F //
      e 0 = deformationClass F T.deformation}

end MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
