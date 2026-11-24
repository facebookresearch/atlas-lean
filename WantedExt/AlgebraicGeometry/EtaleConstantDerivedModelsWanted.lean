/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EtaleGaloisStalkActions

/-!
# Source adapters for base evaluation cones and native field Galois actions

Every derived adjunction is normalized on all cochain units. The base
evaluation and its sheaf cone are fixed before taking the generic stalk;
the cohomological Galois action must agree with every actual automorphism
operator. These requests contain no Milnor formula or conductor value.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EtaleConstantDerivedModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open AdicDerivedContracts EtaleConstantDerivedModels EtaleGaloisStalkActions

def_wanted nativeDerivedConstantAdjunction (Λ : Type) [CommRing Λ]
    (X : Scheme.{0}) : DerivedConstantAdjunction Λ X

def_wanted nativeBaseVanishingModel (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]
    (X Y : Scheme.{0}) (f : X ⟶ Y) (F : Derived Λ X)
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y] :
    BaseVanishingModel Λ f F

def_wanted nativeFieldGaloisAction (Λ K : Type) [CommRing Λ] [Field K]
    [DerivedFunctorTheory Λ] (F : Derived Λ (Spec (.of K))) (q : ℤ) : SourceAction Λ K F q

private def check_nativeDerivedConstantAdjunction (Λ : Type) [CommRing Λ]
    (X : Scheme.{0}) : DefWanted (DerivedConstantAdjunction Λ X) :=
  nativeDerivedConstantAdjunction Λ X

private def check_nativeBaseVanishingModel (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]
    (X Y : Scheme.{0}) (f : X ⟶ Y) (F : Derived Λ X)
    [DerivedConstantAdjunction Λ X] [DerivedConstantAdjunction Λ Y] :
    DefWanted (BaseVanishingModel Λ f F) := nativeBaseVanishingModel Λ X Y f F

private def check_nativeFieldGaloisAction (Λ K : Type) [CommRing Λ] [Field K]
    [DerivedFunctorTheory Λ] (F : Derived Λ (Spec (.of K))) (q : ℤ) :
    DefWanted (SourceAction Λ K F q) := nativeFieldGaloisAction Λ K F q

end WantedExt.AlgebraicGeometry.EtaleConstantDerivedModelsWanted
