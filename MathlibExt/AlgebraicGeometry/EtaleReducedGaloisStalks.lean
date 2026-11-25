/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleGaloisStalkActions
public import MathlibExt.RingTheory.DerivedModuleScalarOperations

/-!
# Actual derived coefficient reduction of Galois stalks

The reduced object is the native derived scalar extension of the original
geometric stalk along the given coefficient ring map. Each Galois operator
is the image of the original spectrum-induced operator under that same
functor, followed by actual homology. Finite local coefficients can use
their native residue-field map; no replacement representation is chosen.

Reference: Saito, arXiv:1510.03018v4, Sections 1.1 and 1.3, and the
coefficient reduction in the proof of Theorem 4.9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleReducedGaloisStalks

open _root_.CategoryTheory _root_.AlgebraicGeometry
open AdicDerivedContracts EtaleGaloisStalkActions
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations

attribute [local instance] HasDerivedCategory.standard

variable (Λ κ : Type) [CommRing Λ] [CommRing κ]
  (r : Λ →+* κ) [HasExtension r] [DerivedFunctorTheory Λ]
  (K : Type) [Field K] (F : Derived Λ (Spec (.of K)))

def reduced : DerivedCategory (ModuleCat.{1} κ) :=
  (extension r).obj (fieldStalk Λ K F).obj

def cohomology (q : ℤ) : ModuleCat.{1} κ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{1} κ) q).obj (reduced Λ κ r K F)

def operator (q : ℤ) (g : Field.absoluteGaloisGroup K) :
    Module.End κ (cohomology Λ κ r K F q) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{1} κ) q).map
    ((extension r).map (deckOperator Λ K F g).hom)).hom

/-- The action is fixed on each original Galois operator after actual reduction. -/
structure SourceAction (q : ℤ) where
  action : Field.absoluteGaloisGroup K →* Module.End κ (cohomology Λ κ r K F q)
  normalized : ∀ g, action g = operator Λ κ r K F q g

end MathlibExt.AlgebraicGeometry.EtaleReducedGaloisStalks
