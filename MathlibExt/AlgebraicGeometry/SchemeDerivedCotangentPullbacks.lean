/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedTwoTermObstructionModels
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Actual derived module inverse images for obstruction maps

The underlying functor is the native scheme-module inverse image on
cochains followed by the native derived quotient. Its derived operator
and counit are the native total left derived constructions. In particular,
restriction to a fixed closed scheme does not assume exact pullback of
arbitrary module sheaves. The two-term vector-bundle source has its own
acyclicity comparison with that actual counit.

Sources: Stacks 08T2; Graber--Pandharipande alg-geom/9708001v2, Section1.
Only the normalized native source data are defined here; source-existence
and vector-bundle acyclicity are separate construction/proof requests.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeDerivedCotangentPullbacks

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GlobalPOTVirtualClass
attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- The exact prescribed source operator before deriving. -/
def pullbackBefore : Complex Y ⥤ D X :=
  (Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- Derivation existence concerns this particular native source functor. -/
structure DerivedPullbackSource : Prop where
  hasLeftDerived : (pullbackBefore f).HasLeftDerivedFunctor
    (HomologicalComplex.quasiIso Y.Modules (.up ℤ))

/-- The actual total left derived inverse image. -/
def derivedPullback (P : DerivedPullbackSource f) : D Y ⥤ D X :=
  letI := P.hasLeftDerived
  (pullbackBefore f).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.Modules (.up ℤ))

/-- Its native counit on every original cochain object. -/
def derivedPullbackCounit (P : DerivedPullbackSource f) :
    DerivedCategory.Q ⋙ derivedPullback f P ⟶ pullbackBefore f :=
  letI := P.hasLeftDerived
  (pullbackBefore f).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.Modules (.up ℤ))

/-- The actual two-term vector-bundle source is acyclic for this exact inverse image. -/
def SourceAcyclic (P : DerivedPullbackSource f) (E : TwoTermModel Y) : Prop :=
  IsIso ((derivedPullbackCounit f P).app (sourceComplex E))

/-- This source comparison is the same native derived counit, not a chosen source isomorphism. -/
def sourceComparison (P : DerivedPullbackSource f) (E : TwoTermModel Y)
    (h : SourceAcyclic f P E) :
    (derivedPullback f P).obj (DerivedCategory.Q.obj (sourceComplex E)) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj (sourceComplex E)) :=
  @asIso (D X) _ _ _ ((derivedPullbackCounit f P).app (sourceComplex E)) h

end MathlibExt.AlgebraicGeometry.SchemeDerivedCotangentPullbacks
