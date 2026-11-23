/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.KTheory.Ring.K0.Projective

/-!
# Quillen and K0 maps of associative-ring scalar extension

The balanced tensor and finite-projective functors are defined in Algebra.
This module supplies their actual Quillen maps, selected-zero comparisons and
additive K0 maps without changing those functor or map programs.
-/

public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped ZeroObject
universe uR uS uP uMR uMS uOR uHR uOS uHS
namespace FGProjectiveCat
variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual Quillen functor induced by noncommutative scalar extension. -/
@[expose] def scalarExtensionQ (f : R →+* S) :
    AlgebraicKTheory.QuillenQ (FGProjectiveCat.{uP} R) ⥤
      AlgebraicKTheory.QuillenQ (FGProjectiveCat.{max uS uP} S) :=
  AlgebraicKTheory.QuillenQ.map (scalarExtension f)

/-- The canonical zero comparison for the same actual Quillen functor. -/
def scalarExtensionQZeroIso (f : R →+* S) :
    (scalarExtensionQ.{uR,uS,uP} f).obj ⟨0⟩ ≅
      (⟨0⟩ : AlgebraicKTheory.QuillenQ (FGProjectiveCat.{max uS uP} S)) :=
  AlgebraicKTheory.QuillenQ.zeroComparisonIso (scalarExtension f)

/-- The all-projective additive RingK0 map of the same scalar-extension functor. -/
def scalarExtensionK0 (f : R →+* S) :
    AlgebraicKTheory.RingK0 R →+ AlgebraicKTheory.RingK0 S :=
  AlgebraicKTheory.K0.map (ringScalarExtension f)

/-- Every actual projective generator maps to its scalar extension, independently of any HE. -/
theorem scalarExtensionK0_mk (f : R →+* S) (P : FGProjectiveCat.{uR} R) :
    scalarExtensionK0 f (AlgebraicKTheory.K0.mk P) =
      AlgebraicKTheory.K0.mk ((ringScalarExtension f).obj P) :=
  AlgebraicKTheory.K0.map_mk (ringScalarExtension f) P

/-- The actual Quillen map on independently parameterized category object and Hom universes. -/
@[expose] def liftedScalarExtensionQ (f : R →+* S) :
    AlgebraicKTheory.QuillenQ (CategoryUniverseLift.category.{uR,uMR,uOR,uHR} R) ⥤
      AlgebraicKTheory.QuillenQ (CategoryUniverseLift.category.{uS,uMS,uOS,uHS} S) :=
  AlgebraicKTheory.QuillenQ.map
    (liftedScalarExtension.{uR,uS,uMR,uMS,uOR,uHR,uOS,uHS} f)

/-- The canonical mapped-zero-to-selected-zero Iso of the same lifted Quillen map. -/
def liftedScalarExtensionQZeroIso (f : R →+* S) :
    (liftedScalarExtensionQ.{uR,uS,uMR,uMS,uOR,uHR,uOS,uHS} f).obj ⟨0⟩ ≅
      (⟨0⟩ : AlgebraicKTheory.QuillenQ
        (CategoryUniverseLift.category.{uS,uMS,uOS,uHS} S)) :=
  AlgebraicKTheory.QuillenQ.zeroComparisonIso
    (liftedScalarExtension.{uR,uS,uMR,uMS,uOR,uHR,uOS,uHS} f)

end FGProjectiveCat
