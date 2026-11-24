/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionIntertwinerCoherence

/-!
# Scalar-extension intertwiner coherence clients

These clients use the generic coherence API through its neutral import.
The whole composition squares retain independent ring universes and the
original ordered pure coefficients. The equality comparison returns the
same original tensor/shrink representative.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory ModuleCat.RingHomScalarExtension

universe uR uS uT

namespace FGProjectiveCat.ScalarExtensionIntertwinerCoherenceTests

variable {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]

/-- The pushed coefficient square is available without a cone absorption import. -/
theorem neutral_pushforward (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) :
    Functor.whiskerRight (ringScalarExtensionIntertwiner f g c hc) (ringScalarExtension k) ≫
        (ringScalarExtensionCompIso g k).hom =
      (ringScalarExtensionCompIso f k).hom ≫
        ringScalarExtensionIntertwiner (k.comp f) (k.comp g) (k c) (hc.map k) :=
  ringScalarExtensionIntertwiner_pushforward f g c hc k

/-- The source-composition square uses the predicate's canonical precomposition operation. -/
theorem neutral_precompose (k : R →+* S) (f g : S →+* T) (c : T)
    (hc : Intertwines f g c) :
    Functor.whiskerLeft (ringScalarExtension k) (ringScalarExtensionIntertwiner f g c hc) ≫
        (ringScalarExtensionCompIso k g).hom =
      (ringScalarExtensionCompIso k f).hom ≫
        ringScalarExtensionIntertwiner (f.comp k) (g.comp k) c (hc.precomp k) :=
  ringScalarExtensionIntertwiner_precompose k f g c hc

/-- Further scalar extension retains the original coefficient product on nested pure classes. -/
theorem pushforward_on_original_pure (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) (X : FGProjectiveCat.{uR} R)
    (t : T) (s : S) (x : X) :
    ((ringScalarExtensionCompIso g k).hom.app X).hom.hom
        (((ringScalarExtension k).map
          ((ringScalarExtensionIntertwiner f g c hc).app X)).hom.hom
          ((ringScalarExtensionCoordinates k ((ringScalarExtension f).obj X)).symm
            (pure k ((ringScalarExtension f).obj X) t
              ((ringScalarExtensionCoordinates f X).symm (pure f X s x))))) =
      (ringScalarExtensionCoordinates (k.comp g) X).symm
        (pure (k.comp g) X (t * k (s * c)) x) := by
  rw [ringScalarExtension_map_pure, ringScalarExtensionIntertwiner_apply_pure,
    ringScalarExtensionCompIso_hom_apply_pure]

/-- Source precomposition retains the coefficient before the mapped original inner scalar. -/
theorem precompose_on_original_pure (k : R →+* S) (f g : S →+* T) (c : T)
    (hc : Intertwines f g c) (X : FGProjectiveCat.{uR} R) (t : T) (s : S) (x : X) :
    ((ringScalarExtensionCompIso k g).hom.app X).hom.hom
        (((ringScalarExtensionIntertwiner f g c hc).app
          ((ringScalarExtension k).obj X)).hom.hom
          ((ringScalarExtensionCoordinates f ((ringScalarExtension k).obj X)).symm
            (pure f ((ringScalarExtension k).obj X) t
              ((ringScalarExtensionCoordinates k X).symm (pure k X s x))))) =
      (ringScalarExtensionCoordinates (g.comp k) X).symm
        (pure (g.comp k) X ((t * c) * g s) x) := by
  rw [ringScalarExtensionIntertwiner_apply_pure, ringScalarExtensionCompIso_hom_apply_pure]

/-- Both equality maps retain the same original pure representative in the round trip. -/
theorem equality_original_pure_return (f g : R →+* S) (h : f = g)
    (X : FGProjectiveCat.{uR} R) (s : S) (x : X) :
    ((ringScalarExtensionHomEqualityIso f g h).inv.app X).hom.hom
        (((ringScalarExtensionHomEqualityIso f g h).hom.app X).hom.hom
          ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) =
      (ringScalarExtensionCoordinates f X).symm (pure f X s x) := by
  rw [ringScalarExtensionHomEqualityIso_hom_pure, ringScalarExtensionHomEqualityIso_inv_pure]

end FGProjectiveCat.ScalarExtensionIntertwinerCoherenceTests

end
