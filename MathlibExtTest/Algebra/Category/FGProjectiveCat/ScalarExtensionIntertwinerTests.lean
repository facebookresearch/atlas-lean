/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionIntertwiner

/-!
# Clients of the original coefficient transformations

The clients compose the actual native coefficient maps, keep their
noncommutative multiplication order, and test the original naturality
square at an independent source-module universe.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory ModuleCat.RingHomScalarExtension

universe uR uS uT uP

namespace FGProjectiveCat.ScalarExtensionIntertwinerTests

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

-- The predicate's relation API is available from this scalar-extension import alone.
example {T : Type uT} [Ring T] (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) (k : S →+* T) :
    Intertwines (k.comp f) (k.comp g) (k c) := hc.map k

example {T : Type uT} [Ring T] (f g : S →+* T) (c : T)
    (hc : Intertwines f g c) (k : R →+* S) :
    Intertwines (f.comp k) (g.comp k) c := hc.precomp k

example (f g : R →+* S) (h : f = g) : Intertwines f g 1 :=
  ModuleCat.RingHomScalarExtension.Intertwines.of_eq h

/-- The actual raw square remains available at an independent module universe. -/
theorem raw_universe_square (f g : R →+* S) (c : S) (hc : Intertwines f g c)
    {X Y : FGProjectiveCat.{uP} R} (v : X ⟶ Y) :
    (scalarExtension f).map v ≫
        (scalarExtensionIntertwiner.{uR, uS, uP} f g c hc).app Y =
      (scalarExtensionIntertwiner.{uR, uS, uP} f g c hc).app X ≫
        (scalarExtension g).map v :=
  (scalarExtensionIntertwiner.{uR, uS, uP} f g c hc).naturality v

/-- Two actual native coefficient maps preserve the original ordered product. -/
theorem two_native_coefficients (f g h : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines g h d)
    (X : FGProjectiveCat.{uR} R) (s : S) (x : X) :
    ((ringScalarExtensionIntertwiner g h d hd).app X).hom.hom
        (((ringScalarExtensionIntertwiner f g c hc).app X).hom.hom
          ((ringScalarExtensionCoordinates f X).symm (pure f X s x))) =
      (ringScalarExtensionCoordinates h X).symm (pure h X (s * (c * d)) x) := by
  rw [ringScalarExtensionIntertwiner_apply_pure,
    ringScalarExtensionIntertwiner_apply_pure, mul_assoc]

/-- The actual product coefficient has the original composite naturality square. -/
theorem product_coefficient_square (f g h : R →+* S) (c d : S)
    (hc : Intertwines f g c) (hd : Intertwines g h d)
    {X Y : FGProjectiveCat.{uR} R} (v : X ⟶ Y) :
    (ringScalarExtension f).map v ≫
        (ringScalarExtensionIntertwiner f h (c * d) (hc.mul hd)).app Y =
      (ringScalarExtensionIntertwiner f g c hc).app X ≫
        (ringScalarExtensionIntertwiner g h d hd).app X ≫ (ringScalarExtension h).map v := by
  rw [← ringScalarExtensionIntertwiner_comp f g h c d hc hd]
  simpa only [NatTrans.comp_app, Category.assoc] using
    (ringScalarExtensionIntertwiner f g c hc ≫
      ringScalarExtensionIntertwiner g h d hd).naturality v

/-- The original unit coefficient acts as the actual native identity before another coefficient. -/
theorem native_unit_before_coefficient (f g : R →+* S) (c : S)
    (hc : Intertwines f g c) :
    ringScalarExtensionIntertwiner f f 1 (Intertwines.one f) ≫
        ringScalarExtensionIntertwiner f g c hc = ringScalarExtensionIntertwiner f g c hc := by
  rw [ringScalarExtensionIntertwiner_one, Category.id_comp]

end FGProjectiveCat.ScalarExtensionIntertwinerTests

end
