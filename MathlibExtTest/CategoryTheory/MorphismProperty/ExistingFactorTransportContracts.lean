/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import MathlibExtTest.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalenceTests
import Mathlib.CategoryTheory.Category.ULift

/-!# Complete existing factor transport contracts used by original-index models -/
set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MorphismProperty

namespace MathlibExtTest.ExistingFactorTransportContracts

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L R : MorphismProperty D} [L.RespectsIso] [R.RespectsIso]
  (d : FunctorialFactorizationData L R) (e : C ≌ D)

example (f : Arrow C) :
    (d.ofEquivalence e).Z.map (𝟙 f) = 𝟙 ((d.ofEquivalence e).Z.obj f) :=
  (d.ofEquivalence e).Z.map_id f

example {f g k : Arrow C} (a : f ⟶ g) (b : g ⟶ k) :
    (d.ofEquivalence e).Z.map (a ≫ b) =
      (d.ofEquivalence e).Z.map a ≫ (d.ofEquivalence e).Z.map b :=
  (d.ofEquivalence e).Z.map_comp a b

example (f : Arrow C) :
    (d.ofEquivalence e).Z.obj f = e.inverse.obj (d.Z.obj (e.functor.mapArrow.obj f)) :=
  d.ofEquivalence_Z_obj e f

example (f : Arrow C) :
    (d.ofEquivalence e).i.app f = e.unit.app f.left ≫
      e.inverse.map (d.i.app (e.functor.mapArrow.obj f)) :=
  d.ofEquivalence_i_app e f

example (f : Arrow C) :
    (d.ofEquivalence e).p.app f =
      e.inverse.map (d.p.app (e.functor.mapArrow.obj f)) ≫ e.unitInv.app f.right :=
  d.ofEquivalence_p_app e f

example {f g : Arrow C} (a : f ⟶ g) :
    a.left ≫ (d.ofEquivalence e).i.app g =
      (d.ofEquivalence e).i.app f ≫ (d.ofEquivalence e).Z.map a :=
  (d.ofEquivalence e).i.naturality a

example {f g : Arrow C} (a : f ⟶ g) :
    (d.ofEquivalence e).Z.map a ≫ (d.ofEquivalence e).p.app g =
      (d.ofEquivalence e).p.app f ≫ a.right :=
  (d.ofEquivalence e).p.naturality a

example (f : Arrow C) :
    (d.ofEquivalence e).i.app f ≫ (d.ofEquivalence e).p.app f = f.hom :=
  d.ofEquivalence_fac_app e f

example (f : Arrow C) :
    e.functor.map ((d.ofEquivalence e).i.app f) ≫ (d.ofEquivalenceZComparisonIso e).hom.app f =
      d.i.app (e.functor.mapArrow.obj f) :=
  d.ofEquivalence_mapped_i e f

example (f : Arrow C) :
    (d.ofEquivalenceZComparisonIso e).hom.app f ≫ d.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((d.ofEquivalence e).p.app f) :=
  d.ofEquivalence_mapped_p e f

/-- The original object type is raised using its stock category. -/
local instance raisedSourceObjectCategory : Category.{vD} (ULift.{uD + 1} D) :=
  uliftCategory D
/-- The original Hom universe is independently raised using its stock category. -/
local instance raisedSourceHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example :
    FunctorialFactorizationData
      (L.inverseImage (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).inverse)
      (R.inverseImage (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).inverse) :=
  d.ofEquivalence (ULiftHomULiftCategory.equiv D).symm

end MathlibExtTest.ExistingFactorTransportContracts
