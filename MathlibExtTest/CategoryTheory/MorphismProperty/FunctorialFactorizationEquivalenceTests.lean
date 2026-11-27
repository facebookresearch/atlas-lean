/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

@[expose] public section
set_option autoImplicit false
noncomputable section
universe vC vD uC uD
open CategoryTheory CategoryTheory.MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData

namespace FunctorialFactorizationEquivalenceOwner

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty D} [W₁.RespectsIso] [W₂.RespectsIso]
  (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D)

example : FunctorialFactorizationData (W₁.inverseImage e.functor) (W₂.inverseImage e.functor) :=
  data.ofEquivalence e

example : (data.ofEquivalence e).Z = e.functor.mapArrow ⋙ data.Z ⋙ e.inverse :=
  data.ofEquivalence_Z e

example (f : Arrow C) : (data.ofEquivalence e).Z.obj f =
    e.inverse.obj (data.Z.obj (e.functor.mapArrow.obj f)) := data.ofEquivalence_Z_obj e f

example {f g : Arrow C} (φ : f ⟶ g) : (data.ofEquivalence e).Z.map φ =
    e.inverse.map (data.Z.map (e.functor.mapArrow.map φ)) := data.ofEquivalence_Z_map e φ

example (f : Arrow C) : (data.ofEquivalence e).i.app f = e.unitIso.hom.app f.left ≫
    e.inverse.map (data.i.app (e.functor.mapArrow.obj f)) := data.ofEquivalence_i_app e f

example (f : Arrow C) : (data.ofEquivalence e).p.app f =
    e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫ e.unitIso.inv.app f.right :=
  data.ofEquivalence_p_app e f

example (f : Arrow C) : (data.ofEquivalence e).i.app f ≫ (data.ofEquivalence e).p.app f = f.hom :=
  data.ofEquivalence_fac_app e f

example (f : Arrow C) : (W₁.inverseImage e.functor) ((data.ofEquivalence e).i.app f) :=
  (data.ofEquivalence e).hi f

example (f : Arrow C) : (W₂.inverseImage e.functor) ((data.ofEquivalence e).p.app f) :=
  (data.ofEquivalence e).hp f

example {f g : Arrow C} (φ : f ⟶ g) :
    φ.left ≫ (data.ofEquivalence e).i.app g =
      (data.ofEquivalence e).i.app f ≫ (data.ofEquivalence e).Z.map φ :=
  (data.ofEquivalence e).i.naturality φ

example {f g : Arrow C} (φ : f ⟶ g) :
    (data.ofEquivalence e).Z.map φ ≫ (data.ofEquivalence e).p.app g =
      (data.ofEquivalence e).p.app f ≫ φ.right :=
  (data.ofEquivalence e).p.naturality φ

example (f : Arrow C) : e.functor.map ((data.ofEquivalence e).i.app f) ≫
    (data.ofEquivalenceZComparisonIso e).hom.app f = data.i.app (e.functor.mapArrow.obj f) :=
  data.ofEquivalence_mapped_i e f

example (f : Arrow C) : (data.ofEquivalenceZComparisonIso e).hom.app f ≫
    data.p.app (e.functor.mapArrow.obj f) = e.functor.map ((data.ofEquivalence e).p.app f) :=
  data.ofEquivalence_mapped_p e f

example {f g : Arrow C} (φ : f ⟶ g) :
    e.functor.map ((data.ofEquivalence e).Z.map φ) ≫
        (data.ofEquivalenceZComparisonIso e).hom.app g =
      (data.ofEquivalenceZComparisonIso e).hom.app f ≫ data.Z.map (e.functor.mapArrow.map φ) :=
  (data.ofEquivalenceZComparisonIso e).hom.naturality φ

set_option pp.universes true
#check @ofEquivalence
#check @ofEquivalence_Z
#check @ofEquivalence_Z_obj
#check @ofEquivalence_Z_map
#check @ofEquivalence_i_app
#check @ofEquivalence_p_app
#check @ofEquivalence_fac_app
#check @ofEquivalenceZComparisonIso
#check @ofEquivalence_mapped_i
#check @ofEquivalence_mapped_p

#print axioms ofEquivalence
#print axioms ofEquivalence_Z
#print axioms ofEquivalence_Z_obj
#print axioms ofEquivalence_Z_map
#print axioms ofEquivalence_i_app
#print axioms ofEquivalence_p_app
#print axioms ofEquivalence_fac_app
#print axioms ofEquivalenceZComparisonIso
#print axioms ofEquivalence_mapped_i
#print axioms ofEquivalence_mapped_p

#lint only unusedArguments in MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

end FunctorialFactorizationEquivalenceOwner
