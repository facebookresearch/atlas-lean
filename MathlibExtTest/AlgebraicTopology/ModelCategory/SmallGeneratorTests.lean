/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v v' v'' u u' u''

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.SmallGeneratorTests

section StrictImageSmallness

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]
variable (I J : MorphismProperty C)
variable (hI : I.IsSmall.{w}) (hJ : J.IsSmall.{w})
variable (F : C ⥤ D) (H : C ⥤ E)

example : (I.strictMap F).IsSmall.{w} := hI.strictMap F
example : (J.strictMap H).IsSmall.{w} := hJ.strictMap H

example {X Y : C} (f : X ⟶ Y) (hf : I f) :
    I.strictMap F (F.map f) :=
  ⟨hf⟩

example [I.IsSmall.{w}] : True := by
  fail_if_success
    have _ : (I.strictMap F).IsSmall.{w} := inferInstance
  trivial

end StrictImageSmallness

section AdjunctionRlp

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]
variable {F : C ⥤ D} {G : D ⥤ C}
variable {L : C ⥤ E} {R : E ⥤ C}
variable (adj : F ⊣ G) (adj' : L ⊣ R)
variable (I J : MorphismProperty C)

example : (I.strictMap F).rlp = I.rlp.inverseImage G :=
  strictMap_rlp_eq_inverseImage_rlp I F G adj

example : (J.strictMap L).rlp = J.rlp.inverseImage R :=
  strictMap_rlp_eq_inverseImage_rlp J L R adj'

example {X Y : D} (p : X ⟶ Y) :
    (I.strictMap F).rlp p ↔ I.rlp (G.map p) := by
  rw [strictMap_rlp_eq_inverseImage_rlp I F G adj]
  rfl

example (_K : MorphismProperty D) : True := by
  fail_if_success
    have _ : (_K.strictMap G).rlp = _K.rlp.inverseImage F :=
      strictMap_rlp_eq_inverseImage_rlp _K G F adj
  trivial

end AdjunctionRlp

section SmallObjectArgument

variable {C : Type u} [Category.{v} C]
variable (I : MorphismProperty C)
variable [IsLocallyPresentable.{w} C] [I.IsSmall.{w}]

example : I.HasSmallObjectArgument.{w} :=
  hasSmallObjectArgument_of_isSmall I

example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular)
      (_ : OrderBot κ.ord.ToType),
      I.IsCardinalForSmallObjectArgument κ := by
  let _ : I.HasSmallObjectArgument.{w} :=
    hasSmallObjectArgument_of_isSmall I
  exact HasSmallObjectArgument.exists_cardinal

example : Nonempty (FunctorialFactorizationData I.rlp.llp I.rlp) := by
  let _ : I.HasSmallObjectArgument.{w} :=
    hasSmallObjectArgument_of_isSmall I
  exact ⟨functorialFactorizationData I.rlp.llp I.rlp⟩

example : True := by
  fail_if_success
    have _ : I.HasSmallObjectArgument.{w} := inferInstance
  trivial

end SmallObjectArgument

section MissingPremises

variable {C : Type u} [Category.{v} C]

section MissingSmallness

variable [IsLocallyPresentable.{w} C]
variable (I : MorphismProperty C)

example : True := by
  fail_if_success
    have _ : I.HasSmallObjectArgument.{w} :=
      hasSmallObjectArgument_of_isSmall I
  trivial

end MissingSmallness

section MissingPresentability

variable (I : MorphismProperty C) [I.IsSmall.{w}]

example : True := by
  fail_if_success
    have _ : I.HasSmallObjectArgument.{w} :=
      hasSmallObjectArgument_of_isSmall I
  trivial

end MissingPresentability

end MissingPremises

section UniverseOneClients

variable {C₁ D₁ : Type 1} [Category.{0} C₁] [Category.{0} D₁]
variable (I₁ : MorphismProperty C₁) (hI₁ : I₁.IsSmall.{1})
variable (F₁ : C₁ ⥤ D₁)

example : (I₁.strictMap F₁).IsSmall.{1} := hI₁.strictMap F₁

variable [IsLocallyPresentable.{1} C₁] [I₁.IsSmall.{1}]

example : I₁.HasSmallObjectArgument.{1} :=
  hasSmallObjectArgument_of_isSmall I₁

end UniverseOneClients

section UniverseZeroClients

variable {C₀ D₀ : Type} [Category C₀] [Category D₀]
variable (I₀ : MorphismProperty C₀) (hI₀ : I₀.IsSmall.{0})
variable (F₀ : C₀ ⥤ D₀)

example : (I₀.strictMap F₀).IsSmall.{0} := hI₀.strictMap F₀

variable [IsLocallyPresentable.{0} C₀] [I₀.IsSmall.{0}]

example : I₀.HasSmallObjectArgument.{0} :=
  hasSmallObjectArgument_of_isSmall I₀

end UniverseZeroClients

end CategoryTheory.SmallGeneratorTests

#check CategoryTheory.MorphismProperty.IsSmall.strictMap
#check CategoryTheory.MorphismProperty.hasSmallObjectArgument_of_isSmall

#print axioms CategoryTheory.MorphismProperty.IsSmall.strictMap
#print axioms CategoryTheory.MorphismProperty.hasSmallObjectArgument_of_isSmall
