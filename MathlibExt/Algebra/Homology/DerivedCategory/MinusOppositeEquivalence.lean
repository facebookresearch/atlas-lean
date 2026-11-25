/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.DerivedCategory.Opposite

/-!
# Canonical native Minus and opposite Plus

Restrict the earned derived opposite equivalence using the exact native
cohomological bound reflection. The functors retain the original derived
objects and maps, and their round trips are the native unit and counit.
No equivalence or bound certificate is supplied by a caller.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v w w'

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} Cᵒᵖ]

/-- The actual reflected native bounded-above derived object, in opposite native Plus. -/
def minusToOppositePlus : Minus C ⥤ (Plus Cᵒᵖ)ᵒᵖ where
  obj X := op
    { obj := OppositeTransport.reflect C X.obj
      property := by
        obtain ⟨n, hn⟩ := X.property
        exact ⟨-n, (OppositeTransport.isLE_iff_reflect_isGE C X.obj n).1 hn⟩ }
  map f := (ObjectProperty.homMk
    ((OppositeTransport.equivalence C).functor.map f.hom.op)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact (OppositeTransport.equivalence C).functor.map_id (op X.obj)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact (OppositeTransport.equivalence C).functor.map_comp g.hom.op f.hom.op

/-- The actual inverse reflection of a native Plus object is in canonical Minus. -/
def oppositePlusToMinus : (Plus Cᵒᵖ)ᵒᵖ ⥤ Minus C where
  obj X :=
    { obj := unop ((OppositeTransport.equivalence C).inverse.obj (unop X).obj)
      property := by
        obtain ⟨n, hn⟩ := (unop X).property
        exact ⟨-n, OppositeTransport.inverse_isLE_of_isGE C (unop X).obj (-n)
          (by simpa only [neg_neg] using hn)⟩ }
  map f := ObjectProperty.homMk
    ((OppositeTransport.equivalence C).inverse.map f.unop.hom).unop
  map_id X := by
    apply ObjectProperty.hom_ext
    exact congrArg Quiver.Hom.unop ((OppositeTransport.equivalence C).inverse.map_id (unop X).obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact congrArg Quiver.Hom.unop
      ((OppositeTransport.equivalence C).inverse.map_comp g.unop.hom f.unop.hom)

/-- The canonical bounded-above derived category is the earned opposite native bounded-below category. -/
def minusOppositeEquivalence : Minus C ≌ (Plus Cᵒᵖ)ᵒᵖ := by
  let unit : 𝟭 (Minus C) ≅ minusToOppositePlus C ⋙ oppositePlusToMinus C :=
    NatIso.ofComponents
      (fun X => ObjectProperty.isoMk (DerivedCategory.TStructure.t (C := C)).minus
        ((OppositeTransport.equivalence C).unitIso.app (op X.obj)).unop.symm)
      (by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply Quiver.Hom.op_inj
        exact ((OppositeTransport.equivalence C).unitIso.inv.naturality f.hom.op).symm)
  let counit : oppositePlusToMinus C ⋙ minusToOppositePlus C ≅ 𝟭 ((Plus Cᵒᵖ)ᵒᵖ) :=
    NatIso.ofComponents
      (fun X => (ObjectProperty.isoMk (DerivedCategory.TStructure.t (C := Cᵒᵖ)).plus
        ((OppositeTransport.equivalence C).counitIso.app (unop X).obj).symm).op)
      (by
        intro X Y f
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        exact ((OppositeTransport.equivalence C).counitIso.inv.naturality f.unop.hom).symm)
  exact CategoryTheory.Equivalence.mk (minusToOppositePlus C) (oppositePlusToMinus C) unit counit

end DerivedCategory

end
