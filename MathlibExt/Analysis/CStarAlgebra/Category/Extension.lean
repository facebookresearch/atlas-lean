/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Category.Basic
public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic
public import Mathlib.CategoryTheory.NatTrans

/-!
# The category of normalized C-star extensions

Objects use the existing closed-ideal/quotient normalization. Its inclusion,
quotient and exactness are derived, not additional stored conclusions.
Morphisms are the existing extension diagrams with both endpoint maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/-- **Category of normalized C*-extensions.** A normalized extension of nonunital complex C*-algebras
has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. Objects are these extensions; morphisms are
compatible homomorphisms on their endpoints and middle algebras. -/
structure CStarExtensionCat : Type (u + 1) where
  /-- The quotient algebra of the normalized extension. -/
  quotient : NonUnitalCStarAlgCat.{u}
  /-- The ideal algebra of the normalized extension. -/
  ideal : NonUnitalCStarAlgCat.{u}
  /-- The actual normalized extension with these quotient and ideal endpoints. -/
  extension : CStarExtension.{u, u, u} quotient ideal

namespace CStarExtensionCat

instance category : Category.{u} CStarExtensionCat.{u} where
  Hom X Y := CStarExtension.Hom X.extension Y.extension
  id X := CStarExtension.Hom.id X.extension
  comp f g := CStarExtension.Hom.comp g f
  id_comp := by
    intro X Y f
    exact CStarExtension.Hom.comp_id f
  comp_id := by
    intro X Y f
    exact CStarExtension.Hom.id_comp f
  assoc := by
    intro X Y Z W f g h
    exact CStarExtension.Hom.comp_assoc h g f

/-- **Normalized C*-extension as an object.** A normalized extension of nonunital complex C*-algebras
has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. It determines an object of the extension
category with the same endpoint and middle algebras and maps. -/
def ofExtension {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (E : CStarExtension.{u, u, u} A B) : CStarExtensionCat.{u} where
  quotient := NonUnitalCStarAlgCat.of A
  ideal := NonUnitalCStarAlgCat.of B
  extension := E

/-- **Middle algebra of a C*-extension.** A normalized extension of nonunital complex C*-algebras has an
ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. The middle algebra is an object of the
nonunital complex C*-algebra category. -/
def middle (E : CStarExtensionCat.{u}) : NonUnitalCStarAlgCat.{u} :=
  NonUnitalCStarAlgCat.of E.extension.Middle

/-- **Ideal functor of C*-extensions.** A normalized extension of nonunital complex C*-algebras has an
ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. Sending an extension to its ideal endpoint
and a compatible extension morphism to its ideal map defines a functor to nonunital complex
C*-algebras. -/
def idealFunctor : CStarExtensionCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj E := E.ideal
  map f := f.idealMap
  map_id _E := rfl
  map_comp _f _g := rfl

/-- **Middle-algebra functor of C*-extensions.** A normalized extension of nonunital complex C*-algebras
has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. Sending an extension to its middle algebra
and a compatible extension morphism to its middle map defines a functor to nonunital complex
C*-algebras. -/
def middleFunctor : CStarExtensionCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj E := middle E
  map f := f.middleMap
  map_id _E := rfl
  map_comp _f _g := rfl

/-- **Quotient functor of C*-extensions.** A normalized extension of nonunital complex C*-algebras has
an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. Sending an extension to its quotient
endpoint and a compatible extension morphism to its quotient map defines a functor to nonunital
complex C*-algebras. -/
def quotientFunctor : CStarExtensionCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj E := E.quotient
  map f := f.quotientMap
  map_id _E := rfl
  map_comp _f _g := rfl

/-- **Natural ideal inclusion of C*-extensions.** A normalized extension of nonunital complex
C*-algebras has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective
inclusion and surjective quotient map forming a short exact sequence. The ideal inclusions form a
natural transformation from the ideal functor to the middle-algebra functor. -/
def inclusionNat : NatTrans idealFunctor.{u} middleFunctor.{u} where
  app E := E.extension.inclusion
  naturality {X Y} f :=
    (show CStarExtension.Hom X.extension Y.extension from f).inclusion_commutes.symm

/-- **Natural quotient projection of C*-extensions.** A normalized extension of nonunital complex
C*-algebras has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective
inclusion and surjective quotient map forming a short exact sequence. The quotient projections form
a natural transformation from the middle-algebra functor to the quotient functor. -/
def quotientNat : NatTrans middleFunctor.{u} quotientFunctor.{u} where
  app E := E.extension.quotient
  naturality {X Y} f :=
    (show CStarExtension.Hom X.extension Y.extension from f).quotient_commutes

@[simp]
theorem inclusionNat_apply (E : CStarExtensionCat.{u}) (b : E.ideal) :
    inclusionNat.app E b = E.extension.inclusion b := by
  rfl

@[simp]
theorem quotientNat_apply (E : CStarExtensionCat.{u}) (a : middle E) :
    quotientNat.app E a = E.extension.quotient a := by
  rfl

/-- **Injectivity of extension inclusion.** A normalized extension of nonunital complex C*-algebras has
an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. For every extension object, its inclusion
from the ideal endpoint into the middle algebra is injective. -/
theorem inclusion_injective (E : CStarExtensionCat.{u}) :
    Function.Injective (inclusionNat.app E) :=
  E.extension.inclusion_injective

/-- **Surjectivity of extension projection.** A normalized extension of nonunital complex C*-algebras
has an ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. For every extension object, its projection
from the middle algebra onto the quotient endpoint is surjective. -/
theorem quotient_surjective (E : CStarExtensionCat.{u}) :
    Function.Surjective (quotientNat.app E) :=
  E.extension.quotient_surjective

/-- **Exactness of a C*-extension.** A normalized extension of nonunital complex C*-algebras has an
ideal endpoint, a middle C*-algebra, and a quotient endpoint, with injective inclusion and
surjective quotient map forming a short exact sequence. For every extension object, the range of its
ideal inclusion equals the kernel of its quotient projection. -/
theorem exact (E : CStarExtensionCat.{u}) :
    Function.Exact (inclusionNat.app E) (quotientNat.app E) :=
  E.extension.exact

end CStarExtensionCat
