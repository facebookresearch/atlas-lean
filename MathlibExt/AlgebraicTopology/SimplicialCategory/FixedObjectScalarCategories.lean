/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategory

/-!
# Actual scalar categories on the original fixed object labels

The canonical `SSet.ScalarObject` category is transported to the
individual labels by the actual vertex equivalence. Its Hom sets are the same original evaluated
Hom objects. Every scalar operator and every actual fixed-object map
preserves these literal labels and the original identity/composition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- The original scalar category at the same individually supplied fixed object labels. -/
@[instance_reducible]
def scalarCategory (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) : Category.{u} O where
  Hom x y := (hom C x y).obj q
  id x := (identityMap C x).app q PUnit.unit
  comp {x y z} a b := (compositionMap C x y z).app q (a, b)
  id_comp {x y} a :=
    @Category.id_comp (SSet.ScalarObject C.val q) inferInstance ⟨vertex C x⟩ ⟨vertex C y⟩ a
  comp_id {x y} a :=
    @Category.comp_id (SSet.ScalarObject C.val q) inferInstance ⟨vertex C x⟩ ⟨vertex C y⟩ a
  assoc {w x y z} a b c :=
    @Category.assoc (SSet.ScalarObject C.val q) inferInstance
      ⟨vertex C w⟩ ⟨vertex C x⟩ ⟨vertex C y⟩ ⟨vertex C z⟩ a b c

/-- The actual scalar operator keeps the same labels and acts on their entire original Hom
simplices. -/
def scalarOperator (C : FixedObjects O) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    @Functor O (scalarCategory C q) O (scalarCategory C r) :=
  @Functor.mk O (scalarCategory C q) O (scalarCategory C r) (fun x => x)
    (fun {x y} a => (hom C x y).map f a)
    (fun x => (SSet.scalarOperator (C := C.val) f).map_id ⟨vertex C x⟩)
    (fun {x y z} a b => (SSet.scalarOperator (C := C.val) f).map_comp
      (X := ⟨vertex C x⟩) (Y := ⟨vertex C y⟩) (Z := ⟨vertex C z⟩) a b)

/-- Every original fixed-object map gives its actual same-label scalar functor. -/
def scalarFunctor {C D : FixedObjects O} (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) :
    @Functor O (scalarCategory C q) O (scalarCategory D q) :=
  @Functor.mk O (scalarCategory C q) O (scalarCategory D q) (fun x => x)
    (fun {x y} a => (homMap F x y).app q a)
    (fun x => congr($(identityMap_homMap F x).app q PUnit.unit))
    (fun {x y z} a b => congr($(compositionMap_homMap F x y z).app q (a, b)))

/-- The same original scalar functor commutes with every actual simplex operator. -/
theorem scalarFunctor_operator {C D : FixedObjects O} (F : C ⟶ D)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (x y : O) (a : (hom C x y).obj q) :
    (homMap F x y).app r ((hom C x y).map f a) =
      (hom D x y).map f ((homMap F x y).app q a) :=
  congr($((homMap F x y).naturality f) a)

end CategoryTheory.SimplicialEnrichment.FixedObjects
