/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Enriched/TensorProduct.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Products and tensor products of enriched categories

If `C` is enriched in `V` and `D` is enriched in `W`, then `C × D` is enriched in the product
monoidal category `V × W`: Hom objects, identities and composition are taken componentwise.

When `C` and `D` are both enriched in a braided monoidal category `V`, the tensor product functor
`MonoidalCategory.tensor V : V × V ⥤ V` is monoidal, and transporting the `V × V`-enrichment of
`C × D` along it gives the tensor product of the two `V`-categories. Its Hom object from `(X, Y)`
to `(X', Y')` is `(X ⟶[V] X') ⊗ (Y ⟶[V] Y')`, its identities are tensor products of identities,
and its composition first applies the middle-four interchange `MonoidalCategory.tensorμ`, which
uses the braiding, and then composes in each factor. For categories enriched in cochain complexes
the braiding carries the Koszul sign, and this is the tensor product of differential graded
categories.

## Main definitions

* `MathlibExt.DGSource.prodEnrichedCategory`: the `V × W`-enrichment of `C × D`.
* `MathlibExt.DGSource.tensorEnrichedCategory`: the `V`-enrichment of `C × D` when `V` is braided.

## Main results

* `MathlibExt.DGSource.eHom_tensor_eq`, `MathlibExt.DGSource.eId_tensor_eq` and `MathlibExt.DGSource.eComp_tensor_eq`: Hom objects,
  identities and composition of the tensor product, in terms of those of the two factors.

## References

* G. M. Kelly, *Basic concepts of enriched category theory*, Section 1.4.
* `Mathlib.CategoryTheory.Enriched.Basic`, for `CategoryTheory.TransportEnrichment`, and
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic`, for the monoidal structure on the tensor
  product functor.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.DGSource

universe v₁ v₂ u₁ u₂ u₃ u₄

section Prod

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  (W : Type u₂) [Category.{v₂} W] [MonoidalCategory W]
  (C : Type u₃) [EnrichedCategory V C] (D : Type u₄) [EnrichedCategory W D]

/-- The product of a `V`-category and a `W`-category is a category enriched in the product
monoidal category `V × W`, with Hom objects, identities and composition taken componentwise. -/
instance prodEnrichedCategory : EnrichedCategory (V × W) (C × D) where
  Hom X Y := (X.1 ⟶[V] Y.1, X.2 ⟶[W] Y.2)
  id X := (eId V X.1, eId W X.2)
  comp X Y Z := (eComp V X.1 Y.1 Z.1, eComp W X.2 Y.2 Z.2)
  id_comp X Y := Prod.hom_ext (e_id_comp V X.1 Y.1) (e_id_comp W X.2 Y.2)
  comp_id X Y := Prod.hom_ext (e_comp_id V X.1 Y.1) (e_comp_id W X.2 Y.2)
  assoc X Y Z T := Prod.hom_ext (e_assoc V X.1 Y.1 Z.1 T.1) (e_assoc W X.2 Y.2 Z.2 T.2)

variable {V W C D}

/-- The Hom object of a product of enriched categories is the pair of Hom objects. -/
lemma eHom_prod_eq (X Y : C × D) :
    (X ⟶[V × W] Y) = (X.1 ⟶[V] Y.1, X.2 ⟶[W] Y.2) :=
  rfl

/-- The identity of an object of a product of enriched categories is the pair of identities. -/
lemma eId_prod_eq (X : C × D) :
    eId (V × W) X = (eId V X.1, eId W X.2) :=
  rfl

/-- Composition in a product of enriched categories is the pair of compositions. -/
lemma eComp_prod_eq (X Y Z : C × D) :
    eComp (V × W) X Y Z = (eComp V X.1 Y.1 Z.1, eComp W X.2 Y.2 Z.2) :=
  rfl

end Prod

section Tensor

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]
  (C : Type u₃) [EnrichedCategory V C] (D : Type u₄) [EnrichedCategory V D]

/-- The **tensor product** of two categories enriched in a braided monoidal category `V`. The Hom
object from `(X, Y)` to `(X', Y')` is `(X ⟶[V] X') ⊗ (Y ⟶[V] Y')`; identities and composition are
described by `MathlibExt.DGSource.eId_tensor_eq` and `MathlibExt.DGSource.eComp_tensor_eq`. It is the `V × V`-enrichment
`MathlibExt.DGSource.prodEnrichedCategory` transported along the monoidal functor
`MonoidalCategory.tensor V`. -/
instance tensorEnrichedCategory : EnrichedCategory V (C × D) :=
  inferInstanceAs (EnrichedCategory V (TransportEnrichment (tensor V) (C × D)))

variable {V C D}

/-- The Hom object of the tensor product of two enriched categories is the tensor product of the
Hom objects of the two factors. -/
lemma eHom_tensor_eq (X Y : C × D) :
    (X ⟶[V] Y) = (X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2) :=
  rfl

/-- The identity of an object of the tensor product of two enriched categories is the tensor
product of the identities of its two components. -/
@[reassoc]
lemma eId_tensor_eq (X : C × D) :
    eId V X = (λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2) :=
  rfl

/-- Composition in the tensor product of two enriched categories: interchange the two middle
factors with `MonoidalCategory.tensorμ`, then compose in each factor. -/
@[reassoc]
lemma eComp_tensor_eq (X Y Z : C × D) :
    eComp V X Y Z =
      tensorμ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2) (Y.1 ⟶[V] Z.1) (Y.2 ⟶[V] Z.2) ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2) :=
  rfl

end Tensor

end MathlibExt.DGSource
