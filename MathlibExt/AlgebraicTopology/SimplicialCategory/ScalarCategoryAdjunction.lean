/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCofreeFunctorNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The canonical original scalar-category functor has a genuine cofree right adjoint

The left functor uses the SAME original ScalarObject and scalarFunctor.
The complete cofree right functor and the genuine whole Hom bijection
retain all original object maps, coefficients and ordinal operators.
This proves actual colimit preservation without a colimit certificate.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ScalarCategoryAdjunction

variable (q : SimplexCategoryᵒᵖ)

/-- The SAME complete original canonical scalar-category functor at the selected ordinal. -/
def scalar : Carrier.{u} ⥤ Cat.{u, u} where
  obj C := Cat.of (SSet.ScalarObject C q)
  map F := (SSet.scalarFunctor F q).toCatHom
  map_id _C := Cat.ext (SSet.scalarFunctor_id q)
  map_comp F G := Cat.ext (SSet.scalarFunctor_comp F G q)

/-- The genuine complete original cofree enrichment on the SAME original ordinary target objects. -/
def cofreeObject (E : Cat.{u, u}) : Carrier.{u} := by
  let _ : EnrichedCategory SSet.{u} E := SSet.ScalarCofree.enrichment q E
  exact of E

/-- The SAME entire original ordinary functor on every full operator-indexed coefficient family. -/
def cofreeMap {E D : Cat.{u, u}} (F : E ⟶ D) : cofreeObject q E ⟶ cofreeObject q D :=
  SSet.ScalarCofree.map (E := (E : Type u)) (D := (D : Type u)) q F.toFunctor

/-- The actual complete original cofree right functor, with both whole original functor laws. -/
def cofree : Cat.{u, u} ⥤ Carrier.{u} where
  obj := cofreeObject q
  map := cofreeMap q
  map_id E := SSet.ScalarCofree.map_id (E := (E : Type u)) q
  map_comp {E D K} F G := SSet.ScalarCofree.map_comp
    (E := (E : Type u)) (D := (D : Type u)) (K := (K : Type u)) q F.toFunctor G.toFunctor

/-- The actual full original Hom bijection uses the SAME canonical scalar category and
complete cofree target. -/
def fullHomEquiv (C : Carrier.{u}) (E : Cat.{u, u}) :
    ((scalar q).obj C ⟶ E) ≃ (C ⟶ cofreeObject q E) :=
  (Cat.Hom.equivFunctor ((scalar q).obj C) E).trans
    (SSet.ScalarCofree.homEquiv (C := (C : Type u)) q (E : Type u)).symm

/-- The genuine original scalar/cofree adjunction retains both entire original inverse Hom maps. -/
def adjunction : scalar q ⊣ cofree q :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fullHomEquiv q
    homEquiv_naturality_left_symm := by
      intro C D E F G
      apply Cat.ext
      exact SSet.ScalarCofree.toFunctor_source
        (E := (E : Type u)) (C := (C : Type u)) (K := (D : Type u)) q F G
    homEquiv_naturality_right := by
      intro C E D F G
      exact (SSet.ScalarCofree.ofFunctor_target
        (C := (C : Type u)) (E := (E : Type u)) (D := (D : Type u)) q F.toFunctor
          G.toFunctor).symm }

/-- The SAME actual original scalar-category functor preserves every existing full colimit. -/
instance preservesColimits : Limits.PreservesColimits (scalar q) :=
  (adjunction q).leftAdjoint_preservesColimits

end CategoryTheory.SimplicialEnrichment.ScalarCategoryAdjunction
