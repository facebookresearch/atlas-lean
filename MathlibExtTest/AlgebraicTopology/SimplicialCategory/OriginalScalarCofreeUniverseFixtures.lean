/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryAdjunction
import Mathlib.CategoryTheory.SingleObj

/-!
# Original scalar cofree clients at independent universes and nonconstant coefficients

The arbitrary enriched source, ordinary target and coefficient universes
remain separate. A concrete one-object ordinary monoid category has a
higher coefficient whose two original vertex operators are different.
-/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.OriginalScalarCofreeUniverseFixtures

/-- Every full operator of the original extension is the SAME original ordinary functor map. -/
theorem fullCoefficient {C : Type v} [EnrichedCategory SSet.{u} C]
    (E : Type w) [Category.{u} E] (q n : SimplexCategoryᵒᵖ)
    (F : SSet.ScalarObject C q ⥤ E) (x y : C) (h : (x ⟶[SSet.{u}] y).obj n) (θ : n ⟶ q) :
    let _ : EnrichedCategory SSet.{u} E := SSet.ScalarCofree.enrichment q E
    ((SSet.ScalarCofree.ofFunctor q E F).map x y).app n h θ =
      F.map ((x ⟶[SSet.{u}] y).map θ h) := by
  let _ : EnrichedCategory SSet.{u} E := SSet.ScalarCofree.enrichment q E
  rfl

/-- Reading the complete arbitrary-universe extension recovers the SAME entire original functor. -/
theorem fullFunctorReadback {C : Type v} [EnrichedCategory SSet.{u} C]
    (E : Type w) [Category.{u} E] (q : SimplexCategoryᵒᵖ)
    (F : SSet.ScalarObject C q ⥤ E) :
    SSet.ScalarCofree.toFunctor q E (SSet.ScalarCofree.ofFunctor q E F) = F :=
  SSet.ScalarCofree.toFunctor_ofFunctor q E F

/-- Original ordinary target change retains the complete enriched extension at three independent object universes. -/
theorem fullTargetNaturality {C : Type v} [EnrichedCategory SSet.{u} C]
    {E : Type w} [Category.{u} E] {D : Type z} [Category.{u} D]
    (q : SimplexCategoryᵒᵖ) (F : SSet.ScalarObject C q ⥤ E) (G : E ⥤ D) :
    let _ : EnrichedCategory SSet.{u} E := SSet.ScalarCofree.enrichment q E
    let _ : EnrichedCategory SSet.{u} D := SSet.ScalarCofree.enrichment q D
    (SSet.ScalarCofree.ofFunctor q E F).comp SSet.{u} (SSet.ScalarCofree.map q G) =
      SSet.ScalarCofree.ofFunctor q D (F ⋙ G) :=
  SSet.ScalarCofree.ofFunctor_target q F G

/-- A genuine original carrier colimit is preserved at every ordinal and independent existing diagram universes. -/
def scalarOriginalColimit {J : Type v} [Category.{w} J]
    (q : SimplexCategoryᵒᵖ) {F : J ⥤ CategoryTheory.SimplicialEnrichment.Carrier.{u}}
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((CategoryTheory.SimplicialEnrichment.ScalarCategoryAdjunction.scalar q).mapCocone c) := by
  let _ : PreservesColimitsOfSize.{w, v}
      (CategoryTheory.SimplicialEnrichment.ScalarCategoryAdjunction.scalar.{u} q) :=
    (CategoryTheory.SimplicialEnrichment.ScalarCategoryAdjunction.adjunction q).leftAdjoint_preservesColimits
  exact isColimitOfPreserves _ hc

/-- A genuine full higher coefficient remembers two different original ordinary endomorphisms. -/
def higherCoefficient :
    (SSet.ScalarCofree.homObject (op ⦋0⦌) (SingleObj ℕ) (SingleObj.star ℕ) (SingleObj.star ℕ)).obj
      (op ⦋1⦌) :=
  fun θ => if θ.unop.toOrderHom 0 = 0 then (1 : ℕ) else (2 : ℕ)

/-- The SAME first original vertex operator reads the first endomorphism. -/
theorem higherCoefficient_first :
    (SSet.ScalarCofree.homObject (op ⦋0⦌) (SingleObj ℕ) (SingleObj.star ℕ) (SingleObj.star ℕ)).map
      (SimplexCategory.δ (1 : Fin 2)).op higherCoefficient (𝟙 (op ⦋0⦌)) = (1 : ℕ) := rfl

/-- The SAME second original vertex operator reads a different endomorphism. -/
theorem higherCoefficient_second :
    (SSet.ScalarCofree.homObject (op ⦋0⦌) (SingleObj ℕ) (SingleObj.star ℕ) (SingleObj.star ℕ)).map
      (SimplexCategory.δ (0 : Fin 2)).op higherCoefficient (𝟙 (op ⦋0⦌)) = (2 : ℕ) := rfl

end MathlibExtTest.OriginalScalarCofreeUniverseFixtures
