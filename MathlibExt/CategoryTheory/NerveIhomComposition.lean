/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism

/-!
# The original two-simplex of a natural-transformation chain

The existing chain classifier gives an actual two-simplex in the simplicial
mapping space. Its three faces are the entire original homotopies of the
two transformations and their composite. No composition or homotopy
witness is supplied, and every simplex of the active nerve is retained.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

universe u v

namespace CategoryTheory.NatTrans

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G H : C ⥤ D}

/-- Proved equality transports of the two functor endpoints retain the
ENTIRE original classified nerve cylinder. -/
public theorem nerveHomotopyMap_eqToHomEndpoints
    {F' G' : C ⥤ D} (hf : F = F') (hg : G = G') (α : F ⟶ G) :
    nerveHomotopyMap (eqToHom hf.symm ≫ α ≫ eqToHom hg) = nerveHomotopyMap α := by
  cases hf
  cases hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The existing original chain prism supplies the actual composition
structure of the three edges in the simplicial mapping space. -/
public def nerveIhomCompStruct (α : F ⟶ G) (β : G ⟶ H) :
    SSet.Edge.CompStruct (nerveHomotopy α).edgeIhom
      (nerveHomotopy β).edgeIhom (nerveHomotopy (α ≫ β)).edgeIhom where
  simplex := SSet.ihomSimplexOfPrism (nerveChainFunctor α β).nervePrismMap
  d₂ := by
    change ((ihom (nerve C)).obj (nerve D)).δ (2 : Fin 3)
      (SSet.ihomSimplexOfPrism (nerveChainFunctor α β).nervePrismMap) =
        (nerveHomotopy α).edgeIhom.edge
    rw [SSet.δ_ihomSimplexOfPrism, Functor.whiskerLeft_δ_nervePrismMap,
      prod_δ_two_comp_nerveChainFunctor, nervePrismMap_nerveCylinderFunctor]
    exact (SSet.Homotopy.edgeIhom_edge (nerveHomotopy α)).symm
  d₀ := by
    change ((ihom (nerve C)).obj (nerve D)).δ (0 : Fin 3)
      (SSet.ihomSimplexOfPrism (nerveChainFunctor α β).nervePrismMap) =
        (nerveHomotopy β).edgeIhom.edge
    rw [SSet.δ_ihomSimplexOfPrism, Functor.whiskerLeft_δ_nervePrismMap,
      prod_δ_zero_comp_nerveChainFunctor, nervePrismMap_nerveCylinderFunctor]
    exact (SSet.Homotopy.edgeIhom_edge (nerveHomotopy β)).symm
  d₁ := by
    change ((ihom (nerve C)).obj (nerve D)).δ (1 : Fin 3)
      (SSet.ihomSimplexOfPrism (nerveChainFunctor α β).nervePrismMap) =
        (nerveHomotopy (α ≫ β)).edgeIhom.edge
    rw [SSet.δ_ihomSimplexOfPrism, Functor.whiskerLeft_δ_nervePrismMap,
      prod_δ_one_comp_nerveChainFunctor, nervePrismMap_nerveCylinderFunctor]
    exact (SSet.Homotopy.edgeIhom_edge (nerveHomotopy (α ≫ β))).symm

/-- The nerve cylinder of an identity transformation is the original
constant simplicial homotopy on the original functor map. -/
public theorem nerveHomotopy_id_reflH (F : C ⥤ D) :
    nerveHomotopy (𝟙 F) = SSet.Homotopy.reflH (nerveMap F) := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change nerveHomotopyMap (𝟙 F) =
    CartesianMonoidalCategory.fst (nerve C) (Δ[1] : SSet.{max u v}) ≫ nerveMap F
  rw [← nervePrismMap_nerveCylinderFunctor, nerveCylinderFunctor_id,
    Functor.nervePrismMap_fst_comp]

/-- The identity transformation gives the literal identity edge of the
mapping-space vertex of its original nerve map. -/
public theorem nerveIhomEdge_id (F : C ⥤ D) :
    (nerveHomotopy (𝟙 F)).edgeIhom =
      SSet.Edge.id (SSet.ihomVertexEquiv (nerve C) (nerve D) (nerveMap F)) := by
  rw [nerveHomotopy_id_reflH, SSet.Homotopy.edgeIhom_reflH]

end CategoryTheory.NatTrans

end
