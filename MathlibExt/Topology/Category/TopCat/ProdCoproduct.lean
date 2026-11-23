/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Products distribute over topological coproducts

For any topological space `K` and indexed family `F`,
`prodCoproductComparisonIso` identifies the coproduct of `K ⨯ F j` with
`K ⨯ ∐ F`.
Its restriction to each coproduct summand is the product of the identity
of `K` with the corresponding coproduct inclusion.
Thus product with a fixed left factor preserves coproducts in `TopCat`,
for arbitrary spaces without a local-compactness assumption.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

variable {J : Type u} (K : TopCat.{u}) (F : J → TopCat.{u})

/-- Swap each right factor to the left inside the indexed sum. -/
noncomputable def prodCoproductSwapSigmaIso :
    TopCat.of (Σ j, ↑(F j) × ↑K) ≅ TopCat.of (Σ j, ↑K × ↑(F j)) :=
  (TopCat.sigmaIsoSigma (fun j => TopCat.of (↑(F j) × ↑K))).symm.trans
    ((Limits.Sigma.mapIso (fun j =>
      (TopCat.isoOfHomeo (Homeomorph.prodComm (↑(F j)) (↑K)) :
        TopCat.of (↑(F j) × ↑K) ≅ TopCat.of (↑K × ↑(F j))))).trans
      (TopCat.sigmaIsoSigma (fun j => TopCat.of (↑K × ↑(F j)))))

/-- Left-fixed type product against the indexed sum, via comm and distrib. -/
noncomputable def prodCoproductMidIso :
    TopCat.of (↑K × Σ j, ↑(F j)) ≅ TopCat.of (Σ j, ↑K × ↑(F j)) :=
  ((TopCat.isoOfHomeo (Homeomorph.prodComm (↑K) (Σ j, ↑(F j))) :
    TopCat.of (↑K × Σ j, ↑(F j)) ≅
      TopCat.of ((Σ j, ↑(F j)) × ↑K))).trans
    (((TopCat.isoOfHomeo (Homeomorph.sigmaProdDistrib :
      ((Σ j, ↑(F j)) × ↑K ≃ₜ Σ j, ↑(F j) × ↑K)) :
    TopCat.of ((Σ j, ↑(F j)) × ↑K) ≅
      TopCat.of (Σ j, ↑(F j) × ↑K))).trans
      (prodCoproductSwapSigmaIso K F))

/-- Canonical comparison iso for fixed-left product against a coproduct. -/
noncomputable def prodCoproductComparisonIso :
    (∐ (fun j => K ⨯ F j)) ≅ K ⨯ (∐ F) :=
  (Limits.Sigma.mapIso (fun j => TopCat.prodIsoProd K (F j))).trans
    ((TopCat.sigmaIsoSigma (fun j => TopCat.of (↑K × ↑(F j)))).trans
      ((prodCoproductMidIso K F).symm.trans
        ((TopCat.prodIsoProd K (TopCat.of (Σ j, ↑(F j)))).symm.trans
          (Limits.prod.mapIso (Iso.refl K)
            (TopCat.sigmaIsoSigma F).symm))))

/-- The comparison iso lies over each coproduct inclusion. -/
theorem prodCoproductComparison_ι (j : J) :
    Limits.Sigma.ι (fun j => K ⨯ F j) j ≫
      (prodCoproductComparisonIso K F).hom =
      Limits.prod.map (𝟙 K) (Limits.Sigma.ι F j) := by
  unfold prodCoproductComparisonIso prodCoproductMidIso prodCoproductSwapSigmaIso
  apply Limits.prod.hom_ext
  · apply TopCat.ext
    intro x
    simp
    rfl
  · apply TopCat.ext
    intro x
    simp
    rfl

instance preservesColimit_prodFunctorObj_coproduct
    [HasCoproduct F] [HasCoproduct fun j => (Limits.prod.functor.obj K).obj (F j)] :
    PreservesColimit (Discrete.functor F) (Limits.prod.functor.obj K) := by
  have hEq : (prodCoproductComparisonIso K F).hom =
      Limits.sigmaComparison (Limits.prod.functor.obj K) F := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [prodCoproductComparison_ι]
    simp [Limits.sigmaComparison, Limits.prod.functor]
  have : IsIso (Limits.sigmaComparison (Limits.prod.functor.obj K) F) :=
    hEq ▸ (prodCoproductComparisonIso K F).isIso_hom
  exact Limits.PreservesCoproduct.of_iso_comparison _ _

instance preservesColimitsOfShape_prodFunctorObj :
    PreservesColimitsOfShape (Discrete J) (Limits.prod.functor.obj K) :=
  Limits.preservesColimitsOfShape_of_discrete _

end TopCat
