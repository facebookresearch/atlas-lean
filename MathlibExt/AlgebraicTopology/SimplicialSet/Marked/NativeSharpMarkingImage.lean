/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingUnit

/-!
# The same original native straightened marking cell is cofibrant

The actual sharp marking-chart unit equation identifies straightening
of the physical original interval marking cell through its unchanged
simplex and sharp image isomorphisms. The genuine original sharp-root
free-cell pushout therefore gives that same original straightened map
the projective left class and actual coherent-model cofibration.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Straightening of the same physical original interval marking cell has precisely its original sharp chart map
under the actual unchanged native image comparisons. -/
theorem nativeMarkingCell_straightening_image (B : SSet.{u}) (σ : B _⦋1⦌) :
    (nativeStraightening B).map (nativeMarkingCell B σ) ≫ (nativeSharpImageIso B σ).hom =
      (nativeSimplexImageIso B 1 σ).hom ≫ nativeSharpMarkingChartMap B σ := by
  let a := nativeStraighteningAdjunction B
  let m := nativeMarkingCell B σ
  let e := nativeSimplexImageIso B 1 σ
  let d := nativeSharpImageIso B σ
  let α := nativeSharpMarkingChartMap B σ
  let H := nativeSimplexChartHomEquiv B 1 σ (nativeSharpChart B σ)
  have hl := (a.homEquiv_naturality_left m d.hom).trans
    (congrArg (fun f => m ≫ f) (nativeSharpImageIso_homEquiv B σ))
  have hn := nativeSimplexChartHomEquiv_natural_right B 1 σ (𝟙 (nativeSimplexChart B 1 σ)) α
  have hr := (a.homEquiv_naturality_right e.hom α).trans
    ((congrArg (fun f => f ≫ (nativeUnstraightening B).map α) (nativeSimplexImageIso_homEquiv B 1 σ)).trans
      (hn.symm.trans (congrArg H (Category.id_comp α))))
  have hα := (congrArg H (Category.comp_id α)).symm.trans
    (nativeSharpMarkingChartMap_homEquiv B σ (nativeSharpChart B σ) (𝟙 _))
  apply (a.homEquiv (nativeSimplexBasis B 1 σ) (nativeSharpChart B σ)).injective
  exact hl.trans (hα.symm.trans hr.symm)

/-- Actual native straightening of the same original physical sharp interval marking cell has the genuine projective
left class. -/
theorem nativeMarkingCell_straightening_projectiveLeft (B : SSet.{u}) (σ : B _⦋1⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      ((nativeStraightening B).map (nativeMarkingCell B σ)) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  let e := nativeSimplexImageIso B 1 σ
  let d := nativeSharpImageIso B σ
  let α := nativeSharpMarkingChartMap B σ
  let f := (nativeStraightening B).map (nativeMarkingCell B σ)
  have h := G.rlp.llp.comp_mem (e.hom ≫ α) d.inv
    (G.rlp.llp.comp_mem e.hom α (G.rlp.llp_of_isIso e.hom) (nativeSharpMarkingChartMap_projectiveLeft B σ))
    (G.rlp.llp_of_isIso d.inv)
  have hm := congrArg (fun q => q ≫ d.inv) (nativeMarkingCell_straightening_image B σ)
  have he : (f ≫ d.hom) ≫ d.inv = f :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => f ≫ q) d.hom_inv_id).trans (Category.comp_id f))
  have hf : (e.hom ≫ α) ≫ d.inv = f := hm.symm.trans he
  change G.rlp.llp f
  exact hf ▸ h

/-- The same original physical native marking cell is sent to a cofibration in the genuinely constructed original
coherent marked model. -/
theorem nativeMarkingCell_straightening_cofibration (B : SSet.{u}) (σ : B _⦋1⦌) :
    let _ := coherentDiagramModelCategory B
    Cofibration ((nativeStraightening B).map (nativeMarkingCell B σ)) := by
  let _ := coherentDiagramModelCategory B
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeMarkingCell_straightening_projectiveLeft B σ

end SSet.Marked
