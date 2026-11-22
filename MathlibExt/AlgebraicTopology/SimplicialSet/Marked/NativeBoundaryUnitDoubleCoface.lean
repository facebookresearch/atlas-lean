/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCofaceBoundaryUnit

/-!
# Genuine original double-coface unit compatibility in the native source

The original double-coface identity makes both full simplex maps into
the same original boundary equal before applying straightening. The
same actual boundary unit therefore has equal original restrictions.
Reading its full coherent sections retains every marked coefficient
and the original dependent base objects, without cancelling a native
boundary comparison or supplying a gluing outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire actual original boundary coface basis has exactly the unchanged underlying original coface after its
original subcomplex inclusion. -/
theorem nativeCofaceBoundaryBasisMap_underlying (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    (nativeCofaceBoundaryBasisMap B n σ j).left.hom ≫ (boundary (n + 1)).ι =
      SSet.stdSimplex.map (SimplexCategory.δ j) :=
  congrArg (fun a => a.left.hom) (nativeCofaceBoundaryBasisMap_attachment B n σ j)

/-- Both unchanged original whole double-coface maps into the original full boundary are equal by the original
simplicial identity. -/
theorem nativeBoundaryCofacePair_underlying (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) :
    SSet.stdSimplex.map (SimplexCategory.δ (k.pred h.ne_zero)) ≫
        (nativeCofaceBoundaryBasisMap B (n + 1) σ j.castSucc).left.hom =
      SSet.stdSimplex.map (SimplexCategory.δ j) ≫
        (nativeCofaceBoundaryBasisMap B (n + 1) σ k).left.hom := by
  let f := SimplexCategory.δ (k.pred h.ne_zero)
  let g := SimplexCategory.δ j
  let a := (nativeCofaceBoundaryBasisMap B (n + 1) σ j.castSucc).left.hom
  let b := (nativeCofaceBoundaryBasisMap B (n + 1) σ k).left.hom
  let ι := (boundary.{u} (n + 2)).ι
  apply (cancel_mono ι).mp
  have ha : (SSet.stdSimplex.map f ≫ a) ≫ ι =
      SSet.stdSimplex.map f ≫ SSet.stdSimplex.map (SimplexCategory.δ j.castSucc) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => SSet.stdSimplex.map f ≫ z) (nativeCofaceBoundaryBasisMap_underlying B (n + 1) σ j.castSucc))
  have hb : (SSet.stdSimplex.map g ≫ b) ≫ ι =
      SSet.stdSimplex.map g ≫ SSet.stdSimplex.map (SimplexCategory.δ k) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => SSet.stdSimplex.map g ≫ z) (nativeCofaceBoundaryBasisMap_underlying B (n + 1) σ k))
  have hd : SSet.stdSimplex.map f ≫ SSet.stdSimplex.map (SimplexCategory.δ j.castSucc) =
      SSet.stdSimplex.map g ≫ SSet.stdSimplex.map (SimplexCategory.δ k) :=
    (SSet.stdSimplex.map_comp f (SimplexCategory.δ j.castSucc)).symm.trans
      ((congrArg SSet.stdSimplex.map (SimplexCategory.δ_comp_δ' h).symm).trans
        (SSet.stdSimplex.map_comp g (SimplexCategory.δ k)))
  exact ha.trans (hd.trans hb.symm)

/-- The original full boundary's actual native unit has the same whole coherent simplex restriction along both
original double cofaces. -/
theorem nativeBoundaryCofaceUnit_double_raw (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) :
    ((nativeSimplexUnHomEquiv B (n + 1) (B.map (SimplexCategory.δ j.castSucc).op σ)
      (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
      (nativeSimplexChartHomEquiv B (n + 1) (B.map (SimplexCategory.δ j.castSucc).op σ)
        (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
        (nativeBoundaryCofaceChartMap B (n + 1) σ j.castSucc))).val).pull
          (SimplexCategory.δ (k.pred h.ne_zero)).toOrderHom.uliftMap =
      ((nativeSimplexUnHomEquiv B (n + 1) (B.map (SimplexCategory.δ k).op σ)
        (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
        (nativeSimplexChartHomEquiv B (n + 1) (B.map (SimplexCategory.δ k).op σ)
          (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
          (nativeBoundaryCofaceChartMap B (n + 1) σ k))).val).pull
            (SimplexCategory.δ j).toOrderHom.uliftMap := by
  let f := SimplexCategory.δ (k.pred h.ne_zero)
  let g := SimplexCategory.δ j
  let a := (nativeCofaceBoundaryBasisMap B (n + 1) σ j.castSucc).left.hom
  let b := (nativeCofaceBoundaryBasisMap B (n + 1) σ k).left.hom
  let β := (nativeBoundaryUnitCoherentMap B (n + 2) σ).left.hom
  have hu : SSet.stdSimplex.map f ≫ (a ≫ β) = SSet.stdSimplex.map g ≫ (b ≫ β) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ β) (nativeBoundaryCofacePair_underlying B n σ j k h)).trans (Category.assoc _ _ _))
  exact (nativeBoundaryCofaceUnit_pull_raw B (n + 1) σ j.castSucc f).trans
    ((congrArg SSet.yonedaEquiv hu).trans (nativeBoundaryCofaceUnit_pull_raw B (n + 1) σ k g).symm)

/-- Both original double cofaces have the same actual whole marked coefficient section in the genuine native
boundary source, retaining the dependent original coherent base-object presentations. -/
theorem nativeBoundaryCofaceSections_double_heq (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : Fin (n + 2)) (k : Fin (n + 3)) (h : j.castSucc < k) (i : (Index.{u} n)ᵒᵖ) :
    HEq (coneImage (SimplexCategory.δ (k.pred h.ne_zero)).toOrderHom.uliftMap i.unop.as ≫
        (EnrichedLeftKan.universalHomEquiv
          (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ j.castSucc).op σ)))
          (coneDiagram (n + 1)) (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
          (nativeBoundaryCofaceChartMap B (n + 1) σ j.castSucc)).app
            (op ((indexMap (SimplexCategory.δ (k.pred h.ne_zero)).toOrderHom.uliftMap).obj i.unop)))
      (coneImage (SimplexCategory.δ j).toOrderHom.uliftMap i.unop.as ≫
        (EnrichedLeftKan.universalHomEquiv
          (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))
          (coneDiagram (n + 1)) (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
          (nativeBoundaryCofaceChartMap B (n + 1) σ k)).app
            (op ((indexMap (SimplexCategory.δ j).toOrderHom.uliftMap).obj i.unop))) := by
  let F := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let f := (SimplexCategory.δ (k.pred h.ne_zero)).toOrderHom.uliftMap
  let g := (SimplexCategory.δ j).toOrderHom.uliftMap
  have hl := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B (n + 1)
    (B.map (SimplexCategory.δ j.castSucc).op σ) F (nativeBoundaryCofaceChartMap B (n + 1) σ j.castSucc))
  have hr := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B (n + 1)
    (B.map (SimplexCategory.δ k).op σ) F (nativeBoundaryCofaceChartMap B (n + 1) σ k))
  have hraw := (congrArg (fun a : UnstraighteningSimplex F (n + 1) => a.pull f) hl).symm.trans
    ((nativeBoundaryCofaceUnit_double_raw B n σ j k h).trans
      (congrArg (fun a : UnstraighteningSimplex F (n + 1) => a.pull g) hr))
  let read := fun a : UnstraighteningSimplex F n =>
    (⟨a.base.obj i.unop, a.sectionMap.app i⟩ : Σ c : (realization B), coneWeight i.unop.as ⟶ F.obj (op c))
  exact (Sigma.mk.inj (congrArg read hraw)).2

end SSet.Marked
