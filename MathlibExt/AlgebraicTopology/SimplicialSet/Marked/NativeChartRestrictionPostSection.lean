/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartWholeOperator

/-!
# Exact original native chart operators into any actual target

The original simplex restriction and native chart unit read the whole
unchanged cone section after any actual enriched target map. Reading
the original fixed-base simplex gives every full marked coefficient
with the genuine original coherent base-object transport retained.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original native chart restriction reads the complete original cone pull of its actual target section. -/
theorem nativeChartRestriction_post_raw (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : B _⦋m⦌) (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativeSimplexChart B m σ ⟶ F) :
    (nativeSimplexUnHomEquiv B n (B.map f.op σ) F
      (nativeSimplexChartHomEquiv B n (B.map f.op σ) F (nativeSimplexChartRestriction B f σ ≫ g))).val =
      ((nativeSimplexUnHomEquiv B m σ F (nativeSimplexChartHomEquiv B m σ F g)).val).pull
        f.toOrderHom.uliftMap := by
  have h := nativeChartRestriction_homEquiv B f σ F g
  exact (congrArg (fun a => (nativeSimplexUnHomEquiv B n (B.map f.op σ) F a).val) h).trans
    (nativeSimplexUn_pre_val B f σ F _)

/-- The complete original marked coefficient section after native restriction is the same whole cone image followed
by the actual original target section. -/
theorem nativeChartRestriction_post_component_heq (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : nativeSimplexChart B m σ ⟶ F) (i : (Index.{u} n)ᵒᵖ) :
    HEq ((EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
      (coneDiagram n) F (nativeSimplexChartRestriction B f σ ≫ g)).app i)
      (coneImage f.toOrderHom.uliftMap i.unop.as ≫
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m) F g).app
          (op ((indexMap f.toOrderHom.uliftMap).obj i.unop))) := by
  have hl := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B n (B.map f.op σ) F
    (nativeSimplexChartRestriction B f σ ≫ g))
  have hr := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B m σ F g)
  have hraw := hl.symm.trans ((nativeChartRestriction_post_raw B f σ F g).trans
    (congrArg (fun a => a.pull f.toOrderHom.uliftMap) hr))
  let read := fun a : UnstraighteningSimplex F n =>
    (⟨a.base.obj i.unop, a.sectionMap.app i⟩ :
      Σ c : (realization B), coneWeight i.unop.as ⟶ F.obj (op c))
  exact (Sigma.mk.inj (congrArg read hraw)).2

/-- The original full native index/base composition gives the actual equality of coefficient base objects for every
original simplex operator. -/
theorem nativeChartOperatorBaseObject (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : B _⦋m⦌) (i : (Index.{u} n)ᵒᵖ) :
    (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))).obj i =
      (EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op ((indexMap f.toOrderHom.uliftMap).obj i.unop)) :=
  (congrArg (fun a : EnrichedFunctor SSet.{u} (Index.{u} n)ᵒᵖ (realization B)ᵒᵖ => a.obj i)
    (nativeChartIndex_comp_simplex B f σ)).symm

private theorem coefficient_heq_transport {A X Y : Marked.{u}} (h : X = Y)
    (a : A ⟶ X) (b : A ⟶ Y) (hab : HEq a b) : a ≫ eqToHom h = b := by
  cases h
  exact (Category.comp_id a).trans (eq_of_heq hab)

/-- The original native operator into the actual enriched target retains the exact original marked coefficient image
after its genuine coherent base-object transport. -/
theorem nativeChartRestriction_post_component (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : nativeSimplexChart B m σ ⟶ F) (i : (Index.{u} n)ᵒᵖ) :
    (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
      (coneDiagram n) F (nativeSimplexChartRestriction B f σ ≫ g)).app i ≫
        eqToHom (congrArg F.obj (nativeChartOperatorBaseObject B f σ i)) =
      coneImage f.toOrderHom.uliftMap i.unop.as ≫
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m) F g).app
          (op ((indexMap f.toOrderHom.uliftMap).obj i.unop)) :=
  coefficient_heq_transport (congrArg F.obj (nativeChartOperatorBaseObject B f σ i)) _ _
    (nativeChartRestriction_post_component_heq B f σ F g i)

end SSet.Marked
