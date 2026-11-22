/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalEdgeChartMates
import Mathlib.CategoryTheory.Whiskering

/-!
# Whole original critical marking-span isomorphisms

The complete original source and target marking spans first retain
their actual native interval and horn or simplex basis records. Their
native straightening spans are then identified through the original
simplex, sharp-edge and positive-horn unit mates and exact critical
composition isomorphisms. BOTH actual arrows of each full span are
preserved, including the original physical interval marking cell.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME complete original SOURCE marking span has its whole native basis isomorphism. -/
def nativeCriticalSourceBasisSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ) ≅
      span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ)) (nativeCriticalMinimalHornEdgeOverMap B n σ) :=
  spanIsoMk (nativeCriticalSourceIntervalBasisIso B n σ) (nativeCriticalSourceSharpBasisIso B n σ)
    (nativeCriticalSourceHornBasisIso B n σ) (nativeCriticalSourceBasisIso_marking B n σ)
      (nativeCriticalSourceBasisIso_edge B n σ)

/-- The complete original TARGET marking span retains BOTH actual original arrows through its native basis
isomorphism. -/
def nativeCriticalTargetBasisSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ) ≅
      span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ))
        (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) :=
  spanIsoMk (nativeCriticalTargetIntervalBasisIso B n σ) (nativeCriticalTargetSharpBasisIso B n σ)
    (nativeCriticalTargetSimplexBasisIso B n σ) (nativeCriticalTargetBasisIso_marking B n σ)
      (nativeCriticalTargetBasisIso_edge B n σ)

/-- The SAME actual original interval marking image retains its entire critical composition square. -/
theorem nativeCriticalMarkingCell_image (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).map (nativeMarkingCell B (nativeCriticalBaseEdge B n σ)) ≫
      ((nativeSharpImageIso B (nativeCriticalBaseEdge B n σ)).hom ≫
        (nativeCriticalSharpEdgeCompositionIso B n σ).inv) =
    ((nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
      (nativeCriticalMinimalEdgeCompositionIso B n σ).inv) ≫ nativeCriticalEdgeMarkingChartMap B n σ := by
  let e := nativeCriticalMinimalEdgeCompositionIso B n σ
  let d := nativeCriticalSharpEdgeCompositionIso B n σ
  let a := (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom
  let m := nativeSharpMarkingChartMap B (nativeCriticalBaseEdge B n σ)
  let f := nativeCriticalEdgeMarkingChartMap B n σ
  have h : (e.inv ≫ f) ≫ d.hom = m :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => e.inv ≫ q) (nativeCriticalEdgeComposition_marking B n σ)).trans
        (e.inv_hom_id_assoc m))
  have hi : m ≫ d.inv = e.inv ≫ f := d.comp_inv_eq.mpr h.symm
  have h₀ := (Category.assoc
    ((nativeStraightening B).map (nativeMarkingCell B (nativeCriticalBaseEdge B n σ)))
      (nativeSharpImageIso B (nativeCriticalBaseEdge B n σ)).hom d.inv).symm
  have h₁ := congrArg (fun q => q ≫ d.inv) (nativeMarkingCell_straightening_image B (nativeCriticalBaseEdge B n σ))
  have h₂ := Category.assoc a m d.inv
  have h₃ := congrArg (fun q => a ≫ q) hi
  have h₄ := (Category.assoc a e.inv f).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/-- The original physical minimal critical simplex restriction keeps precisely the SAME full original native cone
edge mate. -/
theorem nativeCriticalMinimalSimplexEdge_image (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).map (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) ≫
      (nativeSimplexImageIso B (n + 2) σ).hom =
    ((nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
      (nativeCriticalMinimalEdgeCompositionIso B n σ).inv) ≫ nativeCriticalConeEdgeMap B n σ := by
  have h₀ := (nativeSimplexChartRestriction_square B (nativeCriticalEdgeOperator.{u} n) σ).symm
  have h₁ := congrArg (fun q => (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫ q)
    (nativeCriticalMinimalEdgeComposition_attachment B n σ).symm
  have h₂ := (Category.assoc (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom
    (nativeCriticalMinimalEdgeCompositionIso B n σ).inv (nativeCriticalConeEdgeMap B n σ)).symm
  exact h₀.trans (h₁.trans h₂)

/-- Actual native straightening of the SAME full SOURCE basis span is the whole original critical interval marking
span. -/
def nativeCriticalSourceCanonicalImageSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ)) (nativeCriticalMinimalHornEdgeOverMap B n σ) ⋙
      nativeStraightening B ≅ span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalHornEdgeMap B n σ) :=
  spanIsoMk
    (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ) ≪≫ (nativeCriticalMinimalEdgeCompositionIso B n σ).symm)
    (nativeSharpImageIso B (nativeCriticalBaseEdge B n σ) ≪≫ (nativeCriticalSharpEdgeCompositionIso B n σ).symm)
    (nativeCriticalMinimalHornSourceIso B n σ)
    (nativeCriticalMarkingCell_image B n σ)
    ((nativeCriticalMinimalHornEdge_image B n σ).trans (Category.assoc _ _ _).symm)

/-- Actual native straightening of the SAME whole TARGET basis span preserves its full original marking and minimal
edge arrows. -/
def nativeCriticalTargetCanonicalImageSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ))
      (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) ⋙ nativeStraightening B ≅
        span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalConeEdgeMap B n σ) :=
  spanIsoMk
    (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ) ≪≫ (nativeCriticalMinimalEdgeCompositionIso B n σ).symm)
    (nativeSharpImageIso B (nativeCriticalBaseEdge B n σ) ≪≫ (nativeCriticalSharpEdgeCompositionIso B n σ).symm)
    (nativeSimplexImageIso B (n + 2) σ)
    (nativeCriticalMarkingCell_image B n σ) (nativeCriticalMinimalSimplexEdge_image B n σ)

/-- The SAME full ORIGINAL native critical SOURCE marking span is identified with the entire original supported
critical interval span through actual whole records and unit mates. -/
def nativeOriginalCriticalSourceMarkingSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ) ⋙ nativeStraightening B ≅
      span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalHornEdgeMap B n σ) :=
  Functor.isoWhiskerRight (nativeCriticalSourceBasisSpanIso B n σ) (nativeStraightening B) ≪≫
    nativeCriticalSourceCanonicalImageSpanIso B n σ

/-- The entire SAME ORIGINAL native critical TARGET marking span retains both actual original arrows in the full
critically marked simplex interval span. -/
def nativeOriginalCriticalTargetMarkingSpanIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ) ⋙ nativeStraightening B ≅
      span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalConeEdgeMap B n σ) :=
  Functor.isoWhiskerRight (nativeCriticalTargetBasisSpanIso B n σ) (nativeStraightening B) ≪≫
    nativeCriticalTargetCanonicalImageSpanIso B n σ

end SSet.Marked
