/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalSourceIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalTargetIso

/-!
# The SAME original native critical attaching Arrow Iso

The original source and target marking spans retain their whole
critical cell map and original base records. Their exact native span
isomorphisms commute with the same supported marked horn inclusion.
Actual original colimit uniqueness identifies the attaching map through
BOTH full marked Source and Target Isos, for every whole base map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private theorem nativeCriticalConjugateSpanSquare {D : Type*} [Category D]
    {A A' T T' H K : D} (e : A ≅ A') (d : T ≅ T')
    (a : A' ⟶ T') (p : A' ⟶ H) (q : T' ⟶ K) (k : H ⟶ K)
    (h : a ≫ q = p ≫ k) :
    (e.hom ≫ a ≫ d.inv) ≫ (d.hom ≫ q) = (e.hom ≫ p) ≫ k := by
  calc
    (e.hom ≫ a ≫ d.inv) ≫ (d.hom ≫ q) = e.hom ≫ (a ≫ q) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = e.hom ≫ (p ≫ k) := congrArg (fun f => e.hom ≫ f) h
    _ = (e.hom ≫ p) ≫ k := (Category.assoc e.hom p k).symm

private theorem nativeCriticalLegAttachmentSquare {D : Type*} [Category D]
    {A₀ B₀ C₀ D₀ A B C E : D}
    (sourceLeg : A₀ ⟶ A) (targetLeg : B₀ ⟶ B)
    (hornLeg : C₀ ⟶ C) (coneLeg : D₀ ⟶ E)
    (a : A₀ ⟶ B₀) (b : C₀ ⟶ D₀) (vs : A₀ ⟶ C₀) (vt : B₀ ⟶ D₀)
    (es : A ⟶ C) (et : B ⟶ E) (f : A ⟶ B) (g : C ⟶ E)
    (hCell : sourceLeg ≫ f = a ≫ targetLeg)
    (hTarget : targetLeg ≫ et = vt ≫ coneLeg)
    (hSpan : a ≫ vt = vs ≫ b)
    (hSupported : hornLeg ≫ g = b ≫ coneLeg)
    (hSource : sourceLeg ≫ es = vs ≫ hornLeg) :
    sourceLeg ≫ (f ≫ et) = sourceLeg ≫ (es ≫ g) := by
  calc
    sourceLeg ≫ (f ≫ et) = (sourceLeg ≫ f) ≫ et :=
      (Category.assoc sourceLeg f et).symm
    _ = (a ≫ targetLeg) ≫ et := congrArg (fun q => q ≫ et) hCell
    _ = a ≫ (targetLeg ≫ et) := Category.assoc a targetLeg et
    _ = a ≫ (vt ≫ coneLeg) := congrArg (fun q => a ≫ q) hTarget
    _ = (a ≫ vt) ≫ coneLeg := (Category.assoc a vt coneLeg).symm
    _ = (vs ≫ b) ≫ coneLeg := congrArg (fun q => q ≫ coneLeg) hSpan
    _ = vs ≫ (b ≫ coneLeg) := Category.assoc vs b coneLeg
    _ = vs ≫ (hornLeg ≫ g) := congrArg (fun q => vs ≫ q) hSupported.symm
    _ = (vs ≫ hornLeg) ≫ g := (Category.assoc vs hornLeg g).symm
    _ = (sourceLeg ≫ es) ≫ g := congrArg (fun q => q ≫ g) hSource.symm
    _ = sourceLeg ≫ (es ≫ g) := Category.assoc sourceLeg es g

/-- The SAME original minimal critical horn inclusion gives the complete map between both actual basis marking spans. -/
def nativeCriticalCanonicalBasisSpanMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ)) (nativeCriticalMinimalHornEdgeOverMap B n σ) ⟶
      span (nativeMarkingCell B (nativeCriticalBaseEdge B n σ))
        (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) :=
  spanHomMk (𝟙 _) (𝟙 _)
    (nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((nativeCriticalMinimalHornEdgeOverMap_inclusion B n σ).trans (Category.id_comp _).symm)

/-- Both entire original marking spans retain that SAME actual original critical inclusion through their whole basis
identities. -/
def nativeOriginalCriticalOverMarkingSpanMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ) ⟶
      nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ) :=
  (nativeCriticalSourceBasisSpanIso B n σ).hom ≫ nativeCriticalCanonicalBasisSpanMap B n σ ≫
    (nativeCriticalTargetBasisSpanIso B n σ).inv

/-- The original whole marked critical cell is precisely the point map between its SAME complete original source and
target marking cocones. -/
theorem nativeOriginalCriticalOverCocones_cell (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : WalkingSpan) :
    (nativeCriticalSourceOverMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j ≫
      cartesianCriticalOver n (nativeCriticalProjection B n σ) =
    (nativeOriginalCriticalOverMarkingSpanMap B n σ).app j ≫
      (nativeCriticalTargetOverMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j := by
  rcases j with (_ | _ | _)
  · apply CostructuredArrow.hom_ext
    apply Hom.ext
    have h := congrArg Hom.hom (cartesianCriticalSharpLeg_cell.{u} n)
    exact h
  · apply CostructuredArrow.hom_ext
    exact cartesianCriticalSharpLeg_cell.{u} n
  · apply CostructuredArrow.hom_ext
    exact cartesianCriticalMinimalLeg_cell.{u} n

/-- Actual native straightening retains the SAME original full critical cell map between both complete marking
cocones. -/
theorem nativeOriginalCriticalImageCocones_cell (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : WalkingSpan) :
    (nativeCriticalSourceImageMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j ≫
      (nativeStraightening B).map (cartesianCriticalOver n (nativeCriticalProjection B n σ)) =
    (Functor.whiskerRight (nativeOriginalCriticalOverMarkingSpanMap B n σ) (nativeStraightening B)).app j ≫
      (nativeCriticalTargetImageMarkingCocone B n (nativeCriticalProjection B n σ)).ι.app j := by
  let S := nativeStraightening B
  exact (S.map_comp _ _).symm.trans
    ((congrArg S.map (nativeOriginalCriticalOverCocones_cell B n σ j)).trans (S.map_comp _ _))

/-- The SAME complete supported critical marking spans retain the full original minimally marked horn inclusion. -/
def nativeCriticalSupportedMarkingSpanMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalHornEdgeMap B n σ) ⟶
      span (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalConeEdgeMap B n σ) :=
  spanHomMk (𝟙 _) (𝟙 _) (nativeSupportedRootHornChartMap B σ (Fin.last (n + 2)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((nativeCriticalHornEdgeMap_inclusion B n σ).trans (Category.id_comp _).symm)

/-- The SAME critically marked supported horn attachment is the genuine point map between its complete original
interval marking cocones. -/
theorem nativeCriticalSupportedCocones_cell (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (j : WalkingSpan) :
    (nativeCriticalWholeHornEdgeMarkingCocone B n σ).ι.app j ≫ nativeCriticalSupportedHornChartMap B n σ =
      (nativeCriticalSupportedMarkingSpanMap B n σ).app j ≫
        (nativeCriticalWholeConeEdgeMarkingCocone B n σ).ι.app j := by
  rcases j with (_ | _ | _)
  · change (nativeCriticalEdgeMarkingChartMap B n σ ≫ nativeCriticalHornSharpEdgeMap B n σ) ≫
      nativeCriticalSupportedHornChartMap B n σ =
        𝟙 _ ≫ (nativeCriticalEdgeMarkingChartMap B n σ ≫ nativeCriticalConeSharpEdgeMap B n σ)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => nativeCriticalEdgeMarkingChartMap B n σ ≫ f)
        (nativeCriticalHornSharpEdgeMap_inclusion B n σ)).trans (Category.id_comp _).symm)
  · exact (nativeCriticalHornSharpEdgeMap_inclusion B n σ).trans (Category.id_comp _).symm
  · exact nativeCriticalHornMarkingChartMap_inclusion B n σ

/-- The original full basis-span cell map commutes with BOTH genuine native marking-span image comparisons. -/
theorem nativeCriticalCanonicalImageSpans_cell (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    Functor.whiskerRight (nativeCriticalCanonicalBasisSpanMap B n σ) (nativeStraightening B) ≫
      (nativeCriticalTargetCanonicalImageSpanIso B n σ).hom =
    (nativeCriticalSourceCanonicalImageSpanIso B n σ).hom ≫ nativeCriticalSupportedMarkingSpanMap B n σ := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · change (nativeStraightening B).map (𝟙 _) ≫
      ((nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
        (nativeCriticalMinimalEdgeCompositionIso B n σ).inv) =
      ((nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
        (nativeCriticalMinimalEdgeCompositionIso B n σ).inv) ≫ 𝟙 _
    let e := (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
      (nativeCriticalMinimalEdgeCompositionIso B n σ).inv
    exact ((congrArg (fun f => f ≫ e)
      ((nativeStraightening B).map_id (nativeSimplexBasis B 1 (nativeCriticalBaseEdge B n σ)))).trans
        (Category.id_comp e)).trans (Category.comp_id e).symm
  · change (nativeStraightening B).map (𝟙 _) ≫
      ((nativeSharpImageIso B (nativeCriticalBaseEdge B n σ)).hom ≫
        (nativeCriticalSharpEdgeCompositionIso B n σ).inv) =
      ((nativeSharpImageIso B (nativeCriticalBaseEdge B n σ)).hom ≫
        (nativeCriticalSharpEdgeCompositionIso B n σ).inv) ≫ 𝟙 _
    let e := (nativeSharpImageIso B (nativeCriticalBaseEdge B n σ)).hom ≫
      (nativeCriticalSharpEdgeCompositionIso B n σ).inv
    exact ((congrArg (fun f => f ≫ e)
      ((nativeStraightening B).map_id (nativeSharpBasis B (nativeCriticalBaseEdge B n σ)))).trans
        (Category.id_comp e)).trans (Category.comp_id e).symm
  · exact (nativeCriticalMinimalHornSourceIso_attachment B n σ).symm

/-- Both SAME complete ORIGINAL native marking span isomorphisms retain their actual original critical cell map. -/
theorem nativeOriginalCriticalImageSpans_cell (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    Functor.whiskerRight (nativeOriginalCriticalOverMarkingSpanMap B n σ) (nativeStraightening B) ≫
      (nativeOriginalCriticalTargetMarkingSpanIso B n σ).hom =
    (nativeOriginalCriticalSourceMarkingSpanIso B n σ).hom ≫ nativeCriticalSupportedMarkingSpanMap B n σ := by
  let S := nativeStraightening B
  let e := Functor.isoWhiskerRight (nativeCriticalSourceBasisSpanIso B n σ) S
  let d := Functor.isoWhiskerRight (nativeCriticalTargetBasisSpanIso B n σ) S
  let a := Functor.whiskerRight (nativeCriticalCanonicalBasisSpanMap B n σ) S
  let p := (nativeCriticalSourceCanonicalImageSpanIso B n σ).hom
  let q := (nativeCriticalTargetCanonicalImageSpanIso B n σ).hom
  let k := nativeCriticalSupportedMarkingSpanMap B n σ
  have h : a ≫ q = p ≫ k := nativeCriticalCanonicalImageSpans_cell B n σ
  have hc : Functor.whiskerRight (nativeOriginalCriticalOverMarkingSpanMap B n σ) S =
      e.hom ≫ a ≫ d.inv := by
    dsimp only [nativeOriginalCriticalOverMarkingSpanMap]
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp]
    rfl
  have he : (nativeOriginalCriticalSourceMarkingSpanIso B n σ).hom = e.hom ≫ p := rfl
  have hd : (nativeOriginalCriticalTargetMarkingSpanIso B n σ).hom = d.hom ≫ q := rfl
  calc
    Functor.whiskerRight (nativeOriginalCriticalOverMarkingSpanMap B n σ) S ≫
        (nativeOriginalCriticalTargetMarkingSpanIso B n σ).hom =
        (e.hom ≫ a ≫ d.inv) ≫ (d.hom ≫ q) :=
      congrArg₂ (fun f g => f ≫ g) hc hd
    _ = (e.hom ≫ p) ≫ k := nativeCriticalConjugateSpanSquare e d a p q k h
    _ = (nativeOriginalCriticalSourceMarkingSpanIso B n σ).hom ≫ k :=
      congrArg (fun f => f ≫ k) he.symm

/-- The SAME whole original physical critical attaching map agrees through BOTH actual complete Source and Target
Isos. -/
theorem nativeOriginalCriticalCanonical_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).map (cartesianCriticalOver n (nativeCriticalProjection B n σ)) ≫
      (nativeOriginalCriticalTargetCanonicalIso B n σ).hom =
    (nativeOriginalCriticalSourceCanonicalIso B n σ).hom ≫ nativeCriticalSupportedHornChartMap B n σ := by
  let s := nativeCriticalSourceImageMarkingCocone B n (nativeCriticalProjection B n σ)
  let t := nativeCriticalTargetImageMarkingCocone B n (nativeCriticalProjection B n σ)
  let h := nativeCriticalWholeHornEdgeMarkingCocone B n σ
  let d := nativeCriticalWholeConeEdgeMarkingCocone B n σ
  let a := Functor.whiskerRight (nativeOriginalCriticalOverMarkingSpanMap B n σ) (nativeStraightening B)
  let b := nativeCriticalSupportedMarkingSpanMap B n σ
  let es : s.pt ⟶ h.pt := (nativeOriginalCriticalSourceCanonicalIso B n σ).hom
  let et : t.pt ⟶ d.pt := (nativeOriginalCriticalTargetCanonicalIso B n σ).hom
  let vs := (nativeOriginalCriticalSourceMarkingSpanIso B n σ).hom
  let vt := (nativeOriginalCriticalTargetMarkingSpanIso B n σ).hom
  let f : s.pt ⟶ t.pt :=
    (nativeStraightening B).map (cartesianCriticalOver n (nativeCriticalProjection B n σ))
  let g : h.pt ⟶ d.pt := nativeCriticalSupportedHornChartMap B n σ
  apply (nativeCriticalSourceImageMarkingIsColimit B n (nativeCriticalProjection B n σ)).hom_ext
  intro j
  exact nativeCriticalLegAttachmentSquare
    (s.ι.app j) (t.ι.app j) (h.ι.app j) (d.ι.app j)
    (a.app j) (b.app j) (vs.app j) (vt.app j) es et f g
    (nativeOriginalCriticalImageCocones_cell B n σ j)
    (nativeOriginalCriticalTargetCanonicalIso_leg B n σ j)
    (congr_app (nativeOriginalCriticalImageSpans_cell B n σ) j)
    (nativeCriticalSupportedCocones_cell B n σ j)
    (nativeOriginalCriticalSourceCanonicalIso_leg B n σ j)

/-- Both entire original critical attaching arrows are genuinely isomorphic through the SAME complete marked Source
and Target Isos. -/
def nativeOriginalCriticalCanonicalAttachmentIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n (nativeCriticalProjection B n σ))) ≅
      Arrow.mk (nativeCriticalSupportedHornChartMap B n σ) :=
  Arrow.isoMk (nativeOriginalCriticalSourceCanonicalIso B n σ) (nativeOriginalCriticalTargetCanonicalIso B n σ)
    (nativeOriginalCriticalCanonical_attachment B n σ).symm

private theorem criticalArrowEq_left (B : SSet.{u}) (n : ℕ)
    {p q : cartesianCriticalTarget n ⟶ max B} (h : p = q) :
    (eqToHom (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n r))) h)).left =
    eqToHom (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      (nativeStraightening B).obj (Over.mk (cartesianCriticalCell n ≫ r))) h) := by
  exact Arrow.eqToHom_left
    (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n r))) h)

private theorem criticalArrowEq_right (B : SSet.{u}) (n : ℕ)
    {p q : cartesianCriticalTarget n ⟶ max B} (h : p = q) :
    (eqToHom (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n r))) h)).right =
    eqToHom (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      (nativeStraightening B).obj (Over.mk r)) h) := by
  exact Arrow.eqToHom_right
    (congrArg (fun r : cartesianCriticalTarget n ⟶ max B =>
      Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n r))) h)

/-- Every SAME entire original critical native attaching arrow over an arbitrary whole original base map has its
genuine full marked Arrow Iso. -/
def nativeOriginalCriticalAttachmentIso (B : SSet.{u}) (n : ℕ) (r : cartesianCriticalTarget n ⟶ max B) :
    Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n r)) ≅
      Arrow.mk (nativeCriticalSupportedHornChartMap B n (SSet.yonedaEquiv r.hom)) :=
  eqToIso (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
    Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n p)))
      (nativeCriticalProjection_original B n r).symm) ≪≫
    nativeOriginalCriticalCanonicalAttachmentIso B n (SSet.yonedaEquiv r.hom)

private theorem nativeCriticalArrowTransLeftComputed {D : Type*} [Category D]
    {F G H : Arrow D} (q : F = G)
    (e : G.left ≅ H.left) (d : G.right ≅ H.right)
    (w : e.hom ≫ H.hom = G.hom ≫ d.hom) :
    (eqToIso q ≪≫ Arrow.isoMk e d w).hom.left = (eqToHom q).left ≫ e.hom := by
  rfl

/-- The entire original attaching Arrow Iso uses precisely the SAME complete original critical Source Iso. -/
theorem nativeOriginalCriticalAttachmentIso_hom_left (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalAttachmentIso B n r).hom.left = (nativeOriginalCriticalSourceIso B n r).hom := by
  let σ := SSet.yonedaEquiv r.hom
  let q := (nativeCriticalProjection_original B n r).symm
  have hComputed :
      (nativeOriginalCriticalAttachmentIso B n r).hom.left =
      (eqToHom (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n p))) q)).left ≫
        (nativeOriginalCriticalSourceCanonicalIso B n σ).hom :=
    nativeCriticalArrowTransLeftComputed
      (H := Arrow.mk (nativeCriticalSupportedHornChartMap B n σ))
      (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n p))) q)
      (nativeOriginalCriticalSourceCanonicalIso B n σ)
      (nativeOriginalCriticalTargetCanonicalIso B n σ)
      (nativeOriginalCriticalCanonical_attachment B n σ).symm
  have hSource :
      (nativeOriginalCriticalSourceIso B n r).hom =
      eqToHom (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        (nativeStraightening B).obj (Over.mk (cartesianCriticalCell n ≫ p))) q) ≫
        (nativeOriginalCriticalSourceCanonicalIso B n σ).hom := by
    rfl
  exact hComputed.trans
    ((congrArg (fun f => f ≫ (nativeOriginalCriticalSourceCanonicalIso B n σ).hom)
      (criticalArrowEq_left B n q)).trans hSource.symm)

private theorem nativeCriticalArrowTransRightComputed {D : Type*} [Category D]
    {F G H : Arrow D} (q : F = G)
    (e : G.left ≅ H.left) (d : G.right ≅ H.right)
    (w : e.hom ≫ H.hom = G.hom ≫ d.hom) :
    (eqToIso q ≪≫ Arrow.isoMk e d w).hom.right = (eqToHom q).right ≫ d.hom := by
  rfl

/-- The SAME attaching Arrow Iso retains precisely the whole original critical Target Iso. -/
theorem nativeOriginalCriticalAttachmentIso_hom_right (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeOriginalCriticalAttachmentIso B n r).hom.right = (nativeOriginalCriticalTargetIso B n r).hom := by
  let σ := SSet.yonedaEquiv r.hom
  let q := (nativeCriticalProjection_original B n r).symm
  have hComputed :
      (nativeOriginalCriticalAttachmentIso B n r).hom.right =
      (eqToHom (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n p))) q)).right ≫
        (nativeOriginalCriticalTargetCanonicalIso B n σ).hom :=
    nativeCriticalArrowTransRightComputed
      (H := Arrow.mk (nativeCriticalSupportedHornChartMap B n σ))
      (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        Arrow.mk ((nativeStraightening B).map (cartesianCriticalOver n p))) q)
      (nativeOriginalCriticalSourceCanonicalIso B n σ)
      (nativeOriginalCriticalTargetCanonicalIso B n σ)
      (nativeOriginalCriticalCanonical_attachment B n σ).symm
  have hTarget :
      (nativeOriginalCriticalTargetIso B n r).hom =
      eqToHom (congrArg (fun p : cartesianCriticalTarget n ⟶ max B =>
        (nativeStraightening B).obj (Over.mk p)) q) ≫
        (nativeOriginalCriticalTargetCanonicalIso B n σ).hom := by
    rfl
  exact hComputed.trans
    ((congrArg (fun f => f ≫ (nativeOriginalCriticalTargetCanonicalIso B n σ).hom)
      (criticalArrowEq_right B n q)).trans hTarget.symm)

/-- The SAME whole original physical critical attaching map retains every supplied base record through BOTH entire
original marked source and target isomorphisms. -/
theorem nativeOriginalCritical_attachment (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (nativeStraightening B).map (cartesianCriticalOver n r) ≫ (nativeOriginalCriticalTargetIso B n r).hom =
      (nativeOriginalCriticalSourceIso B n r).hom ≫
        nativeCriticalSupportedHornChartMap B n (SSet.yonedaEquiv r.hom) := by
  have h := (nativeOriginalCriticalAttachmentIso B n r).hom.w
  rw [nativeOriginalCriticalAttachmentIso_hom_left, nativeOriginalCriticalAttachmentIso_hom_right] at h
  exact h.symm

end SSet.Marked
