/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CosimplicialHomCorner
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftFrameHomWeakEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex

/-!
# Original boundary transposition for the relative cosimplicial Hom corner

Every whole map out of the original standard boundary is identified with its
actual coefficient map out of the original latching colimit. The original
source transformation and coefficient map therefore give the literal
latching pushout corner, with every original face equation retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CosimplicialHomCorner

variable {C : Type u} [Category.{v} C]

/-- Each original standard-boundary face gives its full original coefficient Hom map. -/
def boundaryCoefficient (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) (a : SimplexCategory.reedy.Latching n) :
    A.obj (SimplexCategory.reedy.latchingSource a) ⟶ X :=
  SSet.yonedaEquiv ((SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).ι.app a ≫ z)

/-- Every actual original boundary map has the full original coefficient latching cocone. -/
def boundaryCoefficientCocone (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) :
    Cocone (SimplexCategory.reedy.latchingDiagram A n) where
  pt := X
  ι.app a := boundaryCoefficient A X n z a
  ι.naturality {a b} f := by
    let δ := SimplexCategory.reedy.latchingComparison f
    let lb : SSet.stdSimplex.obj (SimplexCategory.reedy.latchingSource b) ⟶ hom A X :=
      (SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).ι.app b ≫ z
    let la : SSet.stdSimplex.obj (SimplexCategory.reedy.latchingSource a) ⟶ hom A X :=
      (SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).ι.app a ≫ z
    have hf := (SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).w f
    have h : SSet.stdSimplex.map δ ≫ lb = la :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ z) hf)
    change A.map δ ≫ SSet.yonedaEquiv lb = SSet.yonedaEquiv la ≫ 𝟙 X
    exact (ResolutionHomComplex.left_map_apply A X δ.op (SSet.yonedaEquiv lb)).symm.trans
      (((SSet.yonedaEquiv_naturality δ lb).trans (congrArg SSet.yonedaEquiv h)).trans
        (Category.comp_id _).symm)

variable [HasFiniteColimits C]

/-- The original full boundary gives its actual map out of the original finite latching colimit. -/
def fromBoundary (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) :
    colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X :=
  colimit.desc _ (boundaryCoefficientCocone A X n z)

/-- Every original latching injection retains exactly its original full boundary coordinate. -/
@[reassoc]
theorem fromBoundary_ι (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) (a : SimplexCategory.reedy.Latching n) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫ fromBoundary A X n z =
      boundaryCoefficient A X n z a := colimit.ι_desc _ a

/-- Every actual map out of the original latching colimit gives its full original standard-face cocone. -/
def latchingHomCocone (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (u : colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X) :
    Cocone (SimplexCategory.reedy.latchingDiagram SSet.stdSimplex.{v} n) where
  pt := hom A X
  ι.app a := (SSet.yonedaEquiv (X := hom A X) (n := SimplexCategory.reedy.latchingSource a)).symm
    (colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫ u)
  ι.naturality {a b} f := by
    let δ := SimplexCategory.reedy.latchingComparison f
    let ib : A.obj (SimplexCategory.reedy.latchingSource b) ⟶ X :=
      colimit.ι (SimplexCategory.reedy.latchingDiagram A n) b ≫ u
    let ia : A.obj (SimplexCategory.reedy.latchingSource a) ⟶ X :=
      colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫ u
    let ea := SSet.yonedaEquiv (X := hom A X) (n := SimplexCategory.reedy.latchingSource a)
    let eb := SSet.yonedaEquiv (X := hom A X) (n := SimplexCategory.reedy.latchingSource b)
    change SSet.stdSimplex.map δ ≫ eb.symm ib = ea.symm ia ≫ 𝟙 (hom A X)
    apply ea.injective
    have h : A.map δ ≫ ib = ia := (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ u) (colimit.w (SimplexCategory.reedy.latchingDiagram A n) f))
    have ht : SSet.stdSimplex.map δ ≫ eb.symm ib = ea.symm ia := by
      apply ea.injective
      exact (SSet.yonedaEquiv_naturality δ (eb.symm ib)).symm.trans
        ((congrArg (fun t => (hom A X).map δ.op t) (eb.apply_symm_apply ib)).trans
          ((ResolutionHomComplex.left_map_apply A X δ.op ib).trans
            (h.trans (ea.apply_symm_apply ia).symm)))
    exact congrArg ea (ht.trans (Category.comp_id _).symm)

/-- The actual original standard-boundary colimit gives the entire original left-Hom boundary map. -/
def toBoundary (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (u : colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X) :
    (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X :=
  (SSet.StandardSimplexBoundaryColimit.isColimit.{v} n).desc (latchingHomCocone A X n u)

/-- Every original standard-face leg recovers the same original latching map under the whole boundary map. -/
@[reassoc]
theorem toBoundary_face (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (u : colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X) (a : SimplexCategory.reedy.Latching n) :
    (SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).ι.app a ≫ toBoundary A X n u =
      SSet.yonedaEquiv.symm (colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫ u) :=
  (SSet.StandardSimplexBoundaryColimit.isColimit.{v} n).fac _ a

/-- The actual coefficient boundary construction recovers every original latching map. -/
theorem fromBoundary_toBoundary (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (u : colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X) :
    fromBoundary A X n (toBoundary A X n u) = u := by
  apply colimit.hom_ext
  intro a
  rw [fromBoundary_ι]
  change SSet.yonedaEquiv (_ ≫ toBoundary A X n u) = _
  exact (congrArg SSet.yonedaEquiv (toBoundary_face A X n u a)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

/-- The actual standard-face colimit recovers every entire original boundary map. -/
theorem toBoundary_fromBoundary (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) :
    toBoundary A X n (fromBoundary A X n z) = z := by
  apply (SSet.StandardSimplexBoundaryColimit.isColimit.{v} n).hom_ext
  intro a
  rw [toBoundary_face, fromBoundary_ι]
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- The full original standard-boundary Hom is exactly the original coefficient latching Hom. -/
def boundaryHomEquiv (A : CosimplicialObject C) (X : C) (n : SimplexCategory) :
    ((SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) ≃
      (colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ X) where
  toFun := fromBoundary A X n
  invFun := toBoundary A X n
  left_inv := toBoundary_fromBoundary A X n
  right_inv := fromBoundary_toBoundary A X n

/-- Restricting the whole original simplex is exactly composition with the original latching map. -/
theorem fromBoundary_restrict (A : CosimplicialObject C) (X : C) (n : SimplexCategory)
    (z : SSet.stdSimplex.obj n ⟶ hom A X) :
    fromBoundary A X n ((SSet.boundary.{v} n.len).ι ≫ z) =
      ReedyStructure.latchingMap SimplexCategory.reedy A n ≫ SSet.yonedaEquiv z := by
  apply colimit.hom_ext
  intro a
  rw [fromBoundary_ι]
  let δ := SimplexCategory.reedy.latchingArrow a
  let t : A.obj n ⟶ X := SSet.yonedaEquiv z
  have he : (SSet.StandardSimplexBoundaryColimit.boundaryCocone.{v} n).ι.app a ≫
      (SSet.boundary.{v} n.len).ι = SSet.stdSimplex.map δ :=
    SSet.StandardSimplexBoundaryColimit.boundaryCocone_ι a
  have hr : colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫
      (ReedyStructure.latchingMap SimplexCategory.reedy A n ≫ t) = A.map δ ≫ t :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ t)
      (ReedyStructure.latchingMap_ι SimplexCategory.reedy A n a))
  change SSet.yonedaEquiv (_ ≫ ((SSet.boundary.{v} n.len).ι ≫ z)) = _
  exact (congrArg SSet.yonedaEquiv ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ z) he))).trans
    (((SSet.yonedaEquiv_naturality δ z).symm.trans
      (ResolutionHomComplex.left_map_apply A X δ.op t)).trans hr.symm)

/-- The entire original source action transposes to the same original latching colimit map. -/
theorem fromBoundary_precomp {A B : CosimplicialObject C} (h : A ⟶ B)
    (X : C) (n : SimplexCategory) (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom B X) :
    fromBoundary A X n (z ≫ precomp h X) =
      colimMap (SimplexCategory.reedy.latchingTransformation h n) ≫ fromBoundary B X n z := by
  apply colimit.hom_ext
  intro a
  rw [fromBoundary_ι, ← Category.assoc, ι_colimMap, Category.assoc, fromBoundary_ι]
  change SSet.yonedaEquiv (_ ≫ (z ≫ precomp h X)) =
    h.app (SimplexCategory.reedy.latchingSource a) ≫ SSet.yonedaEquiv (_ ≫ z)
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- The entire original target action transposes to the same original coefficient composition. -/
theorem fromBoundary_postcomp (A : CosimplicialObject C) {X Y : C} (p : X ⟶ Y)
    (n : SimplexCategory) (z : (SSet.boundary.{v} n.len : SSet.{v}) ⟶ hom A X) :
    fromBoundary A Y n (z ≫ postcomp A p) = fromBoundary A X n z ≫ p := by
  apply colimit.hom_ext
  intro a
  rw [fromBoundary_ι, ← Category.assoc, fromBoundary_ι]
  change SSet.yonedaEquiv (_ ≫ (z ≫ postcomp A p)) = SSet.yonedaEquiv (_ ≫ z) ≫ p
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- Every original weak-constant left frame gives actual Kan-fibration target postcomposition. -/
theorem postcomp_frame_fibration [ModelCategory C] (A : CosimplicialObject C)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hW : ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences C (A.map g))
    {X Y : C} (p : X ⟶ Y) [Fibration p] : Fibration (postcomp A p) := by
  let _ : Cofibration p.op := by
    rw [cofibration_op_iff]
    infer_instance
  have hw : ∀ {a b : SimplexCategoryᵒᵖ} (g : a ⟶ b), weakEquivalences Cᵒᵖ (A.op.map g) := by
    intro a b g
    rw [weakEquivalences_op]
    exact hW g.unop
  have hr := QuillenFrameHomComplex.rightPrecomp_fibration p.op A.op
    (LeftFrameHomWeakEquivalence.opposite_matching_fibration A hA) hw
  exact (fibration_iff _).mpr
    (((fibrations SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk (LeftFrameHomWeakEquivalence.leftRightOppositeIso A X)
        (LeftFrameHomWeakEquivalence.leftRightOppositeIso A Y)
        (LeftFrameHomWeakEquivalence.leftRightOppositeIso_target A p).symm)).mpr
          ((fibration_iff _).mp hr))

/-- Every original entire standard-boundary square against the unchanged relative mapping arrow. -/
abbrev BoundarySquare {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C}
    (p : X ⟶ Y) (n : SimplexCategory) :=
  Arrow.mk (SSet.boundary.{v} n.len).ι ⟶ Arrow.mk (map h p)

/-- Every original coefficient square against the literal original relative latching corner. -/
abbrev CoefficientSquare {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C}
    (p : X ⟶ Y) (n : SimplexCategory) :=
  Arrow.mk (ReedyStructure.latchingCorner SimplexCategory.reedy h n) ⟶ Arrow.mk p

/-- The full original upper boundary gives its same actual coefficient on the B latching colimit. -/
def squareCoefficient {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    colimit (SimplexCategory.reedy.latchingDiagram B n) ⟶ X := fromBoundary B X n s.left

/-- The full original bottom simplex retains its unchanged first coefficient. -/
def squareSource {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) : A.obj n ⟶ X :=
  SSet.yonedaEquiv (s.right ≫ pullback.fst (postcomp A p) (precomp h Y))

/-- The full original bottom simplex retains its unchanged second coefficient. -/
def squareBottom {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) : B.obj n ⟶ Y :=
  SSet.yonedaEquiv (s.right ≫ pullback.snd (postcomp A p) (precomp h Y))

/-- The original entire square's first projection is exactly its actual latching compatibility. -/
theorem square_source_condition {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    ReedyStructure.latchingMap SimplexCategory.reedy A n ≫ squareSource s =
      colimMap (SimplexCategory.reedy.latchingTransformation h n) ≫ squareCoefficient s := by
  have hs : s.left ≫ map h p = (SSet.boundary.{v} n.len).ι ≫ s.right := s.w
  have he := congrArg (fun f => f ≫ pullback.fst (postcomp A p) (precomp h Y)) hs
  have hw : s.left ≫ precomp h X = (SSet.boundary.{v} n.len).ι ≫
      (s.right ≫ pullback.fst (postcomp A p) (precomp h Y)) := by
    simpa only [Category.assoc, map_fst] using he
  have ht := congrArg (fromBoundary A X n) hw
  rw [fromBoundary_precomp, fromBoundary_restrict] at ht
  exact ht.symm

/-- The original entire square's second projection is exactly its actual coefficient commutation. -/
theorem square_target_condition {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    squareCoefficient s ≫ p = ReedyStructure.latchingMap SimplexCategory.reedy B n ≫ squareBottom s := by
  have hs : s.left ≫ map h p = (SSet.boundary.{v} n.len).ι ≫ s.right := s.w
  have he := congrArg (fun f => f ≫ pullback.snd (postcomp A p) (precomp h Y)) hs
  have hw : s.left ≫ postcomp B p = (SSet.boundary.{v} n.len).ι ≫
      (s.right ≫ pullback.snd (postcomp A p) (precomp h Y)) := by
    simpa only [Category.assoc, map_snd] using he
  have ht := congrArg (fromBoundary B Y n) hw
  rw [fromBoundary_postcomp, fromBoundary_restrict] at ht
  exact ht

omit [HasFiniteColimits C] in
/-- The original pullback condition is retained as the whole bottom coefficient square. -/
theorem square_pullback_condition {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    squareSource s ≫ p = h.app n ≫ squareBottom s := by
  have hp : pullback.fst (postcomp A p) (precomp h Y) ≫ postcomp A p =
      pullback.snd (postcomp A p) (precomp h Y) ≫ precomp h Y := pullback.condition
  have he : (s.right ≫ pullback.fst (postcomp A p) (precomp h Y)) ≫ postcomp A p =
      (s.right ≫ pullback.snd (postcomp A p) (precomp h Y)) ≫ precomp h Y := by
    simpa only [Category.assoc] using congrArg (fun f => s.right ≫ f) hp
  have ht := congrArg (SSet.yonedaEquiv (X := hom A Y) (n := n)) he
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at ht
  exact ht

/-- Every original full simplicial square gives the literal original pushout-corner coefficient square. -/
def boundarySquareToCoefficient {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) : CoefficientSquare h p n :=
  Arrow.homMk (pushout.desc (squareSource s) (squareCoefficient s) (square_source_condition s))
    (squareBottom s) (by
      change pushout.desc (squareSource s) (squareCoefficient s) (square_source_condition s) ≫ p =
        ReedyStructure.latchingCorner SimplexCategory.reedy h n ≫ squareBottom s
      apply pushout.hom_ext
      · rw [← Category.assoc, pushout.inl_desc, ← Category.assoc, ReedyStructure.latchingCorner_inl]
        exact square_pullback_condition s
      · rw [← Category.assoc, pushout.inr_desc, ← Category.assoc, ReedyStructure.latchingCorner_inr]
        exact square_target_condition s)

/-- The full original transposed square retains its same original source injection. -/
@[reassoc]
theorem boundarySquareToCoefficient_inl {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    pushout.inl (ReedyStructure.latchingMap SimplexCategory.reedy A n)
      (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫
        (boundarySquareToCoefficient s).left = squareSource s := pushout.inl_desc _ _ _

/-- The full original transposed square retains its same original latching injection. -/
@[reassoc]
theorem boundarySquareToCoefficient_inr {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    pushout.inr (ReedyStructure.latchingMap SimplexCategory.reedy A n)
      (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫
        (boundarySquareToCoefficient s).left = squareCoefficient s := pushout.inr_desc _ _ _

/-- Every original coefficient square gives the whole original standard-boundary square. -/
def coefficientSquareToBoundary {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : CoefficientSquare h p n) : BoundarySquare h p n := by
  let v : A.obj n ⟶ X := pushout.inl (ReedyStructure.latchingMap SimplexCategory.reedy A n)
    (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ s.left
  let u : colimit (SimplexCategory.reedy.latchingDiagram B n) ⟶ X :=
    pushout.inr (ReedyStructure.latchingMap SimplexCategory.reedy A n)
      (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ s.left
  let w : B.obj n ⟶ Y := s.right
  have hs : s.left ≫ p = ReedyStructure.latchingCorner SimplexCategory.reedy h n ≫ w := s.w
  have hv : v ≫ p = h.app n ≫ w := by
    dsimp only [v]
    rw [Category.assoc, hs, ← Category.assoc, ReedyStructure.latchingCorner_inl]
  have hu : u ≫ p = ReedyStructure.latchingMap SimplexCategory.reedy B n ≫ w := by
    dsimp only [u]
    rw [Category.assoc, hs, ← Category.assoc, ReedyStructure.latchingCorner_inr]
  have hb : SSet.yonedaEquiv.symm v ≫ postcomp A p = SSet.yonedaEquiv.symm w ≫ precomp h Y := by
    apply (SSet.yonedaEquiv (X := hom A Y) (n := n)).injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    exact ((congrArg (fun t : A.obj n ⟶ X => t ≫ p)
      ((SSet.yonedaEquiv (X := hom A X) (n := n)).apply_symm_apply v)).trans hv).trans
        (congrArg (fun t : B.obj n ⟶ Y => h.app n ≫ t)
          ((SSet.yonedaEquiv (X := hom B Y) (n := n)).apply_symm_apply w)).symm
  let b : SSet.stdSimplex.obj n ⟶ target h p :=
    pullback.lift (SSet.yonedaEquiv.symm v) (SSet.yonedaEquiv.symm w) hb
  refine Arrow.homMk (toBoundary B X n u) b ?_
  change toBoundary B X n u ≫ map h p = (SSet.boundary.{v} n.len).ι ≫ b
  apply pullback.hom_ext
  · rw [Category.assoc, map_fst, Category.assoc, pullback.lift_fst]
    apply (boundaryHomEquiv A X n).injective
    change fromBoundary A X n _ = fromBoundary A X n _
    rw [fromBoundary_precomp, fromBoundary_restrict, fromBoundary_toBoundary]
    have hh : colimMap (SimplexCategory.reedy.latchingTransformation h n) ≫ u =
        ReedyStructure.latchingMap SimplexCategory.reedy A n ≫ v :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ s.left) (pushout.condition).symm).trans (Category.assoc _ _ _))
    exact hh.trans (congrArg
      (fun t : A.obj n ⟶ X => ReedyStructure.latchingMap SimplexCategory.reedy A n ≫ t)
      ((SSet.yonedaEquiv (X := hom A X) (n := n)).apply_symm_apply v)).symm
  · rw [Category.assoc, map_snd, Category.assoc, pullback.lift_snd]
    apply (boundaryHomEquiv B Y n).injective
    change fromBoundary B Y n _ = fromBoundary B Y n _
    rw [fromBoundary_postcomp, fromBoundary_restrict, fromBoundary_toBoundary]
    exact hu.trans (congrArg
      (fun t : B.obj n ⟶ Y => ReedyStructure.latchingMap SimplexCategory.reedy B n ≫ t)
      ((SSet.yonedaEquiv (X := hom B Y) (n := n)).apply_symm_apply w)).symm

/-- The whole inverse square retains the exact original latching injection on its entire upper boundary. -/
theorem coefficientSquareToBoundary_top {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : CoefficientSquare h p n) :
    (coefficientSquareToBoundary s).left = toBoundary B X n
      (pushout.inr (ReedyStructure.latchingMap SimplexCategory.reedy A n)
        (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ s.left) := rfl

/-- The whole inverse square retains its same original first coefficient on its bottom simplex. -/
@[reassoc]
theorem coefficientSquareToBoundary_fst {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : CoefficientSquare h p n) :
    (coefficientSquareToBoundary s).right ≫ pullback.fst (postcomp A p) (precomp h Y) =
      SSet.yonedaEquiv.symm (pushout.inl (ReedyStructure.latchingMap SimplexCategory.reedy A n)
        (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ s.left) := pullback.lift_fst _ _ _

/-- The whole inverse square retains its same original second coefficient on its bottom simplex. -/
@[reassoc]
theorem coefficientSquareToBoundary_snd {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : CoefficientSquare h p n) :
    (coefficientSquareToBoundary s).right ≫ pullback.snd (postcomp A p) (precomp h Y) =
      SSet.yonedaEquiv.symm s.right := pullback.lift_snd _ _ _

/-- The whole boundary transposition returns every unchanged original coefficient square. -/
theorem boundarySquareToCoefficient_coefficientSquareToBoundary {A B : CosimplicialObject C}
    {h : A ⟶ B} {X Y : C} {p : X ⟶ Y} {n : SimplexCategory} (s : CoefficientSquare h p n) :
    boundarySquareToCoefficient (coefficientSquareToBoundary s) = s := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · rw [boundarySquareToCoefficient_inl]
      change SSet.yonedaEquiv (_ ≫ pullback.fst _ _) = _
      exact (congrArg (SSet.yonedaEquiv (X := hom A X) (n := n))
        (coefficientSquareToBoundary_fst s)).trans (SSet.yonedaEquiv.apply_symm_apply _)
    · rw [boundarySquareToCoefficient_inr]
      change fromBoundary B X n _ = _
      rw [coefficientSquareToBoundary_top, fromBoundary_toBoundary]
  · change SSet.yonedaEquiv (_ ≫ pullback.snd _ _) = _
    exact (congrArg (SSet.yonedaEquiv (X := hom B Y) (n := n))
      (coefficientSquareToBoundary_snd s)).trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- The whole coefficient transposition returns every unchanged entire original boundary square. -/
theorem coefficientSquareToBoundary_boundarySquareToCoefficient {A B : CosimplicialObject C}
    {h : A ⟶ B} {X Y : C} {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    coefficientSquareToBoundary (boundarySquareToCoefficient s) = s := by
  apply Arrow.hom_ext
  · rw [coefficientSquareToBoundary_top, boundarySquareToCoefficient_inr]
    exact toBoundary_fromBoundary B X n s.left
  · apply pullback.hom_ext
    · rw [coefficientSquareToBoundary_fst, boundarySquareToCoefficient_inl]
      exact SSet.yonedaEquiv.symm_apply_apply _
    · rw [coefficientSquareToBoundary_snd]
      exact SSet.yonedaEquiv.symm_apply_apply _

/-- Every entire original boundary square is exactly its literal original latching-corner square. -/
def boundarySquareEquiv {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C}
    (p : X ⟶ Y) (n : SimplexCategory) : BoundarySquare h p n ≃ CoefficientSquare h p n where
  toFun := boundarySquareToCoefficient
  invFun := coefficientSquareToBoundary
  left_inv := coefficientSquareToBoundary_boundarySquareToCoefficient
  right_inv := boundarySquareToCoefficient_coefficientSquareToBoundary

/-- Every whole original simplicial filler is its same original coefficient filler of the literal latching corner. -/
def boundaryLiftToCoefficient {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} {s : BoundarySquare h p n} (l : Arrow.LiftStruct s) :
    Arrow.LiftStruct (boundarySquareToCoefficient s) where
  l := SSet.yonedaEquiv l.l
  fac_left := by
    let c : B.obj n ⟶ X := SSet.yonedaEquiv l.l
    change ReedyStructure.latchingCorner SimplexCategory.reedy h n ≫ c =
      (boundarySquareToCoefficient s).left
    apply pushout.hom_ext
    · rw [← Category.assoc, ReedyStructure.latchingCorner_inl, boundarySquareToCoefficient_inl]
      have hr : l.l ≫ map h p = s.right := l.fac_right
      have he := congrArg (fun f => f ≫ pullback.fst (postcomp A p) (precomp h Y)) hr
      have ht : l.l ≫ precomp h X = s.right ≫ pullback.fst (postcomp A p) (precomp h Y) := by
        simpa only [Category.assoc, map_fst] using he
      have hv := congrArg (SSet.yonedaEquiv (X := hom A X) (n := n)) ht
      rw [SSet.yonedaEquiv_comp] at hv
      exact hv
    · rw [← Category.assoc, ReedyStructure.latchingCorner_inr, boundarySquareToCoefficient_inr]
      have hl : (SSet.boundary.{v} n.len).ι ≫ l.l = s.left := l.fac_left
      have he := congrArg (fromBoundary B X n) hl
      rw [fromBoundary_restrict] at he
      exact he
  fac_right := by
    change SSet.yonedaEquiv l.l ≫ p = squareBottom s
    have hr : l.l ≫ map h p = s.right := l.fac_right
    have he := congrArg (fun f => f ≫ pullback.snd (postcomp A p) (precomp h Y)) hr
    have ht : l.l ≫ postcomp B p = s.right ≫ pullback.snd (postcomp A p) (precomp h Y) := by
      simpa only [Category.assoc, map_snd] using he
    have hv := congrArg (SSet.yonedaEquiv (X := hom B Y) (n := n)) ht
    rw [SSet.yonedaEquiv_comp] at hv
    exact hv

/-- Every original coefficient filler gives the entire original standard-simplex filler of the original square. -/
def coefficientLiftToBoundary {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} {s : BoundarySquare h p n}
    (l : Arrow.LiftStruct (boundarySquareToCoefficient s)) : Arrow.LiftStruct s where
  l := SSet.yonedaEquiv.symm l.l
  fac_left := by
    change (SSet.boundary.{v} n.len).ι ≫ SSet.yonedaEquiv.symm l.l = s.left
    have hl : ReedyStructure.latchingCorner SimplexCategory.reedy h n ≫ l.l =
        (boundarySquareToCoefficient s).left := l.fac_left
    have he := congrArg (fun f => pushout.inr (ReedyStructure.latchingMap SimplexCategory.reedy A n)
      (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ f) hl
    have hB : ReedyStructure.latchingMap SimplexCategory.reedy B n ≫ l.l = squareCoefficient s := by
      simpa only [← Category.assoc, ReedyStructure.latchingCorner_inr, boundarySquareToCoefficient_inr] using he
    apply (boundaryHomEquiv B X n).injective
    change fromBoundary B X n _ = fromBoundary B X n _
    rw [fromBoundary_restrict]
    exact (congrArg (fun f : B.obj n ⟶ X => ReedyStructure.latchingMap SimplexCategory.reedy B n ≫ f)
      ((SSet.yonedaEquiv (X := hom B X) (n := n)).apply_symm_apply l.l)).trans hB
  fac_right := by
    change SSet.yonedaEquiv.symm l.l ≫ map h p = s.right
    apply pullback.hom_ext
    · rw [Category.assoc, map_fst]
      have hl : ReedyStructure.latchingCorner SimplexCategory.reedy h n ≫ l.l =
          (boundarySquareToCoefficient s).left := l.fac_left
      have he := congrArg (fun f => pushout.inl (ReedyStructure.latchingMap SimplexCategory.reedy A n)
        (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ≫ f) hl
      have hA : h.app n ≫ l.l = squareSource s := by
        simpa only [← Category.assoc, ReedyStructure.latchingCorner_inl, boundarySquareToCoefficient_inl] using he
      apply (SSet.yonedaEquiv (X := hom A X) (n := n)).injective
      exact ((SSet.yonedaEquiv_comp _ _).trans
        (congrArg (fun f : B.obj n ⟶ X => h.app n ≫ f)
          ((SSet.yonedaEquiv (X := hom B X) (n := n)).apply_symm_apply l.l))).trans hA
    · rw [Category.assoc, map_snd]
      have hr : l.l ≫ p = squareBottom s := l.fac_right
      apply (SSet.yonedaEquiv (X := hom B Y) (n := n)).injective
      exact ((SSet.yonedaEquiv_comp _ _).trans
        (congrArg (fun f : B.obj n ⟶ X => f ≫ p)
          ((SSet.yonedaEquiv (X := hom B X) (n := n)).apply_symm_apply l.l))).trans hr

/-- Every entire original square has exactly the same fillers as its literal original latching-corner square. -/
def boundaryLiftEquiv {A B : CosimplicialObject C} {h : A ⟶ B} {X Y : C}
    {p : X ⟶ Y} {n : SimplexCategory} (s : BoundarySquare h p n) :
    Arrow.LiftStruct s ≃ Arrow.LiftStruct (boundarySquareToCoefficient s) where
  toFun := boundaryLiftToCoefficient
  invFun := coefficientLiftToBoundary
  left_inv l := by
    apply CommSq.LiftStruct.ext
    exact (SSet.yonedaEquiv (X := hom B X) (n := n)).symm_apply_apply l.l
  right_inv l := by
    apply CommSq.LiftStruct.ext
    exact (SSet.yonedaEquiv (X := hom B X) (n := n)).apply_symm_apply l.l

/-- The original whole boundary lifting property is exactly the original coefficient latching-corner lifting
property. -/
theorem boundary_lifting_iff {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C}
    (p : X ⟶ Y) (n : SimplexCategory) :
    HasLiftingProperty (SSet.boundary.{v} n.len).ι (map h p) ↔
      HasLiftingProperty (ReedyStructure.latchingCorner SimplexCategory.reedy h n) p := by
  rw [Arrow.hasLiftingProperty_iff, Arrow.hasLiftingProperty_iff]
  constructor
  · intro hl s
    obtain ⟨l⟩ := hl (coefficientSquareToBoundary s)
    have lt := boundaryLiftToCoefficient l
    rw [boundarySquareToCoefficient_coefficientSquareToBoundary] at lt
    exact ⟨lt⟩
  · intro hl s
    obtain ⟨l⟩ := hl (boundarySquareToCoefficient s)
    exact ⟨coefficientLiftToBoundary l⟩

/-- Original Reedy cofibration corners and an original trivial fibration give a trivial Kan fibration of the
actual corner. -/
theorem map_trivialFibration [ModelCategory C] {A B : CosimplicialObject C} (h : A ⟶ B)
    (hh : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy h n))
    {X Y : C} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] : trivialFibrations SSet.{v} (map h p) := by
  rw [← cofibrations_rlp SSet.{v}, SSet.modelCategoryQuillen.cofibrations_eq, SSet.rlp_monomorphisms]
  intro K L j hj
  obtain ⟨n⟩ := hj
  let _ : Cofibration (ReedyStructure.latchingCorner SimplexCategory.reedy h ⦋n⦌) :=
    (cofibration_iff _).mpr (hh ⦋n⦌)
  exact (boundary_lifting_iff h p ⦋n⦌).mpr inferInstance

/-- Original weak-constant Reedy frames derive the actual relative corner Kan fibration from the two original
base factories. -/
theorem map_fibration [ModelCategory C]
    (Fc : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (Ff : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {A B : CosimplicialObject C} (h : A ⟶ B)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hh : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy h n))
    (hWA : ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences C (A.map g))
    (hWB : ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences C (B.map g))
    {X Y : C} (p : X ⟶ Y) [Fibration p] : Fibration (map h p) := by
  let _ := arrowModel Fc Ff
  let _ : Fibration (identityToArrow p) := identityToArrow_fibration Fc Ff p
  have hr := postcomp_frame_fibration (arrowDiagram h)
    (arrowDiagram_latching_cofibration Fc Ff h hA hh)
    (arrowDiagram_map_weak Fc Ff h hWA hWB) (identityToArrow p)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{v}).arrow_mk_iso_iff (arrowPostcompIso h p)).mp ((fibration_iff _).mp hr))

omit [HasFiniteColimits C] in
/-- Every original frame augmentation with original weak coefficients derives weakness of every original operator. -/
theorem augmentation_map_weak [ModelCategory C] (A : CosimplicialObject C) (K : C)
    (a : A ⟶ (CosimplicialObject.const C).obj K)
    (ha : ∀ n, weakEquivalences C (a.app n)) {i j : SimplexCategory} (g : i ⟶ j) :
    weakEquivalences C (A.map g) := by
  have he : A.map g ≫ a.app j = a.app i := by
    have ht := a.naturality g
    change A.map g ≫ a.app j = a.app i ≫ 𝟙 K at ht
    exact ht.trans (Category.comp_id _)
  exact (weakEquivalences C).of_postcomp _ _ (ha j) (he.symm ▸ ha i)

/-- The actual original frame augmentations derive the whole relative corner Kan fibration, including all
original operators. -/
theorem map_fibration_of_augmentations [ModelCategory C]
    (Fc : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (Ff : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {A B : CosimplicialObject C} (h : A ⟶ B)
    (hA : ∀ n, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hh : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy h n))
    (K L : C) (a : A ⟶ (CosimplicialObject.const C).obj K)
    (b : B ⟶ (CosimplicialObject.const C).obj L)
    (ha : ∀ n, weakEquivalences C (a.app n)) (hb : ∀ n, weakEquivalences C (b.app n))
    {X Y : C} (p : X ⟶ Y) [Fibration p] : Fibration (map h p) :=
  map_fibration Fc Ff h hA hh (augmentation_map_weak A K a ha) (augmentation_map_weak B L b hb) p

/-- Original trivial Reedy cofibration corners give a trivial Kan fibration of the actual corner against any
original base fibration. -/
theorem map_trivialFibration_of_source_weak [ModelCategory C] {A B : CosimplicialObject C} (h : A ⟶ B)
    (hh : ∀ n, cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy h n))
    (hw : ∀ n, weakEquivalences C (h.app n)) {X Y : C} (p : X ⟶ Y) [Fibration p] :
    trivialFibrations SSet.{v} (map h p) := by
  rw [← cofibrations_rlp SSet.{v}, SSet.modelCategoryQuillen.cofibrations_eq, SSet.rlp_monomorphisms]
  intro K L j hj
  obtain ⟨n⟩ := hj
  have ht := ReedyModel.latchingCorner_trivialCofibration_of_cofibration_weak
    SimplexCategory.reedy h hh hw ⦋n⦌
  let _ : Cofibration (ReedyStructure.latchingCorner SimplexCategory.reedy h ⦋n⦌) :=
    (cofibration_iff _).mpr ht.1
  let _ : WeakEquivalence (ReedyStructure.latchingCorner SimplexCategory.reedy h ⦋n⦌) :=
    (weakEquivalence_iff _).mpr ht.2
  exact (boundary_lifting_iff h p ⦋n⦌).mpr inferInstance

end HomotopicalAlgebra.CosimplicialHomCorner
