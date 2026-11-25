/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSuccessorLowerColimits

/-!
# Complete original successor preservation and source squares

Every old order comparison, vertex map, predecessor point and cofan leg, attaching map, cell map
and original comparison component is retained. The actual newborn predecessor comparison is
identified by its genuine colimit legs, yielding the original attaching, vertex and cell-target
squares without a monomorphism or cancellation premise.

## Source and scope

This formalizes preservation in the one-cell successor step of Jacob Lurie's
*Higher Topos Theory*, Lemma A.1.5.7, in the author PDF dated April 9, 2017
(2017-04-09): printed pages 801–802 (PDF pages 819–820). For one constructed
AFTER prefix it retains all nine fields of the given BEFORE prefix and proves
the actual newborn predecessor, attaching and cell-target comparison squares.
The source proof is expressed through abstract cell-tree and chosen-colimit data.
The transfinite history and complete cell-tree goodification are separate
constructions outside this module's successor-only scope.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite
open CategoryTheory.SmallObject.GoodCellExtensionOrder
open CategoryTheory.SmallObject.GoodCellExtensionDiagram
open CategoryTheory.SmallObject.GoodCellExtensionPredecessors
open CategoryTheory.SmallObject.OriginalPredecessorCellCapture
open CategoryTheory.SmallObject.LowerSetColimits

namespace CategoryTheory.SmallObject.OriginalGoodification.TreeProjection

variable {C : Type u} [cCategory : Category.{v} C]
  {B : Type w} {A : Type t} {s : A → Arrow C} {X : C}
  (ord ord' : PartialOrder B)
  (T : @CellTree C cCategory B ord A s X)
  (T' : @CellTree C cCategory B ord' A s X)
  (ho : ord = ord') (hT : T ≍ T')

include ho hT in
theorem tree_vertex_eq (p : B) : (letI := ord; T.vertex p) = (letI := ord'; T'.vertex p) := by
  cases ho
  cases hT
  rfl

include ho hT in
theorem tree_predecessor_eq (p : B) : (letI := ord; T.predecessorObj p) =
    (letI := ord'; T'.predecessorObj p) := by
  cases ho
  cases hT
  rfl

include ho hT in
theorem tree_attaching_heq (p : B) : (letI := ord; T.attaching p) ≍
    (letI := ord'; T'.attaching p) := by
  cases ho
  cases hT
  exact HEq.rfl

include ho hT in
theorem tree_cell_heq (p : B) : (letI := ord; T.cell p) ≍ (letI := ord'; T'.cell p) := by
  cases ho
  cases hT
  exact HEq.rfl

include ho hT in
theorem tree_map_heq (p q : B)
    (h : @LE.le B ord.toLE p q) (h' : @LE.le B ord'.toLE p q) :
    (letI := ord
     letI : Preorder B := ord.toPreorder
     T.diagram.map (homOfLE h : p ⟶ q)) ≍
    (letI := ord'
     letI : Preorder B := ord'.toPreorder
     T'.diagram.map (homOfLE h' : p ⟶ q)) := by
  cases ho
  cases hT
  exact HEq.rfl

include ho hT in
theorem tree_predecessor_leg_heq (p q : B)
    (h : @LT.lt B ord.toLT q p) (h' : @LT.lt B ord'.toLT q p) :
    (letI := ord
     letI : Preorder B := ord.toPreorder
     (T.predecessor p).cocone.ι.app ⟨q, h⟩) ≍
    (letI := ord'
     letI : Preorder B := ord'.toPreorder
     (T'.predecessor p).cocone.ι.app ⟨q, h'⟩) := by
  cases ho
  cases hT
  exact HEq.rfl

end CategoryTheory.SmallObject.OriginalGoodification.TreeProjection

namespace CategoryTheory.SmallObject.OriginalGoodification.TreeProjection

variable {C : Type u} [Category.{v} C]

/-- Projecting a preserved whole Under morphism retains both actual object transports. -/
theorem right_heq {X : C} {U V U' V' : Under X} {f : U ⟶ V} {g : U' ⟶ V'}
    (hU : U = U') (hV : V = V') (hfg : f ≍ g) : f.right ≍ g.right := by
  cases hU
  cases hV
  cases hfg
  exact HEq.rfl

end CategoryTheory.SmallObject.OriginalGoodification.TreeProjection

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder GoodCellExtensionPredecessors

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

theorem prefixEquiv_old (a : before gamma) :
    prefixEquiv gamma (Index.old a) = ⟨a.1, before_le_after gamma a.2⟩ := rfl

theorem prefixEquiv_symm_old (a : before gamma) :
    (prefixEquiv gamma).symm ⟨a.1, before_le_after gamma a.2⟩ = Index.old a :=
  (prefixEquiv gamma).symm_apply_apply (Index.old a)

omit [HasPushouts C] [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorOrder_restrict (a b : before gamma) :
    @LE.le (before gamma) r.ord.toLE a b ↔
      @LE.le (after gamma) (successorOrder O M chi gamma r N).toLE
        ⟨a.1, before_le_after gamma a.2⟩ ⟨b.1, before_le_after gamma b.2⟩ := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  change _ ↔ GoodCellExtensionOrder.extensionLe (successorCapture O M chi gamma r N).support
    ((prefixEquiv gamma).symm ⟨a.1, before_le_after gamma a.2⟩)
    ((prefixEquiv gamma).symm ⟨b.1, before_le_after gamma b.2⟩)
  rw [prefixEquiv_symm_old gamma a, prefixEquiv_symm_old gamma b]
  rfl


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder GoodCellExtensionPredecessors
open TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_vertex (a : before gamma) :
    (letI := successorOrder O M chi gamma r N
     (successorTree O M chi gamma r N).vertex ⟨a.1, before_le_after gamma a.2⟩) =
      (letI := r.ord; r.tree.vertex a) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  change (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
      (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good).vertex
      ((prefixEquiv gamma).symm ⟨a.1, before_le_after gamma a.2⟩) = _
  rw [prefixEquiv_symm_old gamma a]
  rfl

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_predecessor (a : before gamma) :
    (letI := successorOrder O M chi gamma r N
     (successorTree O M chi gamma r N).predecessorObj ⟨a.1, before_le_after gamma a.2⟩) =
      (letI := r.ord; r.tree.predecessorObj a) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  change (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
      (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi
          r.good).predecessorObj
      ((prefixEquiv gamma).symm ⟨a.1, before_le_after gamma a.2⟩) = _
  rw [prefixEquiv_symm_old gamma a]
  rfl

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_attaching (a : before gamma) :
    (letI := successorOrder O M chi gamma r N
     (successorTree O M chi gamma r N).attaching ⟨a.1, before_le_after gamma a.2⟩) ≍
      (letI := r.ord; r.tree.attaching a) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  let T' := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  have step (x y : Index (before gamma)) (hxy : x = y) : T'.attaching x ≍ T'.attaching y := by
    cases hxy
    exact HEq.rfl
  exact step _ _ (prefixEquiv_symm_old gamma a)

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_cell (a : before gamma) :
    (letI := successorOrder O M chi gamma r N
     (successorTree O M chi gamma r N).cell ⟨a.1, before_le_after gamma a.2⟩) ≍
      (letI := r.ord; r.tree.cell a) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  let T' := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  have step (x y : Index (before gamma)) (hxy : x = y) : T'.cell x ≍ T'.cell y := by
    cases hxy
    exact HEq.rfl
  exact step _ _ (prefixEquiv_symm_old gamma a)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder GoodCellExtensionPredecessors

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_map (a b : before gamma)
    (hab : @LE.le (before gamma) r.ord.toLE a b)
    (hab' : @LE.le (after gamma) (successorOrder O M chi gamma r N).toLE
      ⟨a.1, before_le_after gamma a.2⟩ ⟨b.1, before_le_after gamma b.2⟩) :
    (letI := successorOrder O M chi gamma r N
     letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
     (successorTree O M chi gamma r N).diagram.map (homOfLE hab')) ≍
    (letI := r.ord
     letI : Preorder (before gamma) := r.ord.toPreorder
     r.tree.diagram.map (homOfLE hab)) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  let T' := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  have step (x y x' y' : Index (before gamma)) (hx : x = x') (hy : y = y')
      (h : x ≤ y) (h' : x' ≤ y') : T'.diagram.map (homOfLE h) ≍ T'.diagram.map (homOfLE h') := by
    cases hx
    cases hy
    exact HEq.rfl
  have hx : (prefixEquiv gamma).symm ⟨a.1, before_le_after gamma a.2⟩ ≤
      (prefixEquiv gamma).symm ⟨b.1, before_le_after gamma b.2⟩ := by
    rw [prefixEquiv_symm_old gamma a, prefixEquiv_symm_old gamma b]
    exact hab
  exact step _ _ (Index.old a) (Index.old b)
    (prefixEquiv_symm_old gamma a) (prefixEquiv_symm_old gamma b) hx hab

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_old_leg (a z : before gamma)
    (hza : @LT.lt (before gamma) r.ord.toLT z a)
    (hza' : @LT.lt (after gamma) (successorOrder O M chi gamma r N).toLT
      ⟨z.1, before_le_after gamma z.2⟩ ⟨a.1, before_le_after gamma a.2⟩) :
    (letI := successorOrder O M chi gamma r N
     letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
     ((successorTree O M chi gamma r N).predecessor ⟨a.1, before_le_after gamma a.2⟩).cocone.ι.app
       ⟨⟨z.1, before_le_after gamma z.2⟩, hza'⟩) ≍
    (letI := r.ord
     letI : Preorder (before gamma) := r.ord.toPreorder
     (r.tree.predecessor a).cocone.ι.app ⟨z, hza⟩) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  let T' := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  have step (x z x' z' : Index (before gamma)) (hx : x = x') (hz : z = z')
      (h : z < x) (h' : z' < x') :
      (T'.predecessor x).cocone.ι.app ⟨z, h⟩ ≍ (T'.predecessor x').cocone.ι.app ⟨z', h'⟩ := by
    cases hx
    cases hz
    exact HEq.rfl
  have hOld : Index.old z < Index.old a := (old_lt_old _ z a).2 hza
  exact step _ _ (Index.old a) (Index.old z)
    (prefixEquiv_symm_old gamma a) (prefixEquiv_symm_old gamma z) _ hOld

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder GoodCellExtensionPredecessors TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorComparison_old (a : before gamma) :
    (letI := successorOrder O M chi gamma r N
     letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
     (successorComparison O M chi gamma r N).app ⟨a.1, before_le_after gamma a.2⟩) ≍
    (letI := r.ord
     letI : Preorder (before gamma) := r.ord.toPreorder
     r.comparison.app a) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  let beta := OriginalCellExtensionComparison.comparison r.tree N O
    (prefixLabels (before gamma) r.ord r.below) r.comparison (labels.symm gamma)
    (successorPred O M chi gamma r) (fun _ h => h)
    chi r.good (liftedOriginalAttaching O M chi gamma r N)
    (liftedOriginalAttaching_factor O M chi gamma r N)
  have step (x y : Index (before gamma)) (hxy : x = y) : beta.app x ≍ beta.app y := by
    cases hxy
    exact HEq.rfl
  exact step _ _ (prefixEquiv_symm_old gamma a)

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefix_comparison_app_heq {B : LowerSet P}
    (d : Prefix O M chi B) (ord : PartialOrder B)
    (T : letI := ord; CellTree s X (P := B))
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      T.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (ho : d.ord = ord) (hT : d.tree ≍ T)
    (hf : prefixLabels B d.ord d.below ≍ f) (hb : d.comparison ≍ beta) (a : B) :
    (letI := d.ord
     letI : Preorder B := d.ord.toPreorder
     d.comparison.app a) ≍
    (letI := ord
     letI : Preorder B := ord.toPreorder
     beta.app a) := by
  cases ho
  cases hT
  cases hf
  cases hb
  exact HEq.rfl

theorem successorPrefix_preserves :
    Preserves O M chi (before_le_after gamma) r (successorPrefix O M chi gamma r N) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let ord := successorOrder O M chi gamma r N
  let _ := ord
  let _ : Preorder (after gamma) := ord.toPreorder
  let d := successorPrefix O M chi gamma r N
  have hdOrd : d.ord = ord := successorPrefix_order O M chi gamma r N
  have hdTree : d.tree ≍ successorTree O M chi gamma r N := successorPrefix_tree O M chi gamma r N
  have hdBeta : d.comparison ≍ successorComparison O M chi gamma r N :=
    successorPrefix_comparison O M chi gamma r N
  refine {
    order_restrict := ?_
    initial := ?_
    vertices := ?_
    maps := ?_
    predecessorPoints := ?_
    predecessorLegs := ?_
    attaching := ?_
    cells := ?_
    comparisons := ?_ }
  · intro a b
    exact (successorOrder_restrict O M chi gamma r N a b).trans
      (congrArg (fun o : PartialOrder (after gamma) =>
        @LE.le (after gamma) o.toLE ⟨a.1, before_le_after gamma a.2⟩
          ⟨b.1, before_le_after gamma b.2⟩) hdOrd).symm.to_iff
  · intro a b hb hab
    have hOrig : a.1 ≤ b.1 := d.below a b hab
    exact (before gamma).lower' hOrig hb
  · intro a
    exact (successorTree_old_vertex O M chi gamma r N a).symm.trans
      (tree_vertex_eq d.ord ord d.tree (successorTree O M chi gamma r N)
        hdOrd hdTree ⟨a.1, before_le_after gamma a.2⟩).symm
  · intro a b hab
    have habD : @LE.le (after gamma) d.ord.toLE
        ⟨a.1, before_le_after gamma a.2⟩ ⟨b.1, before_le_after gamma b.2⟩ :=
      ((congrArg (fun o : PartialOrder (after gamma) =>
        @LE.le (after gamma) o.toLE ⟨a.1, before_le_after gamma a.2⟩
          ⟨b.1, before_le_after gamma b.2⟩) hdOrd).to_iff).2
        ((successorOrder_restrict O M chi gamma r N a b).1 hab)
    exact (successorTree_old_map O M chi gamma r N a b hab
      ((successorOrder_restrict O M chi gamma r N a b).1 hab)).symm.trans
      (tree_map_heq d.ord ord d.tree (successorTree O M chi gamma r N) hdOrd hdTree
        ⟨a.1, before_le_after gamma a.2⟩ ⟨b.1, before_le_after gamma b.2⟩ habD
        ((successorOrder_restrict O M chi gamma r N a b).1 hab)).symm
  · intro a
    exact (successorTree_old_predecessor O M chi gamma r N a).symm.trans
      (tree_predecessor_eq d.ord ord d.tree (successorTree O M chi gamma r N)
        hdOrd hdTree ⟨a.1, before_le_after gamma a.2⟩).symm
  · intro a z hza hza'
    have hz : @LT.lt (after gamma) ord.toLT
        ⟨z.1, before_le_after gamma z.2⟩ ⟨a.1, before_le_after gamma a.2⟩ :=
      (congrArg (fun o : PartialOrder (after gamma) =>
        @LT.lt (after gamma) o.toLT ⟨z.1, before_le_after gamma z.2⟩
          ⟨a.1, before_le_after gamma a.2⟩) hdOrd).mp hza'
    exact (successorTree_old_leg O M chi gamma r N a z hza hz).symm.trans
      (tree_predecessor_leg_heq d.ord ord d.tree (successorTree O M chi gamma r N)
        hdOrd hdTree ⟨a.1, before_le_after gamma a.2⟩ ⟨z.1, before_le_after gamma z.2⟩ hza' hz).symm
  · intro a
    exact (successorTree_old_attaching O M chi gamma r N a).symm.trans
      (tree_attaching_heq d.ord ord d.tree (successorTree O M chi gamma r N)
        hdOrd hdTree ⟨a.1, before_le_after gamma a.2⟩).symm
  · intro a
    exact (successorTree_old_cell O M chi gamma r N a).symm.trans
      (tree_cell_heq d.ord ord d.tree (successorTree O M chi gamma r N)
        hdOrd hdTree ⟨a.1, before_le_after gamma a.2⟩).symm
  · intro a
    exact (successorComparison_old O M chi gamma r N a).symm.trans
      (prefix_comparison_app_heq O M chi d ord (successorTree O M chi gamma r N)
        (successorLabelHom O M chi gamma r N) (successorComparison O M chi gamma r N)
        hdOrd hdTree (successorPrefix_labels O M chi gamma r N)
        hdBeta ⟨a.1, before_le_after gamma a.2⟩).symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

omit [Nonempty P] in
theorem successorPrefix_new_cell (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (r : Prefix O M chi (before gamma))
    (N : letI := r.ord
      letI : Preorder (before gamma) := r.ord.toPreorder
      LowerSetColimitData r.tree.diagram)
    [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi] :
    letI := successorOrder O M chi gamma r N
    letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
    (successorTree O M chi gamma r N).cell a ≫
        ((successorComparison O M chi gamma r N).app a).right ≍
      O.cell (labels.symm gamma) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  have hn : (prefixEquiv gamma).symm
      (⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩ : after gamma) =
        (Index.new : Index (before gamma)) :=
    (prefixEquiv gamma).symm_apply_apply Index.new
  let T' := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  let beta := OriginalCellExtensionComparison.comparison r.tree N O
    (prefixLabels (before gamma) r.ord r.below) r.comparison (labels.symm gamma)
    (successorPred O M chi gamma r) (fun _ h => h) chi r.good
    (liftedOriginalAttaching O M chi gamma r N) (liftedOriginalAttaching_factor O M chi gamma r N)
  have step (a b : Index (before gamma)) (hab : a = b) :
      T'.cell a ≫ (beta.app a).right ≍ T'.cell b ≫ (beta.app b).right := by
    cases hab
    exact HEq.rfl
  exact (step _ Index.new hn).trans
    (heq_of_eq (newVertexMap_cell r.tree N O (prefixLabels (before gamma) r.ord r.below)
      r.comparison (labels.symm gamma) (successorPred O M chi gamma r) (fun _ h => h)
      chi r.good (liftedOriginalAttaching O M chi gamma r N)
      (liftedOriginalAttaching_factor O M chi gamma r N)))

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefix_cell_projection {B : LowerSet P} (d : Prefix O M chi B)
    (ord : PartialOrder B) (T : letI := ord; CellTree s X (P := B))
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      T.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (ho : d.ord = ord) (hT : d.tree ≍ T)
    (hf : prefixLabels B d.ord d.below ≍ f) (hb : d.comparison ≍ beta) (a : B) :
    (letI := d.ord
     letI : Preorder B := d.ord.toPreorder
     d.tree.cell a ≫ (d.comparison.app a).right) ≍
    (letI := ord
     letI : Preorder B := ord.toPreorder
     T.cell a ≫ (beta.app a).right) := by
  cases ho
  cases hT
  cases hf
  cases hb
  exact HEq.rfl

theorem successorPrefix_new_cell_full (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (r : Prefix O M chi (before gamma))
    (N : letI := r.ord
      letI : Preorder (before gamma) := r.ord.toPreorder
      LowerSetColimitData r.tree.diagram)
    [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
    [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] :
    let d := successorPrefix O M chi gamma r N
    letI := d.ord
    letI : Preorder (after gamma) := d.ord.toPreorder
    let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
    d.tree.cell a ≫ (d.comparison.app a).right ≍ O.cell (labels.symm gamma) := by
  let d := successorPrefix O M chi gamma r N
  let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
  exact (prefix_cell_projection O M chi d (successorOrder O M chi gamma r N)
    (successorTree O M chi gamma r N) (successorLabelHom O M chi gamma r N)
    (successorComparison O M chi gamma r N) (successorPrefix_order O M chi gamma r N)
    (successorPrefix_tree O M chi gamma r N) (successorPrefix_labels O M chi gamma r N)
    (successorPrefix_comparison O M chi gamma r N) a).trans
      (successorPrefix_new_cell O M chi gamma r N)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open GoodCellExtensionOrder GoodCellExtensionPredecessors
open OriginalCellVertexLowerComparison OriginalCapturedCellVertexMap
open LowerSetColimits

variable {P Q : Type w} [PartialOrder P] [PartialOrder Q]
  {C : Type u} [Category.{v} C] [HasPushouts C] {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (L : LowerSetColimitData G.diagram)
  (O : CellTree s X (P := P)) (f : Q →o P) (hf : StrictMono f)
  (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)
  (t : P) (B : LowerSet Q) (hPred : ∀ q : Q, q ∈ B → f q < t)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable (s (O.label t)).left chi] [IsCardinalPresentable (s (O.label t)).right chi]
  (good : G.IsGood chi) (g : (s (O.label t)).left ⟶ (L.obj B).right)
  (hOriginal : g ≫ (lowerMap G L O f beta t B hPred).right = O.attaching t)

include hf in
omit [HasPushouts C] [IsCardinalPresentable (s (O.label t)).right chi] in
theorem extensionLabel_strict :
    letI := extensionOrder (capture G L O t B chi good g).support
    StrictMono (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g) := by
  let _ := extensionOrder (capture G L O t B chi good g).support
  rintro ⟨x⟩ ⟨y⟩ hxy
  cases x with
  | none =>
    cases y with
    | none => exact False.elim ((lt_irrefl (Index.new : Index Q)) hxy)
    | some y => exact False.elim ((new_not_lt_old _ y) hxy)
  | some x =>
    cases y with
    | none => exact hPred x ((capture G L O t B chi good g).below ((old_lt_new _ x).1 hxy))
    | some y => exact hf ((old_lt_old _ x y).1 hxy)

omit [IsCardinalPresentable (s (O.label t)).right chi] in
theorem extensionNewPredecessorComparison :
    letI := extensionOrder (capture G L O t B chi good g).support
    predecessorComparison
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good) O
      (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g)
      (extensionLabel_strict G L O f hf t B hPred chi good g)
      (OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g
          hOriginal) Index.new =
      capturedPredMap G L O f beta t B hPred chi good g := by
  let _ := extensionOrder (capture G L O t B chi good g).support
  let T := OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good
  let j := OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g
  let jStrict := extensionLabel_strict G L O f hf t B hPred chi good g
  let b := OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal
  apply (L.isColimit (capture G L O t B chi good g).support).hom_ext
  intro q
  have h := predecessorComparison_fac T O j jStrict b Index.new (newPredecessorsIso _ q)
  exact h.trans (lowerMap_fac G L O f beta t (capture G L O t B chi good g).support
    (fun q hq => hPred q ((capture G L O t B chi good g).below hq)) q).symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

omit [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorTree_new_attaching :
    let ord := successorOrder O M chi gamma r N
    letI := ord
    letI : Preorder (after gamma) := ord.toPreorder
    let T := successorTree O M chi gamma r N
    let f := successorLabelHom O M chi gamma r N
    let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
    T.attaching a ≫
      (predecessorComparison T O f
        (by
          intro x y hxy
          have hle := f.monotone hxy.le
          have hne : f x ≠ f y := by
            intro he
            have hv := (successorLabelHom_value O M chi gamma r N x).symm.trans
              (he.trans (successorLabelHom_value O M chi gamma r N y))
            exact (ne_of_lt hxy) (Subtype.ext hv)
          exact lt_of_le_of_ne hle hne)
        (successorComparison O M chi gamma r N) a).right ≍ O.attaching (labels.symm gamma) := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let cap := successorCapture O M chi gamma r N
  let _ := extensionOrder cap.support
  let G := OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
    (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good
  let f := OriginalCellExtensionComparison.labelOrderHom r.tree N O
    (prefixLabels (before gamma) r.ord r.below) (labels.symm gamma)
    (successorPred O M chi gamma r) (fun _ h => h) chi r.good
        (liftedOriginalAttaching O M chi gamma r N)
  let hf := extensionLabel_strict r.tree N O (prefixLabels (before gamma) r.ord r.below)
    (prefixLabels_strict O M chi r) (labels.symm gamma) (successorPred O M chi gamma r)
    (fun _ h => h) chi r.good (liftedOriginalAttaching O M chi gamma r N)
  let beta := OriginalCellExtensionComparison.comparison r.tree N O
    (prefixLabels (before gamma) r.ord r.below) r.comparison (labels.symm gamma)
    (successorPred O M chi gamma r) (fun _ h => h) chi r.good
    (liftedOriginalAttaching O M chi gamma r N) (liftedOriginalAttaching_factor O M chi gamma r N)
  let _ := successorOrder O M chi gamma r N
  let _ : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
  let e := pulledIso (prefixEquiv gamma).symm
  let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
  have hn : e a = (Index.new : Index (before gamma)) :=
      (prefixEquiv gamma).symm_apply_apply Index.new
  have hP := predecessorComparison_orderTransport G O f hf beta e a
  have hNew := extensionNewPredecessorComparison r.tree N O
      (prefixLabels (before gamma) r.ord r.below)
    (prefixLabels_strict O M chi r) r.comparison (labels.symm gamma) (successorPred O M chi gamma r)
    (fun _ h => h) chi r.good (liftedOriginalAttaching O M chi gamma r N)
    (liftedOriginalAttaching_factor O M chi gamma r N)
  have hAtt (x y : Index (before gamma)) (hxy : x = y) :
      G.attaching x ≫ (predecessorComparison G O f hf beta x).right ≍
        G.attaching y ≫ (predecessorComparison G O f hf beta y).right := by
    cases hxy
    exact HEq.rfl
  have hTransport :
      (CellTreeOrderReindex.tree e G).attaching a ≫
        (predecessorComparison (CellTreeOrderReindex.tree e G) O
          (OrderIsoLowerColimitTransport.labels e f) (hf.comp e.strictMono)
          (OrderIsoLowerColimitTransport.comparison e f G.diagram O.diagram beta) a).right =
        G.attaching (e a) ≫ (predecessorComparison G O f hf beta (e a)).right :=
    congrArg (fun k => G.attaching (e a) ≫ k.right) hP
  exact (heq_of_eq hTransport).trans ((hAtt _ Index.new hn).trans
    (heq_of_eq (by
      rw [hNew]
      exact capturedPredMap_attaching r.tree N O (prefixLabels (before gamma) r.ord r.below)
        r.comparison (labels.symm gamma) (successorPred O M chi gamma r) (fun _ h => h)
        chi r.good (liftedOriginalAttaching O M chi gamma r N)
        (liftedOriginalAttaching_factor O M chi gamma r N))))

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

theorem successorPrefix_new_attaching (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (r : Prefix O M chi (before gamma))
    (N : letI := r.ord
      letI : Preorder (before gamma) := r.ord.toPreorder
      LowerSetColimitData r.tree.diagram)
    [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
    [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] :
    let d := successorPrefix O M chi gamma r N
    let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
    (letI := d.ord
     d.tree.attaching a ≫ (prefixPredecessorComparison O M chi d a).right) ≍
         O.attaching (labels.symm gamma) := by
  let d := successorPrefix O M chi gamma r N
  let a : after gamma := ⟨labels.symm gamma, by change labels (labels.symm gamma) ≤ gamma; simp⟩
  let hs : @StrictMono (after gamma) P (successorOrder O M chi gamma r N).toPreorder
      pOrder.toPreorder
      (successorLabelHom O M chi gamma r N) := by
    let _ := successorOrder O M chi gamma r N
    let _ : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    intro x y hxy
    have hle := (successorLabelHom O M chi gamma r N).monotone hxy.le
    have hne : (successorLabelHom O M chi gamma r N) x ≠
        (successorLabelHom O M chi gamma r N) y := by
      intro he
      exact (ne_of_lt hxy) (Subtype.ext
        ((successorLabelHom_value O M chi gamma r N x).symm.trans
          (he.trans (successorLabelHom_value O M chi gamma r N y))))
    exact lt_of_le_of_ne hle hne
  exact (prefix_attaching_projection O M chi d (successorOrder O M chi gamma r N)
    (successorTree O M chi gamma r N) (successorLabelHom O M chi gamma r N) hs
    (successorComparison O M chi gamma r N) (successorPrefix_order O M chi gamma r N)
    (successorPrefix_tree O M chi gamma r N) (successorPrefix_labels O M chi gamma r N)
    (successorPrefix_comparison O M chi gamma r N) a).trans
      (successorTree_new_attaching O M chi gamma r N)


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P] [Nonempty P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- The whole original cell-target law uses the actual complete prefix comparison. -/
def PrefixCellSquares {B : LowerSet P} (r : Prefix O M chi B) : Prop :=
  ∀ a : B,
    (letI := r.ord
     letI : Preorder B := r.ord.toPreorder
     r.tree.cell a ≫ (r.comparison.app a).right) ≍ O.cell a.1

omit [WellFoundedLT P] [Nonempty P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem cellSquare_of_preserves {B D : LowerSet P} {hBD : B ≤ D}
    {b : Prefix O M chi B} {d : Prefix O M chi D}
    (h : Preserves O M chi hBD b d) (a : B)
    (ha : (letI := b.ord
      letI : Preorder B := b.ord.toPreorder
      b.tree.cell a ≫ (b.comparison.app a).right) ≍ O.cell a.1) :
    (letI := d.ord
     letI : Preorder D := d.ord.toPreorder
     d.tree.cell ⟨a.1, hBD a.2⟩ ≫ (d.comparison.app ⟨a.1, hBD a.2⟩).right) ≍ O.cell a.1 := by
  have hc := h.cells a
  have hb := h.comparisons a
  have hv := h.vertices a
  have hf := congrArg (fun i => (s i).right) ((b.labels a).trans (d.labels ⟨a.1, hBD a.2⟩).symm)
  have hBetaRight := TreeProjection.right_heq
    hv (by rfl) hb
  have hComp := CategoryTheory.heq_comp
    hf (congrArg Under.right hv) (by rfl) hc hBetaRight
  exact hComp.symm.trans ha

end

end CategoryTheory.SmallObject.OriginalGoodification
