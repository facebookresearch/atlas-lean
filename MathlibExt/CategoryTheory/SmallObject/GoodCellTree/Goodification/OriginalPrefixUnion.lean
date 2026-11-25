/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPrefixData
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyLowerColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeOrderReindex

/-!
# Complete original good prefixes on literal original unions

Actual directed compatible prefixes glue on any original lower carrier, including a proper one.
Their whole original diagrams, predecessor cocones, cell maps and comparison components are
retained. Every original lower comparison universal property is constructed from the original
filtered lower intersections. The original root and whole union have no compactness bound.

## Source and scope

This is intermediate infrastructure for Jacob Lurie's *Higher Topos Theory*,
Lemma A.1.5.7, in the author PDF dated April 9, 2017: printed pages 801–802
(PDF pages 819–820). The chosen original tree, lower colimits and root remain
explicit. These modules formalize complete prefix data, original comparison
maps and compatible prefix unions. Complete cell-tree goodification is the
separate construction in `OriginalCellTreeGoodification`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite

namespace CategoryTheory.SmallObject.OriginalGoodification


section FixedOrder

variable {P I : Type w} [PartialOrder P] [Preorder I]
  {C : Type u} [Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)

include hDirected hMono in
-- The induction keeps ordered old data. A common upper stage derives every full overlap.
/-- A common upper stage derives every actual full overlap from ordered preservation. -/
theorem fullOverlap_of_ordered
    (hLabels : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (T i).label ⟨p, hi⟩ = (T j).label ⟨p, hj⟩)
    (hPoints : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (T i).predecessorObj ⟨p, hi⟩ = (T j).predecessorObj ⟨p, hj⟩)
    (hLegs : ∀ (i j : I) (_ : i ≤ j) (p q : P)
      (hi : p ∈ S i) (hj : p ∈ S j) (hqp : q < p),
      ((T i).predecessor ⟨p, hi⟩).cocone.ι.app
        ⟨⟨q, (S i).lower' hqp.le hi⟩, hqp⟩ ≍
      ((T j).predecessor ⟨p, hj⟩).cocone.ι.app
        ⟨⟨q, (S j).lower' hqp.le hj⟩, hqp⟩)
    (hAttaching : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (T i).attaching ⟨p, hi⟩ ≍ (T j).attaching ⟨p, hj⟩)
    (hCells : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (T i).cell ⟨p, hi⟩ ≍ (T j).cell ⟨p, hj⟩) :
    InitialCellTreeFullCompatibility.Overlap S T where
  labels i j p hi hj := by
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact (hLabels i k hik p hi (hMono hik hi)).trans
      (hLabels j k hjk p hj (hMono hjk hj)).symm
  predecessorPoints i j p hi hj := by
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact (hPoints i k hik p hi (hMono hik hi)).trans
      (hPoints j k hjk p hj (hMono hjk hj)).symm
  predecessorLegs i j p q hi hj hqp := by
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact (hLegs i k hik p q hi (hMono hik hi) hqp).trans
      (hLegs j k hjk p q hj (hMono hjk hj) hqp).symm
  attaching i j p hi hj := by
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact (hAttaching i k hik p hi (hMono hik hi)).trans
      (hAttaching j k hjk p hj (hMono hjk hj)).symm
  cells i j p hi hj := by
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact (hCells i k hik p hi (hMono hik hi)).trans
      (hCells j k hjk p hj (hMono hjk hj)).symm

end FixedOrder

section OriginalOrders

open InitialOrderFamilyGlue

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hInitial : ∀ (i j : I) (_ : i ≤ j) (a b : S j), b.1 ∈ S i →
    @LE.le (S j) (orders j).toLE a b → a.1 ∈ S i)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  {C : Type u} [Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))

-- The local orders and their real strict-predecessor legs are used before reindexing.
/-- Actual refining orders derive the full predecessor and cell overlap on original labels. -/
theorem originalFullOverlap_of_ordered
    (hLabels : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (letI := orders i; (T i).label ⟨p, hi⟩) =
        (letI := orders j; (T j).label ⟨p, hj⟩))
    (hPoints : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (letI := orders i; (T i).predecessorObj ⟨p, hi⟩) =
        (letI := orders j; (T j).predecessorObj ⟨p, hj⟩))
    (hLegs : ∀ (i j : I) (_ : i ≤ j) (p q : P)
      (hi : p ∈ S i) (hj : p ∈ S j) (hqi : q ∈ S i) (hqj : q ∈ S j)
      (hqp_i : @LT.lt (S i) (orders i).toLT ⟨q, hqi⟩ ⟨p, hi⟩)
      (hqp_j : @LT.lt (S j) (orders j).toLT ⟨q, hqj⟩ ⟨p, hj⟩),
      (letI := orders i
       letI : Preorder (S i) := (orders i).toPreorder
       ((T i).predecessor ⟨p, hi⟩).cocone.ι.app ⟨⟨q, hqi⟩, hqp_i⟩) ≍
      (letI := orders j
       letI : Preorder (S j) := (orders j).toPreorder
       ((T j).predecessor ⟨p, hj⟩).cocone.ι.app ⟨⟨q, hqj⟩, hqp_j⟩))
    (hAttaching : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (letI := orders i; (T i).attaching ⟨p, hi⟩) ≍
        (letI := orders j; (T j).attaching ⟨p, hj⟩))
    (hCells : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
      (letI := orders i; (T i).cell ⟨p, hi⟩) ≍
        (letI := orders j; (T j).cell ⟨p, hj⟩)) :
    let ls := lower S orders hDirected hMono hRestrict hBelow hCover
    let gs := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    InitialCellTreeFullCompatibility.Overlap ls gs := by
  let ls := lower S orders hDirected hMono hRestrict hBelow hCover
  let gs := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let _ := order S orders hDirected hMono hRestrict hBelow hCover
  apply fullOverlap_of_ordered ls gs hDirected hMono
  · intro i j hij p hi hj
    exact hLabels i j hij p hi hj
  · intro i j hij p hi hj
    exact hPoints i j hij p hi hj
  · intro i j hij p q hi hj hqp
    let qi : S i := ⟨q, (ls i).lower' hqp.le hi⟩
    let qj : S j := ⟨q, (ls j).lower' hqp.le hj⟩
    have hqi : @LT.lt (S i) (orders i).toLT qi ⟨p, hi⟩ := by
      let _ := orders i
      let _ : Preorder (S i) := (orders i).toPreorder
      exact (stageIso (pOrder := pOrder) S orders hDirected hMono hRestrict
        hInitial hBelow hCover i).strictMono
        (show (⟨q, qi.2⟩ : ls i) < ⟨p, hi⟩ from hqp)
    have hqj : @LT.lt (S j) (orders j).toLT qj ⟨p, hj⟩ := by
      let _ := orders j
      let _ : Preorder (S j) := (orders j).toPreorder
      exact (stageIso (pOrder := pOrder) S orders hDirected hMono hRestrict
        hInitial hBelow hCover j).strictMono
        (show (⟨q, qj.2⟩ : ls j) < ⟨p, hj⟩ from hqp)
    exact hLegs i j hij p q hi hj qi.2 qj.2 hqi hqj
  · intro i j hij p hi hj
    exact hAttaching i j hij p hi hj
  · intro i j hij p hi hj
    exact hCells i j hij p hi hj

end OriginalOrders

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- The same original lower support, viewed on the literal containing carrier. -/
def inside (B D : LowerSet P) : LowerSet B where
  carrier := {p | p.1 ∈ D}
  lower' := fun _ _ h hp => D.lower' h hp

/-- The original support has its literal label bijection inside its containing carrier. -/
def insideEquiv (B D : LowerSet P) (hDB : D ≤ B) : inside B D ≃ D where
  toFun p := ⟨p.1.1, p.2⟩
  invFun p := ⟨⟨p.1, hDB p.2⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {I : Type w} [Preorder I] (B : LowerSet P)
  (S : I → LowerSet P) (hInto : ∀ i : I, S i ≤ B) (hMono : Monotone S)
  (F : ∀ i : I, Prefix O M chi (S i))
  (hPreserves : ∀ (i j : I) (hij : i ≤ j),
    Preserves O M chi (hMono hij) (F i) (F j))

/-- The actual refining order is pulled back through the same original support labels. -/
@[instance_reducible]
def insideOrders (i : I) : PartialOrder (inside B (S i)) :=
  @PartialOrder.lift (inside B (S i)) (S i) (F i).ord
    (insideEquiv B (S i) (hInto i)) (insideEquiv B (S i) (hInto i)).injective

/-- The pulled order keeps its actual original-label order isomorphism. -/
def insideOrderIso (i : I) :
    @OrderIso (inside B (S i)) (S i)
      (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i).toLE (F i).ord.toLE where
  toEquiv := insideEquiv B (S i) (hInto i)
  map_rel_iff' := Iff.rfl

/-- Every actual original prefix field is transported to its literal inside carrier. -/
def insideTree (i : I) :
    letI := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i
    CellTree s X (P := inside B (S i)) :=
  @CellTreeOrderReindex.tree C cCategory (S i) (inside B (S i)) (F i).ord
    (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i) A s X
    (insideOrderIso (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i) (F i).tree

include hMono in
/-- Original support inclusions are monotone on the same containing carrier. -/
theorem insideMono : Monotone (fun i : I => inside B (S i)) :=
  fun _ _ hij _ hp => hMono hij hp

include hPreserves in
/-- Full old-order restriction is retained by the literal inside-label functions. -/
theorem insideRestrict (i j : I) (hij : i ≤ j) (a b : B)
    (ha : a ∈ inside B (S i)) (hb : b ∈ inside B (S i)) :
    @LE.le (inside B (S i)) (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (inside B (S j)) (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) j).toLE
        ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩ :=
  (hPreserves i j hij).order_restrict ⟨a.1, ha⟩ ⟨b.1, hb⟩

include hPreserves in
/-- The old original supports remain initial in every later refining order. -/
theorem insideInitial (i j : I) (hij : i ≤ j)
    (a b : inside B (S j)) (hb : b.1 ∈ inside B (S i))
    (hab : @LE.le (inside B (S j)) (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) j).toLE a b) :
    a.1 ∈ inside B (S i) :=
  (hPreserves i j hij).initial ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩ hb hab

omit [Preorder I] in
/-- Every transported new comparison remains an original comparison. -/
theorem insideBelow (i : I) (a b : inside B (S i))
    (hab : @LE.le (inside B (S i)) (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i).toLE a b) :
    a.1 ≤ b.1 := (F i).below ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩ hab

include hPreserves in
/-- Every original vertex object is retained under the same inside-label functions. -/
theorem insideObjects (i j : I) (hij : i ≤ j) (p : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    (letI := os i; (ts i).vertex ⟨p, hi⟩) =
      (letI := os j; (ts j).vertex ⟨p, hj⟩) :=
  (hPreserves i j hij).vertices ⟨p.1, hi⟩

include hPreserves in
/-- Every complete original diagram map is retained under literal inside labels. -/
theorem insideMaps (i j : I) (hij : i ≤ j) (a b : B)
    (ha : a ∈ inside B (S i)) (hb : b ∈ inside B (S i)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    ∀ (hab : @LE.le (inside B (S i)) (os i).toLE ⟨a, ha⟩ ⟨b, hb⟩),
      (letI := os i
       letI : Preorder (inside B (S i)) := (os i).toPreorder
       (ts i).diagram.map (homOfLE hab : (⟨a, ha⟩ : inside B (S i)) ⟶ ⟨b, hb⟩)) ≍
      (letI := os j
       letI : Preorder (inside B (S j)) := (os j).toPreorder
       (ts j).diagram.map
         (homOfLE (((hPreserves i j hij).order_restrict ⟨a.1, ha⟩ ⟨b.1, hb⟩).1 hab) :
           (⟨a, hMono hij ha⟩ : inside B (S j)) ⟶ ⟨b, hMono hij hb⟩)) := by
  dsimp only
  intro hab
  exact (hPreserves i j hij).maps ⟨a.1, ha⟩ ⟨b.1, hb⟩ hab

include hPreserves in
/-- Every original selected predecessor point is retained inside the same carrier. -/
theorem insidePoints (i j : I) (hij : i ≤ j) (p : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    (letI := os i; (ts i).predecessorObj ⟨p, hi⟩) =
      (letI := os j; (ts j).predecessorObj ⟨p, hj⟩) :=
  (hPreserves i j hij).predecessorPoints ⟨p.1, hi⟩

include hPreserves in
/-- All actual strict-predecessor cofan legs are retained on original labels. -/
theorem insideLegs (i j : I) (hij : i ≤ j) (p z : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j))
    (hzi : z ∈ inside B (S i)) (hzj : z ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    ∀ (hzp_i : @LT.lt (inside B (S i)) (os i).toLT ⟨z, hzi⟩ ⟨p, hi⟩)
      (hzp_j : @LT.lt (inside B (S j)) (os j).toLT ⟨z, hzj⟩ ⟨p, hj⟩),
      (letI := os i
       letI : Preorder (inside B (S i)) := (os i).toPreorder
       ((ts i).predecessor ⟨p, hi⟩).cocone.ι.app ⟨⟨z, hzi⟩, hzp_i⟩) ≍
      (letI := os j
       letI : Preorder (inside B (S j)) := (os j).toPreorder
       ((ts j).predecessor ⟨p, hj⟩).cocone.ι.app ⟨⟨z, hzj⟩, hzp_j⟩) := by
  dsimp only
  intro hzp_i hzp_j
  exact (hPreserves i j hij).predecessorLegs ⟨p.1, hi⟩ ⟨z.1, hzi⟩ hzp_i hzp_j

include hPreserves in
/-- Every original cell-source attaching map is retained on the inside labels. -/
theorem insideAttaching (i j : I) (hij : i ≤ j) (p : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    (letI := os i; (ts i).attaching ⟨p, hi⟩) ≍
      (letI := os j; (ts j).attaching ⟨p, hj⟩) :=
  (hPreserves i j hij).attaching ⟨p.1, hi⟩

include hPreserves in
/-- Every original cell-target map is retained on the inside labels. -/
theorem insideCells (i j : I) (hij : i ≤ j) (p : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    (letI := os i; (ts i).cell ⟨p, hi⟩) ≍
      (letI := os j; (ts j).cell ⟨p, hj⟩) :=
  (hPreserves i j hij).cells ⟨p.1, hi⟩

omit [Preorder I] in
/-- The original attaching labels agree on every full overlap. -/
theorem insideLabels (i j : I) (p : B)
    (hi : p ∈ inside B (S i)) (hj : p ∈ inside B (S j)) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    (letI := os i; (ts i).label ⟨p, hi⟩) =
      (letI := os j; (ts j).label ⟨p, hj⟩) :=
  ((F i).labels ⟨p.1, hi⟩).trans ((F j).labels ⟨p.1, hj⟩).symm

omit [Preorder I] in
/-- The genuine original cell and predecessor bounds survive the actual label transport. -/
theorem insideGood (i : I) :
    let os := insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    let ts := insideTree (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F)
    letI := os i
    (ts i).IsGood chi :=
  @CellTreeOrderReindex.tree_good C cCategory (S i) (inside B (S i)) (F i).ord
    (insideOrders (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i) A s X
    (insideOrderIso (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i) (F i).tree
    chi (inferInstance : Fact chi.IsRegular) (F i).good

variable [HasColimitsOfSize.{w, w} C] [Nonempty I]
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hCover : ∀ p : B, ∃ i : I, p.1 ∈ S i)

-- Build the genuine BEFORE prefix while retaining original P and its original chosen M points.
/-- Compatible complete prefixes construct the actual good prefix on a proper original union. -/
def partialLimitPrefix : Prefix O M chi B := by
  let oldOrder : PartialOrder B := inferInstance
  let si := fun i : I => inside B (S i)
  let os := insideOrders (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let ts := insideTree (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let hM := insideMono (B := B) (S := S) (hMono := hMono)
  let hr := insideRestrict (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hi := insideInitial (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hb := insideBelow (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let ho := insideObjects (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hm := insideMaps (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hLabels := fun (i j : I) (_ : i ≤ j) =>
    insideLabels (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i j
  let hPoints := insidePoints (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hLegs := insideLegs (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hAt := insideAttaching (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hCells := insideCells (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hGood := insideGood (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let hf := originalFullOverlap_of_ordered (P := B) (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts hLabels hPoints hLegs hAt hCells
  let ls := InitialOrderFamilyGlue.lower (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let gs := InitialOrderCellTreeReindex.tree (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts
  let hObj := InitialOrderCellTreeCompatibility.objects_overlap (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts ho
  let hMap := InitialOrderCellTreeCompatibility.maps_overlap (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts hm
  let Y := @CellTree.diagram C cCategory P pOrder A s X O
  let originalLabels := fun i : I => (F i).labels
  let originalDiagrams := fun i : I =>
    @CellTree.diagram C cCategory (S i) (F i).ord A s X (F i).tree
  let originalComparisons := fun i : I => (F i).comparison
  let originalMaps := fun i : I => prefixLabels (S i) (F i).ord (F i).below
  let originalLowerUP := fun i : I => (F i).lowerUP
  let newOrder := InitialOrderFamilyGlue.order (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let stagesOrder := InitialOrderFamilyGlue.restrictedOrder (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let e := fun i : I => @OrderIso.trans (ls i) (si i) (S i)
    (stagesOrder i).toLE (os i).toLE (F i).ord.toLE
    (InitialOrderFamilyGlue.stageIso (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover i)
    (insideOrderIso (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i)
  let fs := fun i : I => @CellTree.diagram C cCategory (ls i) (stagesOrder i) A s X (gs i)
  let f : @OrderHom B P newOrder.toPreorder pOrder.toPreorder :=
    @OrderHom.mk B P newOrder.toPreorder pOrder.toPreorder Subtype.val (by
      intro a b h
      exact @CellOrderDirectedUnion.unionLe_below B I oldOrder
        (InitialOrderFamilyGlue.rel (pOrder := oldOrder) si os)
        (InitialOrderFamilyGlue.rel_below (pOrder := oldOrder) si os hb) a b h)
  let bs := fun i : I => @OrderIsoLowerColimitTransport.comparison
    (ls i) (S i) P (stagesOrder i) (F i).ord pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X))
    (e i) (originalMaps i) (originalDiagrams i) Y (originalComparisons i)
  letI := newOrder
  have hBeta : ∀ (i j : I) (p : B) (hip : p ∈ ls i) (hjp : p ∈ ls j),
      (letI : Preorder (ls i) := (stagesOrder i).toPreorder; (bs i).app ⟨p, hip⟩) ≍
      (letI : Preorder (ls j) := (stagesOrder j).toPreorder; (bs j).app ⟨p, hjp⟩) := by
    intro i j p hip hjp
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact ((hPreserves i k hik).comparisons ⟨p.1, hip⟩).trans
      ((hPreserves j k hjk).comparisons ⟨p.1, hjp⟩).symm
  let Q : @CellTree C cCategory B newOrder A s X :=
    OriginalInitialFamilyCellTree.tree (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf
  let beta := @InitialFunctorComparisonGlue.comparison B I P newOrder pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X))
    ls fs hCover hObj hMap f Y bs hBeta
  refine @Prefix.mk P pOrder C cCategory A s X O M chi
    (inferInstance : Fact chi.IsRegular) B newOrder
    (fun a b h => @OrderHom.monotone' B P newOrder.toPreorder pOrder.toPreorder f a b h)
    Q ?_ beta ?_ ?_
  · intro p
    obtain ⟨i, hp⟩ := hCover p
    have ht := OriginalInitialFamilyCellTree.tree_stage_data (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i p hp
    exact ht.1.trans (originalLabels i ⟨p.1, hp⟩)
  · exact OriginalInitialFamilyCellTree.tree_good (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf chi hGood
  · intro D hD
    let ds := OriginalLowerStagePieces.pieces S hMono D
    have hUnion : FilteredOriginalLowerColimit.union ds = D := by
      ext p
      change p ∈ (⨆ i : I, D ⊓ S i) ↔ p ∈ D
      rw [LowerSet.mem_iSup_iff]
      constructor
      · rintro ⟨i, hp⟩
        exact hp.1
      · intro hp
        obtain ⟨i, hi⟩ := hCover ⟨p, hD hp⟩
        exact ⟨i, hp, hi⟩
    let hc := fun (i : I) (p : B) (hp : f p ∈ ds.obj i) => hp.2
    let hu := fun i : I => @OrderIsoLowerColimitTransport.isColimit
      (ls i) (S i) P (stagesOrder i) (F i).ord pOrder.toPreorder
      (Under X) (inferInstance : Category.{v} (Under X))
      (e i) (originalMaps i) (originalDiagrams i) Y (originalComparisons i) M (ds.obj i)
      (originalLowerUP i (ds.obj i) inf_le_right)
    let _ : IsDirectedOrder I := ⟨hDirected⟩
    have hUP := @InitialComparisonFilteredLowerColimit.isColimit B I P newOrder
      (inferInstance : Category.{w} I) (inferInstance : IsFiltered I) pOrder.toPreorder
      (Under X) (inferInstance : Category.{v} (Under X))
      ls fs hCover hObj hMap f Y bs hBeta M ds hc hu
    rw [hUnion] at hUP
    exact hUP

/-- The proper-carrier union retains all nine actual original preservation fields. -/
theorem partialLimitPrefix_preserves (i : I) :
    Preserves O M chi (hInto i) (F i)
      (partialLimitPrefix O M chi B S hInto hMono F hPreserves hDirected hCover) := by
  let oldOrder : PartialOrder B := inferInstance
  let si := fun i : I => inside B (S i)
  let os := insideOrders (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let ts := insideTree (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let hM := insideMono (B := B) (S := S) (hMono := hMono)
  let hr := insideRestrict (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hi := insideInitial (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hb := insideBelow (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let ho := insideObjects (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hm := insideMaps (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hLabels := fun (i j : I) (_ : i ≤ j) =>
    insideLabels (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i j
  let hPoints := insidePoints (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hLegs := insideLegs (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hAt := insideAttaching (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hCells := insideCells (O := O) (M := M) (chi := chi)
    (B := B) (S := S) (hInto := hInto) (F := F)
    (hMono := hMono) (hPreserves := hPreserves)
  let hGood := insideGood (O := O) (M := M) (chi := chi) (B := B) (S := S) (hInto := hInto) (F := F)
  let hf := originalFullOverlap_of_ordered (P := B) (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts hLabels hPoints hLegs hAt hCells
  let ls := InitialOrderFamilyGlue.lower (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let gs := InitialOrderCellTreeReindex.tree (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts
  let hObj := InitialOrderCellTreeCompatibility.objects_overlap (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts ho
  let hMap := InitialOrderCellTreeCompatibility.maps_overlap (pOrder := oldOrder)
    si os hDirected hM hr hi hb hCover ts hm
  let Y := @CellTree.diagram C cCategory P pOrder A s X O
  let originalLabels := fun i : I => (F i).labels
  let originalDiagrams := fun i : I =>
    @CellTree.diagram C cCategory (S i) (F i).ord A s X (F i).tree
  let originalComparisons := fun i : I => (F i).comparison
  let originalMaps := fun i : I => prefixLabels (S i) (F i).ord (F i).below
  let originalLowerUP := fun i : I => (F i).lowerUP
  let oldLower := fun i : I => (S i).lower'
  let newOrder := InitialOrderFamilyGlue.order (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let stagesOrder := InitialOrderFamilyGlue.restrictedOrder (pOrder := oldOrder)
    si os hDirected hM hr hb hCover
  let e := fun i : I => @OrderIso.trans (ls i) (si i) (S i)
    (stagesOrder i).toLE (os i).toLE (F i).ord.toLE
    (InitialOrderFamilyGlue.stageIso (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover i)
    (insideOrderIso (O := O) (M := M) (chi := chi)
      (B := B) (S := S) (hInto := hInto) (F := F) i)
  let fs := fun i : I => @CellTree.diagram C cCategory (ls i) (stagesOrder i) A s X (gs i)
  let f : @OrderHom B P newOrder.toPreorder pOrder.toPreorder :=
    @OrderHom.mk B P newOrder.toPreorder pOrder.toPreorder Subtype.val (by
      intro a b h
      exact @CellOrderDirectedUnion.unionLe_below B I oldOrder
        (InitialOrderFamilyGlue.rel (pOrder := oldOrder) si os)
        (InitialOrderFamilyGlue.rel_below (pOrder := oldOrder) si os hb) a b h)
  let bs := fun i : I => @OrderIsoLowerColimitTransport.comparison
    (ls i) (S i) P (stagesOrder i) (F i).ord pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X))
    (e i) (originalMaps i) (originalDiagrams i) Y (originalComparisons i)
  let _ := newOrder
  have hBeta : ∀ (i j : I) (p : B) (hip : p ∈ ls i) (hjp : p ∈ ls j),
      (letI : Preorder (ls i) := (stagesOrder i).toPreorder; (bs i).app ⟨p, hip⟩) ≍
      (letI : Preorder (ls j) := (stagesOrder j).toPreorder; (bs j).app ⟨p, hjp⟩) := by
    intro i j p hip hjp
    obtain ⟨k, hik, hjk⟩ := hDirected i j
    exact ((hPreserves i k hik).comparisons ⟨p.1, hip⟩).trans
      ((hPreserves j k hjk).comparisons ⟨p.1, hjp⟩).symm
  let Q : @CellTree C cCategory B newOrder A s X :=
    OriginalInitialFamilyCellTree.tree (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf
  let beta := @InitialFunctorComparisonGlue.comparison B I P newOrder pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X))
    ls fs hCover hObj hMap f Y bs hBeta
  refine @Preserves.mk P pOrder C cCategory A s X O M chi
    (inferInstance : Fact chi.IsRegular) (S i) B (hInto i) (F i)
    (partialLimitPrefix O M chi B S hInto hMono F hPreserves hDirected hCover)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a a'
    exact (InitialOrderFamilyGlue.le_at_stage (pOrder := oldOrder)
      si os hDirected hM hr hi i ⟨a.1, hInto i a.2⟩ ⟨a'.1, hInto i a'.2⟩ a.2 a'.2).symm
  · intro a a' ha' haa'
    have hOrig := @OrderHom.monotone' B P newOrder.toPreorder pOrder.toPreorder f a a' haa'
    exact oldLower i hOrig ha'
  · intro a
    let _ : Preorder (ls i) := (stagesOrder i).toPreorder
    have hd := OriginalInitialFamilyCellTree.tree_stage_diagram (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i
    exact (Functor.congr_obj hd
      (⟨⟨a.1, hInto i a.2⟩, a.2⟩ : ls i)).symm
  · intro a a' haa'
    let _ : Preorder (ls i) := (stagesOrder i).toPreorder
    have hd := OriginalInitialFamilyCellTree.tree_stage_diagram (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i
    have hGlobal := (InitialOrderFamilyGlue.le_at_stage (pOrder := oldOrder)
      si os hDirected hM hr hi i ⟨a.1, hInto i a.2⟩ ⟨a'.1, hInto i a'.2⟩ a.2 a'.2).2 haa'
    exact (Functor.hcongr_hom hd
      (homOfLE hGlobal : (⟨⟨a.1, hInto i a.2⟩, a.2⟩ : ls i) ⟶
        ⟨⟨a'.1, hInto i a'.2⟩, a'.2⟩)).symm
  · intro a
    exact (OriginalInitialFamilyCellTree.tree_stage_data (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i ⟨a.1, hInto i a.2⟩ a.2).2.1.symm
  · intro a z hza hza'
    exact (OriginalInitialFamilyCellTree.tree_stage_predecessor_leg (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i ⟨a.1, hInto i a.2⟩ a.2
        ⟨⟨z.1, hInto i z.2⟩, hza'⟩).symm
  · intro a
    exact (OriginalInitialFamilyCellTree.tree_stage_data (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i ⟨a.1, hInto i a.2⟩ a.2).2.2.1.symm
  · intro a
    exact (OriginalInitialFamilyCellTree.tree_stage_data (pOrder := oldOrder)
      si os hDirected hM hr hi hb hCover ts ho hm hf i ⟨a.1, hInto i a.2⟩ a.2).2.2.2.symm
  · intro a
    exact (@InitialFunctorComparisonGlue.component_heq B I P newOrder pOrder.toPreorder
      (Under X) (inferInstance : Category.{v} (Under X))
      ls fs hCover hObj f Y bs hBeta i ⟨a.1, hInto i a.2⟩ a.2).symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {I : Type w} [Preorder I] (B : LowerSet P)
  (S : I → LowerSet P) (hInto : ∀ i : I, S i ≤ B) (hMono : Monotone S)
  (F : ∀ i : I, Prefix O M chi (S i))
  (hPreserves : ∀ (i j : I) (hij : i ≤ j),
    Preserves O M chi (hMono hij) (F i) (F j))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hCover : ∀ p : B, ∃ i : I, p.1 ∈ S i)

/-- For a fixed cell tree `O`, chosen lower-set colimits `M`, regular `chi`
and working-size colimits in `C`, assemble a prefix on `B` from a coherent
family of prefixes on a monotone family of lower sets covering `B`.

The inputs are `S : I → LowerSet P`, monotone with `S i ≤ B`; a prefix `F i`
on each `S i`; `Preserves` of the actual prefix fields from `F i` to `F j`
for every `i ≤ j`; a common upper stage for each pair `i`, `j`;
and, for every `p : B`, some `i` with `p ∈ S i`. If `I` is empty that cover
forces `B = ⊥`, and the designated empty prefix is returned; otherwise the
assembly is `partialLimitPrefix`, which retains every `F i`
(`unionPrefix_preserves`). The family is a cover by lower sets of `B`, not an
arbitrary one; the `F i` are prefixes of the same goodification data, not
independent ones; and directedness is the pairwise upper stage required
here. -/
def unionPrefix : Prefix O M chi B := by
  classical
  by_cases hI : Nonempty I
  · let _ := hI
    exact partialLimitPrefix O M chi B S hInto hMono F hPreserves hDirected hCover
  · have hB : B = ⊥ := by
      apply le_antisymm
      · intro p hp
        obtain ⟨i, _⟩ := hCover ⟨p, hp⟩
        exact False.elim (hI ⟨i⟩)
      · exact bot_le
    subst B
    exact emptyPrefix O M chi

/-- Every actual old prefix is retained by the complete union producer, with all original fields. -/
theorem unionPrefix_preserves (i : I) :
    Preserves O M chi (hInto i) (F i)
      (unionPrefix O M chi B S hInto hMono F hPreserves hDirected hCover) := by
  classical
  have hI : Nonempty I := ⟨i⟩
  unfold unionPrefix
  rw [dite_eq_left hI]
  exact partialLimitPrefix_preserves O M chi B S hInto hMono F hPreserves hDirected hCover i

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {I : Type w} [Preorder I]
  (S : I → LowerSet P) (hMono : Monotone S)
  (F : ∀ i : I, Prefix O M chi (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hPreserves : ∀ (i j : I) (hij : i ≤ j),
    Preserves O M chi (hMono hij) (F i) (F j))

/-- For the same fixed cell tree `O`, lower-set colimits `M`, regular `chi`
and working-size colimits in `C`, the whole-carrier prefix is the `B = ⊤`
case of `unionPrefix`.

It takes the same monotone family `S`, prefixes `F i`, pairwise upper stages
and preservation along transitions, and requires the cover to reach every
`p : P` rather than only the members of a proper lower set. It retains every
`F i` (`limitPrefix_preserves`). If the stage index is empty, this coverage
forces `P` to be empty and the bottom-case prefix applies. -/
def limitPrefix : Prefix O M chi (⊤ : LowerSet P) :=
  unionPrefix O M chi ⊤ S (fun _ => le_top) hMono F hPreserves hDirected
    (fun p => hCover p.1)

/-- The whole-original-carrier limit retains every complete prior original prefix. -/
theorem limitPrefix_preserves (i : I) :
    Preserves O M chi (le_top : S i ≤ ⊤) (F i)
      (limitPrefix O M chi S hMono F hDirected hCover hPreserves) :=
  unionPrefix_preserves O M chi ⊤ S (fun _ => le_top) hMono F hPreserves hDirected
    (fun p => hCover p.1) i

end

end CategoryTheory.SmallObject.OriginalGoodification
