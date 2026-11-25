/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
public import MathlibExt.AlgebraicGeometry.WaldhausenExactFlags

/-!
# The actual full infinity-categorical S-construction

The level consists of coherent functors from the actual interval-arrow
category, with zero diagonals and the actual universal cofiber squares.
The full enhanced subcategory retains every natural transformation.
The equivalence-edge core is taken only after this full level is formed.

All ordinal restriction maps are native interval-arrow functors. This
module also fixes the coordinate square functors used in the iterated
construction; source model and spectrum comparison proofs are separate.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4,
Definition 7.1, Definition 7.5 and Section 7.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinitySConstruction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
open QuasicategoricalModels StableInfinityMappingSpaces StableInfinityFiniteDiagrams
open StableInfinityCategoryModels
open scoped Simplicial

universe u

/-- The actual arrow category on the finite ordered interval. -/
abbrev IntervalCategory (n : ℕ) := Arrow (Fin (n + 1))

/-- The monotone two-value coordinate used for each direction of a cofiber square. -/
def twoValue {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Fin 2 →o Fin (n + 1) where
  toFun a := if a = 0 then i else j
  monotone' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- The lower interval coordinate is the second walking-square coordinate. -/
def lowerIndex {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : SquareCorner →o Fin (n + 1) where
  toFun p := twoValue i j h p.coordinate.2
  monotone' := fun _ _ hxy => (twoValue i j h).monotone hxy.2

/-- The upper interval coordinate is the first walking-square coordinate. -/
def upperIndex {n : ℕ} (j k : Fin (n + 1)) (h : j ≤ k) : SquareCorner →o Fin (n + 1) where
  toFun p := twoValue j k h p.coordinate.1
  monotone' := fun _ _ hxy => (twoValue j k h).monotone hxy.1

/-- The literal cofiber square at i≤j≤k, including all four interval objects and arrows. -/
def gapSquareIndex {n : ℕ} (i j k : Fin (n + 1)) (h : i ≤ j) (h' : j ≤ k) :
    SquareCorner ⥤ IntervalCategory n where
  obj p := interval (lowerIndex i j h p) (upperIndex j k h' p) (by
    cases p
    · simpa [lowerIndex, upperIndex, twoValue, SquareCorner.coordinate] using h
    · simpa [lowerIndex, upperIndex, twoValue, SquareCorner.coordinate] using h.trans h'
    · simp [lowerIndex, upperIndex, twoValue, SquareCorner.coordinate]
    · simpa [lowerIndex, upperIndex, twoValue, SquareCorner.coordinate] using h')
  map {p q} f := Arrow.homMk
    (homOfLE ((lowerIndex i j h).monotone (leOfHom f)))
    (homOfLE ((upperIndex j k h').monotone (leOfHom f)))
  map_id p := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The source's particular cofiber square in the actual coherent diagram. -/
def gapSquare {C : StableInfinityCategory.{u}} {n : ℕ}
    (d : indexNerve (IntervalCategory n) ⟶ C.toSSet)
    (i j k : Fin (n + 1)) (h : i ≤ j) (h' : j ≤ k) : indexNerve SquareCorner ⟶ C.toSSet :=
  indexMap (gapSquareIndex i j k h h') ≫ d

/-- The actual source conditions on a coherent interval diagram. -/
def IsGapDiagram (C : StableInfinityCategory.{u}) (n : ℕ)
    (d : indexNerve (IntervalCategory n) ⟶ C.toSSet) : Prop :=
  (∀ i : Fin (n + 1), IsZeroObject C.toSSet
    (d.app (op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ (interval i i le_rfl))))) ∧
  ∀ (i j k : Fin (n + 1)) (h : i ≤ j) (h' : j ≤ k),
    IsPushoutSquare (gapSquare d i j k h h')

/-- The predicate is evaluated on the native enriched Hom zero-simplex. -/
def IsGapVertex (C : StableInfinityCategory.{u}) (n : ℕ)
    (a : (mapping (indexNerve (IntervalCategory n)) C.toSSet) _⦋0⦌) : Prop :=
  IsGapDiagram C n ((mappingZero (indexNerve (IntervalCategory n)) C.toSSet).symm a)

/-- The actual full S_n infinity category. -/
def gapCategory (C : StableInfinityCategory.{u}) (n : ℕ) : SSet.{u} :=
  ((mapping (indexNerve (IntervalCategory n)) C.toSSet).fullEnhancedSubcategory
    (IsGapVertex C n)).toSSet

/-- Its maximal core keeps every interval object and exactly the equivalence-edge transformations. -/
def gapCore (C : StableInfinityCategory.{u}) (n : ℕ) : SSet.{u} := core (gapCategory C n)

/-- Ordinal restriction is the actual native arrow functor of the monotone map. -/
def intervalRestriction {m n : ℕ} (a : Fin (m + 1) →o Fin (n + 1)) :
    IntervalCategory m ⥤ IntervalCategory n := (orderFunctor a).mapArrow

/-- Its full coherent-diagram map is the native precomposition map. -/
def diagramRestriction {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) :
    mapping (indexNerve (IntervalCategory n)) C.toSSet ⟶
      mapping (indexNerve (IntervalCategory m)) C.toSSet :=
  precomposition (indexMap (intervalRestriction a)) C.toSSet

/-- The coordinate square commutes literally with ordinal restriction. -/
theorem gapSquareIndex_restriction {m n : ℕ} (a : Fin (m + 1) →o Fin (n + 1))
    (i j k : Fin (m + 1)) (h : i ≤ j) (h' : j ≤ k) :
    gapSquareIndex i j k h h' ⋙ intervalRestriction a =
      gapSquareIndex (a i) (a j) (a k) (a.monotone h) (a.monotone h') := by
  exact _root_.CategoryTheory.Functor.ext (h_obj := fun p => by cases p <;> rfl)

/-- Restriction of the source's coherent interval diagram. -/
def restrictedDiagram {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1))
    (d : indexNerve (IntervalCategory n) ⟶ C.toSSet) :
    indexNerve (IntervalCategory m) ⟶ C.toSSet := indexMap (intervalRestriction a) ≫ d

/-- Native ordinal reindexing preserves the actual zero and cofiber square conditions. -/
theorem restrictedDiagram_isGap {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1))
    (d : indexNerve (IntervalCategory n) ⟶ C.toSSet) (hd : IsGapDiagram C n d) :
    IsGapDiagram C m (restrictedDiagram a d) := by
  constructor
  · intro i
    exact hd.1 (a i)
  · intro i j k h h'
    have hx := hd.2 (a i) (a j) (a k) (a.monotone h) (a.monotone h')
    have he := gapSquareIndex_restriction a i j k h h'
    dsimp only [gapSquare] at hx
    rw [← he, indexMap_comp] at hx
    simpa only [gapSquare, restrictedDiagram, Category.assoc] using hx

/-- Restrict a map to genuine full enhanced subcategories using its vertex preservation proof. -/
def fullMap {X Y : SSet.{u}} (f : X ⟶ Y) (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (h : ∀ x : X _⦋0⦌, P x → Q (f.app (op ⦋0⦌) x)) :
    (X.fullEnhancedSubcategory P).toSSet ⟶ (Y.fullEnhancedSubcategory Q).toSSet :=
  SSet.Subcomplex.lift ((X.fullEnhancedSubcategory P).ι ≫ f) (by
    rw [SSet.range_le_fullEnhancedSubcategory_iff]
    intro x
    exact h x.val ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff P x.val).mp x.property))

/-- Every actual ordinal restriction preserves the native S-level vertices. -/
theorem diagramRestriction_isGap {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1))
    (x : (mapping (indexNerve (IntervalCategory n)) C.toSSet) _⦋0⦌)
    (hx : IsGapVertex C n x) :
    IsGapVertex C m ((diagramRestriction a).app (op ⦋0⦌) x) := by
  let d := (mappingZero (indexNerve (IntervalCategory n)) C.toSSet).symm x
  have he := (mappingZero (indexNerve (IntervalCategory n)) C.toSSet).apply_symm_apply x
  rw [← he]
  dsimp only [diagramRestriction]
  rw [mappingZero_precomposition]
  simpa only [IsGapVertex, Equiv.symm_apply_apply, restrictedDiagram] using
    restrictedDiagram_isGap a d hx

/-- The actual full S-level restriction map includes every coherent natural transformation. -/
def gapRestriction {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) : gapCategory C n ⟶ gapCategory C m :=
  fullMap (diagramRestriction a) (IsGapVertex C n) (IsGapVertex C m)
    (diagramRestriction_isGap a)

/-- The core map is taken only after the full native restriction has been constructed. -/
def gapCoreRestriction {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) : gapCore C n ⟶ gapCore C m :=
  coreMap (gapRestriction a)

/-- Identity ordinal maps give the actual identity interval functor. -/
theorem intervalRestriction_id (n : ℕ) :
    intervalRestriction (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) = 𝟭 (IntervalCategory n) := by
  rfl

/-- Composite ordinal maps give the actual composite interval-arrow functor. -/
theorem intervalRestriction_comp {l m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) (b : Fin (l + 1) →o Fin (m + 1)) :
    intervalRestriction (a.comp b) = intervalRestriction b ⋙ intervalRestriction a := by
  rfl

/-- Native simplicial Hom precomposition preserves index identities. -/
theorem precomposition_id (X Z : SSet.{u}) : precomposition (𝟙 X) Z = 𝟙 (mapping X Z) := by
  exact congrArg (fun f => f.app Z) ((SimplicialCategory.sHomFunctor SSet).map_id (op X))

/-- Native simplicial Hom precomposition reverses index composition. -/
theorem precomposition_comp {X Y Z W : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    precomposition (f ≫ g) W = precomposition g W ≫ precomposition f W := by
  exact congrArg (fun a => a.app W)
    ((SimplicialCategory.sHomFunctor SSet).map_comp g.op f.op)

/-- The underlying map is the actual full diagram restriction on every simplex. -/
theorem gapRestriction_app_val {C : StableInfinityCategory.{u}} {m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) (k : SimplexCategoryᵒᵖ) (x : (gapCategory C n).obj k) :
    ((gapRestriction a).app k x).val = (diagramRestriction a).app k x.val := rfl

/-- The full S-level maps preserve the actual identity ordinal restriction. -/
theorem gapRestriction_id (C : StableInfinityCategory.{u}) (n : ℕ) :
    gapRestriction (C := C) (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) = 𝟙 (gapCategory C n) := by
  ext k x
  apply Subtype.ext
  change ((gapRestriction (OrderHom.id : Fin (n + 1) →o Fin (n + 1))).app k x).val = x.val
  rw [gapRestriction_app_val]
  dsimp only [diagramRestriction]
  rw [intervalRestriction_id, indexMap_id, precomposition_id]
  rfl

/-- The full S-level maps preserve the actual composite ordinal restrictions. -/
theorem gapRestriction_comp {C : StableInfinityCategory.{u}} {l m n : ℕ}
    (a : Fin (m + 1) →o Fin (n + 1)) (b : Fin (l + 1) →o Fin (m + 1)) :
    gapRestriction (a.comp b) = gapRestriction a ≫ gapRestriction (C := C) b := by
  ext k x
  apply Subtype.ext
  change ((gapRestriction (a.comp b)).app k x).val =
    ((gapRestriction b).app k ((gapRestriction a).app k x)).val
  rw [gapRestriction_app_val, gapRestriction_app_val, gapRestriction_app_val]
  dsimp only [diagramRestriction]
  rw [intervalRestriction_comp, indexMap_comp, precomposition_comp]
  rfl

/-- The maximal-core operation is the actual native functor on simplicial maps. -/
def coreFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := core X
  map f := coreMap f
  map_id X := coreMap_id X
  map_comp f g := coreMap_comp f g

/-- The actual full simplicial infinity category S_infinity(C). -/
def sConstruction (C : StableInfinityCategory.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := gapCategory C n.unop.len
  map a := gapRestriction a.unop.toOrderHom
  map_id n := gapRestriction_id C n.unop.len
  map_comp a b := by
    exact gapRestriction_comp a.unop.toOrderHom b.unop.toOrderHom

/-- Its actual simplicial maximal-core space, after full S-level construction. -/
def coreSConstruction (C : StableInfinityCategory.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  sConstruction C ⋙ coreFunctor

/-- The native diagonal of the coherent S-core bisimplicial space. -/
def sDiagonal (C : StableInfinityCategory.{u}) : SSet.{u} where
  obj n := ((coreSConstruction C).obj n).obj n
  map {n m} a := ((coreSConstruction C).map a).app n ≫ ((coreSConstruction C).obj m).map a
  map_id n := by simp only [_root_.CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  map_comp a b := by
    simp only [_root_.CategoryTheory.Functor.map_comp]
    rw [← NatTrans.naturality]
    rfl

/-- The actual spine chain consists of intervals (0,1),...,(0,n). -/
def flagSpine (n : ℕ) : Fin n ⥤ IntervalCategory n where
  obj i := interval 0 i.succ (Fin.zero_le _)
  map {i j} f := Arrow.homMk (𝟙 _) (homOfLE (Fin.succ_le_succ_iff.mpr (leOfHom f)))
  map_id i := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The source Lemma7.3 forgetful map is the actual native spine restriction. -/
def gapSpineRestriction (C : StableInfinityCategory.{u}) (n : ℕ) :
    gapCategory C n ⟶ mapping (indexNerve (Fin n)) C.toSSet :=
  ((mapping (indexNerve (IntervalCategory n)) C.toSSet).fullEnhancedSubcategory
    (IsGapVertex C n)).ι ≫ precomposition (indexMap (flagSpine n)) C.toSSet

end MathlibExt.AlgebraicTopology.StableInfinitySConstruction
