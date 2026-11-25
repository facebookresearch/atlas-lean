/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySConstruction
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# The literal iterated S-construction on products of interval-arrow categories

The source category is the actual finite product Ar[n_1] times ... times
Ar[n_q]. The full enhanced subcategory has a zero object on every
coordinate diagonal and every original coordinate cofiber square.
Ordinal maps act by the native product of interval-arrow functors.
All higher natural transformations are retained before the core.

For q=0 this is the full functor category on the empty product index,
with its canonical evaluation comparison to C. The comparison and the
one-skeleton spectrum structure maps are kept separate from K0 and
corepresentability conclusions.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Definition 7.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
open QuasicategoricalModels StableInfinityMappingSpaces StableInfinityFiniteDiagrams
open StableInfinityCategoryModels StableInfinitySConstruction
open scoped Simplicial

universe u

/-- The actual product of the source interval-arrow categories. -/
abbrev MultiIntervalCategory (q : ℕ) (n : Fin q → ℕ) := ∀ i : Fin q, IntervalCategory (n i)

/-- This coordinate square changes exactly the original r-th interval factor. -/
def coordinateSquare {q : ℕ} {n : Fin q → ℕ} (p : MultiIntervalCategory q n) (r : Fin q)
    (k : Fin (n r + 1)) (h : (p r).right ≤ k) : SquareCorner ⥤ MultiIntervalCategory q n :=
  _root_.CategoryTheory.Functor.pi'
    (Function.update (fun i : Fin q => (_root_.CategoryTheory.Functor.const SquareCorner).obj (p i)) r
      (gapSquareIndex (p r).left (p r).right k (leOfHom (p r).hom) h))

/-- The full multi-gap source condition, with every coordinate and every cofiber test. -/
def IsMultiGapDiagram (C : StableInfinityCategory.{u}) (q : ℕ) (n : Fin q → ℕ)
    (d : indexNerve (MultiIntervalCategory q n) ⟶ C.toSSet) : Prop :=
  (∀ (p : MultiIntervalCategory q n) (r : Fin q), (p r).left = (p r).right →
    IsZeroObject C.toSSet (d.app (op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ p)))) ∧
  ∀ (p : MultiIntervalCategory q n) (r : Fin q) (k : Fin (n r + 1)) (h : (p r).right ≤ k),
    IsPushoutSquare (indexMap (coordinateSquare p r k h) ≫ d)

/-- The native enriched Hom zero-simplex gives the actual whole multi-interval diagram. -/
def IsMultiGapVertex (C : StableInfinityCategory.{u}) (q : ℕ) (n : Fin q → ℕ)
    (a : (mapping (indexNerve (MultiIntervalCategory q n)) C.toSSet) _⦋0⦌) : Prop :=
  IsMultiGapDiagram C q n ((mappingZero (indexNerve (MultiIntervalCategory q n)) C.toSSet).symm a)

/-- The actual full q-fold S-level, with all coherent diagram morphisms. -/
def multiGapCategory (C : StableInfinityCategory.{u}) (q : ℕ) (n : Fin q → ℕ) : SSet.{u} :=
  ((mapping (indexNerve (MultiIntervalCategory q n)) C.toSSet).fullEnhancedSubcategory
    (IsMultiGapVertex C q n)).toSSet

/-- Apply the maximal equivalence-edge core only after the full q-fold S-level. -/
def multiGapCore (C : StableInfinityCategory.{u}) (q : ℕ) (n : Fin q → ℕ) : SSet.{u} :=
  core (multiGapCategory C q n)

/-- Every coordinate ordinal acts by its actual native interval-arrow functor. -/
def multiIntervalRestriction {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    MultiIntervalCategory q m ⥤ MultiIntervalCategory q n :=
  _root_.CategoryTheory.Functor.pi (fun i => intervalRestriction (a i))

/-- The coordinate square commutes with the actual product restriction functor. -/
theorem coordinateSquare_restriction {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1))
    (p : MultiIntervalCategory q m) (r : Fin q) (k : Fin (m r + 1)) (h : (p r).right ≤ k) :
    coordinateSquare p r k h ⋙ multiIntervalRestriction a =
      coordinateSquare ((multiIntervalRestriction a).obj p) r (a r k) ((a r).monotone h) := by
  apply _root_.CategoryTheory.Functor.ext (h_obj := ?_)
  intro c
  funext i
  by_cases hi : i = r
  · subst i
    have he := gapSquareIndex_restriction (a r) (p r).left (p r).right k
      (leOfHom (p r).hom) h
    simpa [coordinateSquare, multiIntervalRestriction, intervalRestriction, orderFunctor] using
      congrArg (fun F => F.obj c) he
  · simp [coordinateSquare, multiIntervalRestriction, Function.update_of_ne hi]

/-- The whole source diagram is restricted by its actual native product index map. -/
def restrictedMultiDiagram {C : StableInfinityCategory.{u}} {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1))
    (d : indexNerve (MultiIntervalCategory q n) ⟶ C.toSSet) :
    indexNerve (MultiIntervalCategory q m) ⟶ C.toSSet := indexMap (multiIntervalRestriction a) ≫ d

/-- Actual coordinate ordinal restriction preserves all source diagonal and cofiber tests. -/
theorem restrictedMultiDiagram_isGap {C : StableInfinityCategory.{u}} {q : ℕ}
    {m n : Fin q → ℕ} (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1))
    (d : indexNerve (MultiIntervalCategory q n) ⟶ C.toSSet) (hd : IsMultiGapDiagram C q n d) :
    IsMultiGapDiagram C q m (restrictedMultiDiagram a d) := by
  constructor
  · intro p r h
    exact hd.1 ((multiIntervalRestriction a).obj p) r (congrArg (a r) h)
  · intro p r k h
    have hx := hd.2 ((multiIntervalRestriction a).obj p) r (a r k) ((a r).monotone h)
    rw [← coordinateSquare_restriction, indexMap_comp] at hx
    simpa only [restrictedMultiDiagram, Category.assoc] using hx

/-- The actual full enriched-diagram restriction in all interval coordinates. -/
def multiDiagramRestriction {C : StableInfinityCategory.{u}} {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    mapping (indexNerve (MultiIntervalCategory q n)) C.toSSet ⟶
      mapping (indexNerve (MultiIntervalCategory q m)) C.toSSet :=
  precomposition (indexMap (multiIntervalRestriction a)) C.toSSet

/-- The full q-fold restriction acts on every coherent parameter simplex. -/
def multiGapRestriction {C : StableInfinityCategory.{u}} {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    multiGapCategory C q n ⟶ multiGapCategory C q m :=
  fullMap (multiDiagramRestriction a) (IsMultiGapVertex C q n) (IsMultiGapVertex C q m) (by
    intro x hx
    let d := (mappingZero (indexNerve (MultiIntervalCategory q n)) C.toSSet).symm x
    have he := (mappingZero (indexNerve (MultiIntervalCategory q n)) C.toSSet).apply_symm_apply x
    rw [← he]
    dsimp only [multiDiagramRestriction]
    rw [mappingZero_precomposition]
    simpa only [IsMultiGapVertex, Equiv.symm_apply_apply, restrictedMultiDiagram] using
      restrictedMultiDiagram_isGap a d hx)

/-- The actual q-fold core restriction is induced from that same full diagram map. -/
def multiGapCoreRestriction {C : StableInfinityCategory.{u}} {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    multiGapCore C q n ⟶ multiGapCore C q m := coreMap (multiGapRestriction a)

/-- The underlying q-fold map is the actual native diagram map on every simplex. -/
theorem multiGapRestriction_app_val {C : StableInfinityCategory.{u}} {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) (k : SimplexCategoryᵒᵖ)
    (x : (multiGapCategory C q n).obj k) :
    ((multiGapRestriction a).app k x).val = (multiDiagramRestriction a).app k x.val := rfl

/-- The actual product interval functor preserves identity ordinals. -/
theorem multiIntervalRestriction_id (q : ℕ) (n : Fin q → ℕ) :
    multiIntervalRestriction (fun i => (OrderHom.id : Fin (n i + 1) →o _)) =
      𝟭 (MultiIntervalCategory q n) := by
  rfl

/-- The product interval functor preserves coordinatewise ordinal composition. -/
theorem multiIntervalRestriction_comp {q : ℕ} {l m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1))
    (b : ∀ i : Fin q, Fin (l i + 1) →o Fin (m i + 1)) :
    multiIntervalRestriction (fun i => (a i).comp (b i)) =
      multiIntervalRestriction b ⋙ multiIntervalRestriction a := by
  rfl

/-- The full q-fold S-level identity is the actual identity on every parameter simplex. -/
theorem multiGapRestriction_id (C : StableInfinityCategory.{u}) (q : ℕ) (n : Fin q → ℕ) :
    multiGapRestriction (C := C) (fun i => (OrderHom.id : Fin (n i + 1) →o _)) =
      𝟙 (multiGapCategory C q n) := by
  ext k x
  apply Subtype.ext
  change ((multiGapRestriction (fun i => (OrderHom.id : Fin (n i + 1) →o _))).app k x).val = x.val
  rw [multiGapRestriction_app_val]
  dsimp only [multiDiagramRestriction]
  rw [multiIntervalRestriction_id, indexMap_id, precomposition_id]
  rfl

/-- The full q-fold S-level composition is fixed by all actual ordinal coordinates. -/
theorem multiGapRestriction_comp {C : StableInfinityCategory.{u}} {q : ℕ} {l m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1))
    (b : ∀ i : Fin q, Fin (l i + 1) →o Fin (m i + 1)) :
    multiGapRestriction (fun i => (a i).comp (b i)) =
      multiGapRestriction a ≫ multiGapRestriction (C := C) b := by
  ext k x
  apply Subtype.ext
  change ((multiGapRestriction (fun i => (a i).comp (b i))).app k x).val =
    ((multiGapRestriction b).app k ((multiGapRestriction a).app k x)).val
  rw [multiGapRestriction_app_val, multiGapRestriction_app_val, multiGapRestriction_app_val]
  dsimp only [multiDiagramRestriction]
  rw [multiIntervalRestriction_comp, indexMap_comp, precomposition_comp]
  rfl

/-- The actual multisimplicial full enhanced S-level functor. -/
def multiSConstruction (C : StableInfinityCategory.{u}) (q : ℕ) :
    (Fin q → SimplexCategoryᵒᵖ) ⥤ SSet.{u} where
  obj n := multiGapCategory C q (fun i => (n i).unop.len)
  map a := multiGapRestriction (fun i => (a i).unop.toOrderHom)
  map_id n := multiGapRestriction_id C q (fun i => (n i).unop.len)
  map_comp a b := multiGapRestriction_comp
    (fun i => (a i).unop.toOrderHom) (fun i => (b i).unop.toOrderHom)

/-- The native constant-coordinate functor gives the multisimplicial diagonal index. -/
def diagonalIndex (q : ℕ) : SimplexCategoryᵒᵖ ⥤ (Fin q → SimplexCategoryᵒᵖ) where
  obj n := fun _ => n
  map a := fun _ => a

/-- The actual diagonal q-fold S-core functor, with all native index maps. -/
def diagonalCoreFunctor (C : StableInfinityCategory.{u}) (q : ℕ) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  diagonalIndex q ⋙ multiSConstruction C q ⋙ coreFunctor

/-- The q-fold S-core is the native diagonal in all index and parameter directions. -/
def multiSDiagonal (C : StableInfinityCategory.{u}) (q : ℕ) : SSet.{u} where
  obj n := ((diagonalCoreFunctor C q).obj n).obj n
  map {n m} a := ((diagonalCoreFunctor C q).map a).app n ≫
    ((diagonalCoreFunctor C q).obj m).map a
  map_id n := by simp only [_root_.CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  map_comp a b := by
    simp only [_root_.CategoryTheory.Functor.map_comp]
    rw [← NatTrans.naturality]
    rfl

/-- Equal-level interval coordinates are permuted by the actual finite bijection. -/
def coordinatePermutation (q n : ℕ) (a : Equiv.Perm (Fin q)) :
    MultiIntervalCategory q (fun _ => n) ⥤ MultiIntervalCategory q (fun _ => n) where
  obj p := fun i => p (a i)
  map f := fun i => f (a i)

/-- Equal interval endpoints give the same actual arrow object. -/
theorem interval_eq_of_endpoints {n : ℕ} {i j i' j' : Fin (n + 1)}
    (h : i ≤ j) (h' : i' ≤ j') (hi : i = i') (hj : j = j') : interval i j h = interval i' j' h' := by
  subst i'
  subst j'
  rfl

/-- The actual coordinate permutation preserves the original cofiber square functors. -/
theorem coordinateSquare_permutation (q n : ℕ) (a : Equiv.Perm (Fin q))
    (p : MultiIntervalCategory q (fun _ => n)) (r : Fin q)
    (k : Fin (n + 1)) (h : (p r).right ≤ k) :
    coordinateSquare p r k h ⋙ coordinatePermutation q n a =
      coordinateSquare ((coordinatePermutation q n a).obj p) (a.symm r) k (by
        change (p (a (a.symm r))).right ≤ k
        rw [_root_.Equiv.apply_symm_apply]
        exact h) := by
  apply _root_.CategoryTheory.Functor.ext (h_obj := ?_)
  intro c
  funext i
  by_cases hi : a i = r
  · have hx : i = a.symm r := by simpa using congrArg a.symm hi
    subst i
    have hp := congrArg p hi
    cases c
    · simp only [coordinateSquare, coordinatePermutation, _root_.CategoryTheory.Functor.comp_obj,
        _root_.CategoryTheory.Functor.pi'_obj, Function.update_apply, Function.update_self, hi, gapSquareIndex,
        lowerIndex, upperIndex, twoValue, SquareCorner.coordinate, ite_eq_left, ite_eq_right]
      exact interval_eq_of_endpoints _ _ (congrArg Arrow.left hp.symm) (congrArg Arrow.right hp.symm)
    · simp only [coordinateSquare, coordinatePermutation, _root_.CategoryTheory.Functor.comp_obj,
        _root_.CategoryTheory.Functor.pi'_obj, Function.update_apply, Function.update_self, hi, gapSquareIndex,
        lowerIndex, upperIndex, twoValue, SquareCorner.coordinate, ite_eq_left, ite_eq_right]
      exact interval_eq_of_endpoints _ _ (congrArg Arrow.left hp.symm) rfl
    · simp only [coordinateSquare, coordinatePermutation, _root_.CategoryTheory.Functor.comp_obj,
        _root_.CategoryTheory.Functor.pi'_obj, Function.update_apply, Function.update_self, hi, gapSquareIndex,
        lowerIndex, upperIndex, twoValue, SquareCorner.coordinate, ite_eq_left, ite_eq_right]
      exact interval_eq_of_endpoints _ _ (congrArg Arrow.right hp.symm) (congrArg Arrow.right hp.symm)
    · simp only [coordinateSquare, coordinatePermutation, _root_.CategoryTheory.Functor.comp_obj,
        _root_.CategoryTheory.Functor.pi'_obj, Function.update_apply, Function.update_self, hi, gapSquareIndex,
        lowerIndex, upperIndex, twoValue, SquareCorner.coordinate, ite_eq_left, ite_eq_right]
      exact interval_eq_of_endpoints _ _ (congrArg Arrow.right hp.symm) rfl
  · have hx : i ≠ a.symm r := by
      intro he
      apply hi
      simp only [he, _root_.Equiv.apply_symm_apply]
    simp [coordinateSquare, coordinatePermutation, Function.update_of_ne hi, Function.update_of_ne hx]

/-- The whole native coordinate permutation acts on actual full multi-gap diagrams. -/
def permutedDiagram {C : StableInfinityCategory.{u}} (q n : ℕ) (a : Equiv.Perm (Fin q))
    (d : indexNerve (MultiIntervalCategory q (fun _ => n)) ⟶ C.toSSet) :
    indexNerve (MultiIntervalCategory q (fun _ => n)) ⟶ C.toSSet :=
  indexMap (coordinatePermutation q n a) ≫ d

/-- Every coordinate permutation preserves every source diagonal and cofiber condition. -/
theorem permutedDiagram_isGap {C : StableInfinityCategory.{u}} (q n : ℕ)
    (a : Equiv.Perm (Fin q))
    (d : indexNerve (MultiIntervalCategory q (fun _ => n)) ⟶ C.toSSet)
    (hd : IsMultiGapDiagram C q (fun _ => n) d) :
    IsMultiGapDiagram C q (fun _ => n) (permutedDiagram q n a d) := by
  constructor
  · intro p r h
    exact hd.1 ((coordinatePermutation q n a).obj p) (a.symm r) (by
        change (p (a (a.symm r))).left = (p (a (a.symm r))).right
        rw [_root_.Equiv.apply_symm_apply]
        exact h)
  · intro p r k h
    have hx := hd.2 ((coordinatePermutation q n a).obj p) (a.symm r) k (by
        change (p (a (a.symm r))).right ≤ k
        rw [_root_.Equiv.apply_symm_apply]
        exact h)
    rw [← coordinateSquare_permutation, indexMap_comp] at hx
    simpa only [permutedDiagram, Category.assoc] using hx

/-- The full permutation map is actual precomposition on all coherent parameter simplices. -/
def multiPermutationMap {C : StableInfinityCategory.{u}} (q n : ℕ) (a : Equiv.Perm (Fin q)) :
    multiGapCategory C q (fun _ => n) ⟶ multiGapCategory C q (fun _ => n) :=
  fullMap (precomposition (indexMap (coordinatePermutation q n a)) C.toSSet)
    (IsMultiGapVertex C q (fun _ => n)) (IsMultiGapVertex C q (fun _ => n)) (by
      intro x hx
      let d := (mappingZero (indexNerve (MultiIntervalCategory q (fun _ => n))) C.toSSet).symm x
      have he := (mappingZero (indexNerve (MultiIntervalCategory q (fun _ => n))) C.toSSet).apply_symm_apply x
      rw [← he, mappingZero_precomposition]
      simpa only [IsMultiGapVertex, Equiv.symm_apply_apply, permutedDiagram] using
        permutedDiagram_isGap q n a d hx)

end MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction
