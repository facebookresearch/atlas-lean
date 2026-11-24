/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Sigma.Basic

/-!
# The actual tagged right-lifting test

The source elements are original generator tags and original diagonals.
The target elements are those same tags and native Arrow squares. The
test is an actual Arrow functor, and its surjectivity is the original
right lifting property. Working-size normalization retains both complete
functions and every original tag, diagonal and square.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w t uA vA s u v

open CategoryTheory TypeCat

namespace CategoryTheory.MorphismProperty.LiftingTest

section Normalization

variable {A : Type uA} [Category.{vA} A]
  (T : A ⥤ Arrow (Type t))
  [∀ p, Small.{w} (T.obj p).left] [∀ p, Small.{w} (T.obj p).right]

/-- Normalize the actual Arrow functions and both maps by their explicit original bijections. -/
def normalizedFunctor : A ⥤ Arrow (Type w) where
  obj p := Arrow.mk (ofHom (equivShrink (T.obj p).right ∘
    (T.obj p).hom ∘ (equivShrink (T.obj p).left).symm))
  map {p q} τ := Arrow.homMk
    (ofHom (equivShrink (T.obj q).left ∘ (T.map τ).left ∘
      (equivShrink (T.obj p).left).symm))
    (ofHom (equivShrink (T.obj q).right ∘ (T.map τ).right ∘
      (equivShrink (T.obj p).right).symm)) (by
      apply ConcreteCategory.hom_ext
      intro z
      change equivShrink (T.obj q).right
          ((T.obj q).hom ((equivShrink (T.obj q).left).symm
            (equivShrink (T.obj q).left ((T.map τ).left
              ((equivShrink (T.obj p).left).symm z))))) =
        equivShrink (T.obj q).right ((T.map τ).right
          ((equivShrink (T.obj p).right).symm
            (equivShrink (T.obj p).right
              ((T.obj p).hom ((equivShrink (T.obj p).left).symm z)))))
      simp only [Equiv.symm_apply_apply]
      exact congrArg (equivShrink (T.obj q).right)
        (ConcreteCategory.congr_hom (T.map τ).w
          ((equivShrink (T.obj p).left).symm z)))
  map_id p := by
    apply Arrow.hom_ext
    · apply ConcreteCategory.hom_ext
      intro z
      change equivShrink (T.obj p).left
        ((T.map (𝟙 p)).left ((equivShrink (T.obj p).left).symm z)) = z
      rw [T.map_id]
      exact (equivShrink (T.obj p).left).apply_symm_apply z
    · apply ConcreteCategory.hom_ext
      intro z
      change equivShrink (T.obj p).right
        ((T.map (𝟙 p)).right ((equivShrink (T.obj p).right).symm z)) = z
      rw [T.map_id]
      exact (equivShrink (T.obj p).right).apply_symm_apply z
  map_comp {p q r} τ σ := by
    apply Arrow.hom_ext
    · apply ConcreteCategory.hom_ext
      intro z
      change equivShrink (T.obj r).left
        ((T.map (τ ≫ σ)).left ((equivShrink (T.obj p).left).symm z)) =
        equivShrink (T.obj r).left ((T.map σ).left
          ((equivShrink (T.obj q).left).symm
            (equivShrink (T.obj q).left ((T.map τ).left
              ((equivShrink (T.obj p).left).symm z)))))
      rw [T.map_comp]
      simp only [Equiv.symm_apply_apply]
      rfl
    · apply ConcreteCategory.hom_ext
      intro z
      change equivShrink (T.obj r).right
        ((T.map (τ ≫ σ)).right ((equivShrink (T.obj p).right).symm z)) =
        equivShrink (T.obj r).right ((T.map σ).right
          ((equivShrink (T.obj q).right).symm
            (equivShrink (T.obj q).right ((T.map τ).right
              ((equivShrink (T.obj p).right).symm z)))))
      rw [T.map_comp]
      simp only [Equiv.symm_apply_apply]
      rfl

/-- The complete normalized object function recovers the same actual original function. -/
theorem normalizedFunctor_hom_function (p : A) :
    ((normalizedFunctor T).obj p).hom ∘ equivShrink (T.obj p).left =
      equivShrink (T.obj p).right ∘ (T.obj p).hom := by
  funext z
  change equivShrink (T.obj p).right
    ((T.obj p).hom ((equivShrink (T.obj p).left).symm
      (equivShrink (T.obj p).left z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The full normalized source map retains every original source-map value. -/
theorem normalizedFunctor_map_left_function {p q : A} (τ : p ⟶ q) :
    ((normalizedFunctor T).map τ).left ∘ equivShrink (T.obj p).left =
      equivShrink (T.obj q).left ∘ (T.map τ).left := by
  funext z
  change equivShrink (T.obj q).left
    ((T.map τ).left ((equivShrink (T.obj p).left).symm
      (equivShrink (T.obj p).left z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The full normalized target map retains every original target-map value. -/
theorem normalizedFunctor_map_right_function {p q : A} (τ : p ⟶ q) :
    ((normalizedFunctor T).map τ).right ∘ equivShrink (T.obj p).right =
      equivShrink (T.obj q).right ∘ (T.map τ).right := by
  funext z
  change equivShrink (T.obj q).right
    ((T.map τ).right ((equivShrink (T.obj p).right).symm
      (equivShrink (T.obj p).right z))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Explicit working-size normalization preserves and reflects actual surjectivity. -/
theorem normalizedFunctor_surjective_iff (p : A) :
    Function.Surjective ((normalizedFunctor T).obj p).hom ↔
      Function.Surjective (T.obj p).hom := by
  change Function.Surjective
    (equivShrink (T.obj p).right ∘ (T.obj p).hom ∘
      (equivShrink (T.obj p).left).symm) ↔ _
  constructor
  · intro h z
    obtain ⟨l, hl⟩ := h (equivShrink (T.obj p).right z)
    exact ⟨(equivShrink (T.obj p).left).symm l,
      (equivShrink (T.obj p).right).injective hl⟩
  · intro h z
    obtain ⟨l, hl⟩ := h ((equivShrink (T.obj p).right).symm z)
    refine ⟨equivShrink (T.obj p).left l, ?_⟩
    change equivShrink (T.obj p).right
      ((T.obj p).hom ((equivShrink (T.obj p).left).symm
        (equivShrink (T.obj p).left l))) = z
    rw [Equiv.symm_apply_apply, hl, Equiv.apply_symm_apply]

end Normalization

variable {C : Type u} [Category.{v} C] {ι : Type s} (f : ι → Arrow C)

/-- All actual diagonal arrows, with their original generator tags. -/
abbrev RawLifts (p : Arrow C) : Type (max s v) :=
  Σ k : ι, (f k).right ⟶ p.left

/-- All native commuting squares, with their original generator tags. -/
abbrev RawSquares (p : Arrow C) : Type (max s v) :=
  Σ k : ι, f k ⟶ p

/-- A tagged diagonal gives its actual native square and both original factor maps. -/
def liftToSquare (p : Arrow C) : RawLifts f p → RawSquares f p :=
  fun z => ⟨z.1, Arrow.homMk ((f z.1).hom ≫ z.2) (z.2 ≫ p.hom)
    (Category.assoc _ _ _)⟩

/-- The original generator tag is retained by the entire test function. -/
theorem liftToSquare_tag (p : Arrow C) (z : RawLifts f p) :
    (liftToSquare f p z).1 = z.1 := rfl

/-- The top field is the original generator followed by the original diagonal. -/
theorem liftToSquare_left (p : Arrow C) (k : ι) (l : (f k).right ⟶ p.left) :
    (liftToSquare f p ⟨k, l⟩).2.left = (f k).hom ≫ l := rfl

/-- The bottom field is the original diagonal followed by the original tested arrow. -/
theorem liftToSquare_right (p : Arrow C) (k : ι) (l : (f k).right ⟶ p.left) :
    (liftToSquare f p ⟨k, l⟩).2.right = l ≫ p.hom := rfl

/-- Actual Arrow postcomposition acts on the original tagged diagonals. -/
def rawLiftMap {p q : Arrow C} (τ : p ⟶ q) : RawLifts f p → RawLifts f q :=
  fun z => ⟨z.1, z.2 ≫ τ.left⟩

/-- Actual Arrow postcomposition acts on the original tagged native squares. -/
def rawSquareMap {p q : Arrow C} (τ : p ⟶ q) : RawSquares f p → RawSquares f q :=
  fun z => ⟨z.1, z.2 ≫ τ⟩

/-- The whole original diagonal map of an identity is the identity function. -/
theorem rawLiftMap_id (p : Arrow C) : rawLiftMap f (𝟙 p) = id := by
  funext z
  rcases z with ⟨k, l⟩
  simp [rawLiftMap, id]

/-- The whole original square map of an identity is the identity function. -/
theorem rawSquareMap_id (p : Arrow C) : rawSquareMap f (𝟙 p) = id := by
  funext z
  rcases z with ⟨k, a⟩
  simp [rawSquareMap, id]

/-- The whole original diagonal function retains composition of actual Arrow squares. -/
theorem rawLiftMap_comp {p q r : Arrow C} (τ : p ⟶ q) (σ : q ⟶ r) :
    rawLiftMap f (τ ≫ σ) = rawLiftMap f σ ∘ rawLiftMap f τ := by
  funext z
  rcases z with ⟨k, l⟩
  simp [rawLiftMap, Category.assoc]

/-- The whole original square function retains composition of actual Arrow squares. -/
theorem rawSquareMap_comp {p q r : Arrow C} (τ : p ⟶ q) (σ : q ⟶ r) :
    rawSquareMap f (τ ≫ σ) = rawSquareMap f σ ∘ rawSquareMap f τ := by
  funext z
  rcases z with ⟨k, a⟩
  simp [rawSquareMap, Category.assoc]

/-- Both full original functions commute with the actual tested Arrow square. -/
theorem liftToSquare_naturality {p q : Arrow C} (τ : p ⟶ q) :
    rawSquareMap f τ ∘ liftToSquare f p =
      liftToSquare f q ∘ rawLiftMap f τ := by
  funext z
  rcases z with ⟨k, l⟩
  dsimp only [Function.comp_apply, rawSquareMap, liftToSquare, rawLiftMap]
  apply congrArg (fun a : f k ⟶ q => (⟨k, a⟩ : RawSquares f q))
  apply Arrow.hom_ext
  · exact Category.assoc _ _ _
  · change (l ≫ p.hom) ≫ τ.right = (l ≫ τ.left) ≫ q.hom
    simpa only [Category.assoc] using
      congrArg (fun a : p.left ⟶ q.right => l ≫ a) τ.w.symm

/-- The original tagged diagonals form their actual Type-valued functor. -/
def liftsFunctor : Arrow C ⥤ Type (max s v) where
  obj p := RawLifts f p
  map τ := ofHom (rawLiftMap f τ)
  map_id p := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrFun (rawLiftMap_id f p) z
  map_comp τ σ := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrFun (rawLiftMap_comp f τ σ) z

/-- The original tagged native squares form their actual Type-valued functor. -/
def squaresFunctor : Arrow C ⥤ Type (max s v) where
  obj p := RawSquares f p
  map τ := ofHom (rawSquareMap f τ)
  map_id p := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrFun (rawSquareMap_id f p) z
  map_comp τ σ := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrFun (rawSquareMap_comp f τ σ) z

/-- The test is the original natural transformation between those two actual functors. -/
def liftToSquareNatTrans : liftsFunctor f ⟶ squaresFunctor f where
  app p := ofHom (liftToSquare f p)
  naturality p q τ := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (congrFun (liftToSquare_naturality f τ) z).symm

/-- The raw right-lifting test retains the original test function and both Arrow maps. -/
abbrev rawFunctor : Arrow C ⥤ Arrow (Type (max s v)) :=
  NatTrans.arrow (liftToSquareNatTrans f)

/-- The raw Arrow object has exactly the complete original test function. -/
theorem rawFunctor_hom_function (p : Arrow C) :
    ((rawFunctor f).obj p).hom = ofHom (liftToSquare f p) := rfl

/-- The entire source map is the original tagged diagonal map. -/
theorem rawFunctor_map_left_function {p q : Arrow C} (τ : p ⟶ q) :
    ((rawFunctor f).map τ).left = ofHom (rawLiftMap f τ) := rfl

/-- The entire target map is the original tagged native square map. -/
theorem rawFunctor_map_right_function {p q : Arrow C} (τ : p ⟶ q) :
    ((rawFunctor f).map τ).right = ofHom (rawSquareMap f τ) := rfl

/-- Surjectivity retains the actual original generator and both native lift equations. -/
theorem rawFunctor_surjective_iff (p : Arrow C) :
    Function.Surjective ((rawFunctor f).obj p).hom ↔
      ∀ k : ι, HasLiftingProperty (f k).hom p.hom := by
  constructor
  · intro h k
    rw [Arrow.hasLiftingProperty_iff]
    intro a
    change f k ⟶ p at a
    obtain ⟨⟨k', l⟩, hl⟩ := h ⟨k, a⟩
    change liftToSquare f p ⟨k', l⟩ = ⟨k, a⟩ at hl
    have htag : k' = k := congrArg Sigma.fst hl
    subst k'
    have ha := sigma_mk_injective hl
    refine ⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩
    · exact congrArg (fun b : f k ⟶ p => b.left) ha
    · exact congrArg (fun b : f k ⟶ p => b.right) ha
  · intro h z
    rcases z with ⟨k, a⟩
    let _ : HasLiftingProperty (f k).hom p.hom := h k
    let sq : CommSq a.left (f k).hom p.hom a.right := ⟨a.w⟩
    refine ⟨⟨k, sq.lift⟩, ?_⟩
    change liftToSquare f p ⟨k, sq.lift⟩ = ⟨k, a⟩
    dsimp only [liftToSquare]
    apply congrArg (fun b : f k ⟶ p => (⟨k, b⟩ : RawSquares f p))
    apply Arrow.hom_ext
    · exact sq.fac_left
    · exact sq.fac_right

/-- Surjectivity is exactly the native right class of the actual indexed arrow family. -/
theorem rawFunctor_surjective_iff_rlp (p : Arrow C) :
    Function.Surjective ((rawFunctor f).obj p).hom ↔
      (MorphismProperty.ofHoms (fun k => (f k).hom)).rlp p.hom := by
  rw [rawFunctor_surjective_iff]
  constructor
  · intro h A B i hi
    cases hi with
    | mk k => exact h k
  · intro h k
    exact h ((f k).hom) (MorphismProperty.ofHoms.mk k)

section WorkingSize

variable [Small.{w} ι] [LocallySmall.{w} C]

/-- The original diagonal family is working-small without shrinking the coefficient objects. -/
instance rawLifts_small (p : Arrow C) : Small.{w} (RawLifts f p) := by
  unfold RawLifts
  infer_instance

/-- Native Arrow local smallness makes the original tagged square family working-small. -/
instance rawSquares_small (p : Arrow C) : Small.{w} (RawSquares f p) := by
  let _ : LocallySmall.{w} (Arrow C) := Comma.locallySmall (𝟭 C) (𝟭 C)
  unfold RawSquares
  infer_instance

/-- The explicit working-size equivalence of all original tagged diagonals. -/
def liftsEquiv (p : Arrow C) : RawLifts f p ≃ Shrink.{w} (RawLifts f p) :=
  equivShrink _

/-- The explicit working-size equivalence of all original tagged native squares. -/
def squaresEquiv (p : Arrow C) : RawSquares f p ≃ Shrink.{w} (RawSquares f p) :=
  equivShrink _

/-- The actual working-size test conjugates the original full functions by their bijections. -/
abbrev smallFunctor : Arrow C ⥤ Arrow (Type w) := by
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).left :=
    fun p => rawLifts_small f p
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).right :=
    fun p => rawSquares_small f p
  exact normalizedFunctor.{w} (rawFunctor f)

/-- The whole working-size test retains the original test under both actual equivalences. -/
theorem smallFunctor_hom_function (p : Arrow C) :
    ((smallFunctor f).obj p).hom ∘ liftsEquiv f p =
      squaresEquiv f p ∘ liftToSquare f p := by
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).left :=
    fun p => rawLifts_small f p
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).right :=
    fun p => rawSquares_small f p
  exact normalizedFunctor_hom_function.{w} (rawFunctor f) p

/-- The entire normalized diagonal map recovers the original map on every original input. -/
theorem smallFunctor_map_left_function {p q : Arrow C} (τ : p ⟶ q) :
    ((smallFunctor f).map τ).left ∘ liftsEquiv f p =
      liftsEquiv f q ∘ rawLiftMap f τ := by
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).left :=
    fun p => rawLifts_small f p
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).right :=
    fun p => rawSquares_small f p
  exact normalizedFunctor_map_left_function.{w} (rawFunctor f) τ

/-- The entire normalized square map recovers the original map on every original input. -/
theorem smallFunctor_map_right_function {p q : Arrow C} (τ : p ⟶ q) :
    ((smallFunctor f).map τ).right ∘ squaresEquiv f p =
      squaresEquiv f q ∘ rawSquareMap f τ := by
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).left :=
    fun p => rawLifts_small f p
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).right :=
    fun p => rawSquares_small f p
  exact normalizedFunctor_map_right_function.{w} (rawFunctor f) τ

/-- The working-size function is surjective exactly for the original generated right class. -/
theorem smallFunctor_surjective_iff (p : Arrow C) :
    Function.Surjective ((smallFunctor f).obj p).hom ↔
      (MorphismProperty.ofHoms (fun k => (f k).hom)).rlp p.hom := by
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).left :=
    fun p => rawLifts_small f p
  let _ : ∀ p : Arrow C, Small.{w} ((rawFunctor f).obj p).right :=
    fun p => rawSquares_small f p
  exact (normalizedFunctor_surjective_iff.{w} (rawFunctor f) p).trans
    (rawFunctor_surjective_iff_rlp f p)

end WorkingSize
end CategoryTheory.MorphismProperty.LiftingTest
