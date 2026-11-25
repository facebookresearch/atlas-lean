/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps
public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Actual contravariant presheaf sources and representable right slices

The right slice consists of the original (n+1)-simplices with the final
vertex fixed. Its projection deletes that final vertex. Right fibrations
use every native noninitial horn. The presheaf infinity category is the
full categorical localization of the actual right-fibration category at
fibrewise weak equivalences, retaining all coherent natural transformations.

This source is independent of K-theory and of motive corepresentability.
References: Lurie, Higher Topos Theory, Sections 2.1--2.2 and 5.3.5;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.4 and 9.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTContravariantPresheaves

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels
open SimplicialCovariantModels
open scoped Simplicial

universe u

/-- Append the fixed final vertex to the actual simplex order map. -/
def appendMap {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.mk (n.len + 1) ⟶ SimplexCategory.mk (m.len + 1) :=
  SimplexCategory.Hom.mk
    { toFun := Fin.lastCases (Fin.last (m.len + 1))
        (fun i => (f.toOrderHom i).castSucc)
      monotone' := by
        intro a b hab
        cases a using Fin.lastCases with
        | last =>
          have hb : b = Fin.last (n.len + 1) :=
            le_antisymm (Fin.le_last _) hab
          subst b
          exact le_rfl
        | cast a =>
          cases b using Fin.lastCases with
          | last =>
            simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
            exact Fin.le_last _
          | cast b =>
            simp only [Fin.lastCases_castSucc]
            exact Fin.castSucc_le_castSucc_iff.mpr
              (f.toOrderHom.monotone (Fin.castSucc_le_castSucc_iff.mp hab)) }

/-- The entire native final-vertex simplex functor. -/
def append : SimplexCategory ⥤ SimplexCategory where
  obj n := .mk (n.len + 1)
  map f := appendMap f
  map_id n := by
    ext i
    cases i using Fin.lastCases <;> simp [appendMap]
  map_comp f g := by
    ext i
    cases i using Fin.lastCases <;> simp [appendMap]

/-- The original final vertex of the appended simplex. -/
def finalVertex (n : SimplexCategory) : ⦋0⦌ ⟶ append.obj n :=
  SimplexCategory.const _ _ (Fin.last (n.len + 1))

/-- Every actual appended simplex map preserves that final vertex. -/
theorem finalVertex_append {n m : SimplexCategory} (f : n ⟶ m) :
    finalVertex n ≫ append.map f = finalVertex m := by
  ext i
  fin_cases i
  simp [finalVertex, append, appendMap]

/-- The native face retaining every vertex except the appended final one. -/
def omitFinalVertex (n : SimplexCategory) : n ⟶ append.obj n :=
  SimplexCategory.Hom.mk
    { toFun := Fin.castSucc
      monotone' := fun _ _ h => Fin.castSucc_le_castSucc_iff.mpr h }

/-- The original face commutes with the entire appended simplex map. -/
theorem omitFinalVertex_append {n m : SimplexCategory} (f : n ⟶ m) :
    omitFinalVertex n ≫ append.map f = f ≫ omitFinalVertex m := by
  ext i
  simp [omitFinalVertex, append, appendMap]

/-- The actual right slice retains all original source-to-fixed-target simplices. -/
def rightSlice (C : SSet.{u}) (x : C _⦋0⦌) : SSet.{u} where
  obj n := {a : C.obj (op (append.obj n.unop)) //
    C.map (finalVertex n.unop).op a = x}
  map {n m} f := ↾fun a =>
    ⟨C.map (append.map f.unop).op a.val, by
      rw [← C.map_comp_apply, ← op_comp, finalVertex_append]
      exact a.property⟩
  map_id n := by ext a; simp
  map_comp f g := by ext a; simp

/-- Projection deletes the appended final vertex from the actual simplex. -/
def sourceProjection (C : SSet.{u}) (x : C _⦋0⦌) : rightSlice C x ⟶ C where
  app n := ↾fun a => C.map (omitFinalVertex n.unop).op a.val
  naturality n m f := by
    ext a
    have h : (omitFinalVertex n.unop).op ≫ f =
        (append.map f.unop).op ≫ (omitFinalVertex m.unop).op := by
      apply Quiver.Hom.unop_inj
      simpa using (omitFinalVertex_append f.unop).symm
    change C.map (omitFinalVertex m.unop).op
        (C.map (append.map f.unop).op a.val) =
      C.map f (C.map (omitFinalVertex n.unop).op a.val)
    rw [← C.map_comp_apply, ← C.map_comp_apply, h]

/-- Right fibrations lift every original horn except the initial one. -/
def IsRightFibration {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 2)), 0 < i →
    HasLiftingProperty (Λ[n + 1, i].ι) p

/-- The native right-fibration full subcategory of simplicial sets over C. -/
def rightFibrationProperty (C : SSet.{u}) : ObjectProperty (Over C) :=
  fun E => IsRightFibration E.hom

/-- Every original map over C is retained before localization. -/
abbrev RightFibrationCategory (C : SSet.{u}) :=
  (rightFibrationProperty C).FullSubcategory

/-- Weak maps use all actual fibres and their native base-preserving maps. -/
def IsRightWeak {C : SSet.{u}} {E F : RightFibrationCategory C}
    (f : E ⟶ F) : Prop :=
  ∀ x : C _⦋0⦌,
    WeakEquivalence (fibreMap E.obj.hom F.obj.hom f.hom.left
      (Over.w f.hom) x)

/-- Inversion is tested on the actual source one-simplex of every weak map. -/
def InvertsRightWeak (C : SSet.{0}) (Z : SSet.{1})
    (a : (mapping (nerve (RightFibrationCategory C)) Z) _⦋0⦌) : Prop :=
  ∀ (E F : RightFibrationCategory C) (f : E ⟶ F), IsRightWeak f →
    IsEquivalenceEdge Z
      (((mappingZero _ _).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- The entire right-fibration localization, with its full functor universal property. -/
structure PresheafInfinitySource (C : SSet.{0}) where
  category : SSet.{1}
  quasicategory : SSet.Quasicategory category
  source : nerve (RightFibrationCategory C) ⟶ category
  source_objects : Function.Bijective (source.app (op ⦋0⦌))
  invert : ∀ (E F : RightFibrationCategory C) (f : E ⟶ F), IsRightWeak f →
    IsEquivalenceEdge category
      (source.app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (Z : SSet.{1}) [SSet.Quasicategory Z],
    ∃ f : mapping category Z ⟶
      ((mapping (nerve (RightFibrationCategory C)) Z).fullEnhancedSubcategory (InvertsRightWeak C Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition source Z ∧
        CategoricalWeakEquivalence f

attribute [instance] PresheafInfinitySource.quasicategory

/-- A representable object is the actual source-localized right slice. -/
structure PresheafYonedaSource (C : SSet.{0})
    (P : PresheafInfinitySource C) where
  representable : C _⦋0⦌ → RightFibrationCategory C
  total : ∀ x : C _⦋0⦌, (representable x).obj.left = rightSlice C x
  projection : ∀ x : C _⦋0⦌,
    HEq (representable x).obj.hom (sourceProjection C x)
  map : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj C ⟶ P.category
  vertex : ∀ x : C _⦋0⦌,
    map.app (op ⦋0⦌) (ULift.up x) =
      P.source.app (op ⦋0⦌) (ComposableArrows.mk₀ (representable x))
  evaluation : ∀ E : RightFibrationCategory C,
    pullback
      (sourceProjection P.category
        (P.source.app (op ⦋0⦌) (ComposableArrows.mk₀ E))) map ⟶
      (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj E.obj.left
  evaluation_over : ∀ E : RightFibrationCategory C,
    evaluation E ≫
      (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map E.obj.hom =
      pullback.snd
        (sourceProjection P.category
          (P.source.app (op ⦋0⦌) (ComposableArrows.mk₀ E))) map
  evaluation_weak : ∀ (E : RightFibrationCategory C)
    (x : ((SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj C) _⦋0⦌),
    WeakEquivalence (fibreMap
      (pullback.snd
        (sourceProjection P.category
          (P.source.app (op ⦋0⦌) (ComposableArrows.mk₀ E))) map)
      ((SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map E.obj.hom)
      (evaluation E) (evaluation_over E) x)

/-- Equivalence of actual objects uses a native equivalence edge and its endpoints. -/
def EquivalentVertices (C : SSet.{u}) (x y : C _⦋0⦌) : Prop :=
  ∃ e : C _⦋1⦌, IsEquivalenceEdge C e ∧ C.δ 1 e = x ∧ C.δ 0 e = y

/-- Representability uses the actual whole right-slice source object. -/
def IsRepresentableVertex {C : SSet.{0}} (P : PresheafInfinitySource C)
    (Y : PresheafYonedaSource C P) (x : P.category _⦋0⦌) : Prop :=
  ∃ a : C _⦋0⦌, EquivalentVertices P.category x
    (Y.map.app (op ⦋0⦌) (ULift.up a))

end MathlibExt.AlgebraicTopology.BGTContravariantPresheaves
