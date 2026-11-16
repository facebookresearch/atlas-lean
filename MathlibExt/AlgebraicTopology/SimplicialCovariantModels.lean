/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Native left slices and covariant models

The left slice uses the actual (n+1)-simplices with first vertex fixed.
Its projection deletes that first vertex. Thus its fibre represents the
actual mapping space from the fixed source, including every higher
simplex. Left fibrations use all actual left-horn lifting tests.

Covariant weak equivalence is tested by the native mapping spaces over
the fixed base, into every left fibration. A replacement is a genuine
augmentation over that base, not independently chosen fibre spaces.

Reference: Lurie, Higher Topos Theory, §§2.1--2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.SimplicialCovariantModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u

/-- Prepend one fixed initial vertex to an actual simplex order map. -/
def prependMap {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.mk (n.len + 1) ⟶ SimplexCategory.mk (m.len + 1) :=
  SimplexCategory.Hom.mk
    { toFun := Fin.cases 0 (fun i => (f.toOrderHom i).succ)
      monotone' := by
        intro a b hab
        cases a using Fin.cases with
        | zero => exact Fin.zero_le _
        | succ a =>
          cases b using Fin.cases with
          | zero => simp at hab
          | succ b =>
              change (f.toOrderHom a).succ ≤ (f.toOrderHom b).succ
              simpa only [Fin.succ_le_succ_iff] using
                f.toOrderHom.monotone
                  (show a ≤ b from by simpa only [Fin.succ_le_succ_iff] using hab) }

/-- Actual fixed-initial-vertex simplex functor. -/
def prepend : SimplexCategory ⥤ SimplexCategory where
  obj n := .mk (n.len + 1)
  map f := prependMap f
  map_id n := by ext i; cases i using Fin.cases <;> rfl
  map_comp f g := by ext i; cases i using Fin.cases <;> rfl

/-- The actual first vertex of the prepended simplex. -/
def initialVertex (n : SimplexCategory) : ⦋0⦌ ⟶ prepend.obj n :=
  SimplexCategory.const _ _ 0

/-- Every prepended simplex map preserves the fixed initial vertex. -/
theorem initialVertex_prepend {n m : SimplexCategory} (f : n ⟶ m) :
    initialVertex n ≫ prepend.map f = initialVertex m := by
  ext i
  fin_cases i
  rfl

/-- The actual left slice, retaining all coherent source-fixed simplices. -/
def leftSlice (C : SSet.{u}) (x : C _⦋0⦌) : SSet.{u} where
  obj n := {a : C.obj (op (prepend.obj n.unop)) // C.map (initialVertex n.unop).op a = x}
  map {n m} f := ↾fun a => ⟨C.map (prepend.map f.unop).op a.val, by
    rw [← C.map_comp_apply, ← op_comp, initialVertex_prepend]
    exact a.property⟩
  map_id n := by
    ext a
    change C.map (prepend.map (𝟙 n.unop)).op a.val = a.val
    simp
  map_comp f g := by
    ext a
    simp

/-- The actual map from the left slice to its target vertex/simplex. -/
def targetProjection (C : SSet.{u}) (x : C _⦋0⦌) : leftSlice C x ⟶ C where
  app n := ↾fun a => C.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op a.val
  naturality n m f := by
    ext a
    symm
    let b : C.obj (op (prepend.obj n.unop)) := a.val
    change C.map f (C.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op b) =
      C.map (SimplexCategory.δ (0 : Fin (m.unop.len + 2))).op
        (C.map (prepend.map f.unop).op b)
    have h : (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op ≫ f =
        (prepend.map f.unop).op ≫ (SimplexCategory.δ (0 : Fin (m.unop.len + 2))).op := by
      apply Quiver.Hom.unop_inj
      ext i
      rfl
    calc
      C.map f (C.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op b) =
          C.map ((SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op ≫ f) b :=
        (C.map_comp_apply _ _ _).symm
      _ = C.map ((prepend.map f.unop).op ≫
          (SimplexCategory.δ (0 : Fin (m.unop.len + 2))).op) b :=
        congrArg (fun t => C.map t b) h
      _ = C.map (SimplexCategory.δ (0 : Fin (m.unop.len + 2))).op
          (C.map (prepend.map f.unop).op b) := C.map_comp_apply _ _ _

/-- A left fibration lifts every actual horn except the final one. -/
def IsLeftFibration {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
    HasLiftingProperty (Λ[n + 1, i].ι) p

/-- Mapping over the base is a literal native Hom subcomplex. -/
def mappingOverSubcomplex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) :
    (mapping X Y).Subcomplex where
  obj n := {a | ∀ (m : SimplexCategoryᵒᵖ) (f : n ⟶ m) (x : X.obj m),
    q.app m ((a.app m f) x) = p.app m x}
  map {n m} f a h := by
    intro l g x
    exact h l (f ≫ g) x

/-- The actual relative mapping space, retaining all parameter simplices. -/
def mappingOver {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) : SSet.{u} :=
  (mappingOverSubcomplex p q).toSSet

/-- An actual map over the base is its native vertex in the relative mapping space. -/
def overMapVertex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (hf : f ≫ q = p) : (mappingOver p q) _⦋0⦌ :=
  ⟨(SimplicialCategory.homEquiv' X Y) f, by
    intro m g x
    change q.app m (f.app m x) = p.app m x
    exact congrArg (fun t => t.app m x) hf⟩

/-- Precompose the actual relative Hom by an actual map over its base. -/
def mappingOverMap {X Y Z B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B)
    (i : X ⟶ Y) (h : i ≫ q = p) : mappingOver q r ⟶ mappingOver p r where
  app n := ↾fun a => ⟨((SimplicialCategory.sHomFunctor SSet).map i.op).app Z |>.app n a.val, by
    intro m f x
    change r.app m ((a.val.app m f) (i.app m x)) = p.app m x
    rw [a.property m f (i.app m x)]
    exact congrArg (fun t => t.app m x) h⟩
  naturality n m g := by
    ext a
    apply Subtype.ext
    exact congrArg (fun t => t a.val) ((((SimplicialCategory.sHomFunctor SSet).map i.op).app Z).naturality g)

/-- Covariant weak equivalence is the actual relative mapping test into all left fibrations. -/
def IsCovariantWeakEquivalence {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (i : X ⟶ Y) (h : i ≫ q = p) : Prop :=
  ∀ (Z : SSet.{u}) (r : Z ⟶ B), IsLeftFibration r →
    WeakEquivalence (mappingOverMap p q r i h)

/-- An actual fibrant covariant replacement, with its entire base-preserving augmentation. -/
structure CovariantReplacement {X B : SSet.{u}} (p : X ⟶ B) where
  total : SSet.{u}
  projection : total ⟶ B
  map : X ⟶ total
  mono : Mono map
  over : map ≫ projection = p
  left_fibration : IsLeftFibration projection
  weak : IsCovariantWeakEquivalence p projection map over

/-- The actual fibre of a map at a specified base vertex. -/
def fibre {E B : SSet.{u}} (p : E ⟶ B) (x : B _⦋0⦌) : SSet.{u} :=
  pullback p (SSet.const x : Δ[0] ⟶ B)

/-- An actual map over the base induces its literal map between those fibres. -/
def fibreMap {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (h : f ≫ q = p) (x : B _⦋0⦌) : fibre p x ⟶ fibre q x :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (by
    rw [Category.assoc, h, pullback.condition])

end MathlibExt.AlgebraicTopology.SimplicialCovariantModels
