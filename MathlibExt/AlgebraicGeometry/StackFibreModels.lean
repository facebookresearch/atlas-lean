/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackCycleGeometry
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Actual fibred-category models of stack base changes

The fibre of `f : X → Y` over `(T,y)` is the costructured-arrow category
of the actual CoGrothendieck functor at that point. Its objects retain
the scheme map, source object and comparison isomorphism; its morphisms
retain both base and fibre arrows. A scheme model is an equivalence to
schemes over a genuine `Z`, compatible with the actual projection to `T`.
This avoids objectwise fibre bijections without base-change coherence.

References: Stacks Tags 0045 and 026D; Kresch arXiv:math/9810166v1,
Convention 2.1.1. The Grothendieck functors and their laws are completed
Mathlib mathematics, reused directly rather than re-requested.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackFibreModels

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry

variable {S : Scheme.{0}}

abbrev Total (X : Stack S) := Pseudofunctor.CoGrothendieck X.toPseudofunctor

abbrev totalMap {X Y : Stack S} (f : StackHom X Y) : Total X ⥤ Total Y :=
  Pseudofunctor.CoGrothendieck.map f

def point {X : Stack S} (T : Over S) (x : X.Fibre T) : Total X := ⟨T, x⟩

abbrev FibreCategory {X Y : Stack S} (f : StackHom X Y)
    (T : Over S) (y : Y.Fibre T) :=
  CostructuredArrow (totalMap f) (point T y)

/-- The literal map to the category of schemes over the test point. -/
def fibreForget {X Y : Stack S} (f : StackHom X Y) (T : Over S)
    (y : Y.Fibre T) : FibreCategory f T y ⥤ Over T where
  obj q := Over.mk q.hom.base
  map {q r} h := Over.homMk h.left.base (by
    have hh := congrArg
      (fun a : (totalMap f).obj q.left ⟶ point T y => a.base) h.w
    exact hh)
  map_id q := by rfl
  map_comp h k := by rfl

/-- All morphisms and the structural map are part of representability,
not merely the set of isomorphism classes in each fibre. -/
structure SchemeFibreModel {X Y : Stack S} (f : StackHom X Y)
    (T : Over S) (y : Y.Fibre T) where
  scheme : Over T.left
  comparison : FibreCategory f T y ≌ Over scheme.left
  overBase : comparison.functor ⋙ Over.map scheme.hom ≅
    fibreForget f T y ⋙ T.iteratedSliceForward

def HasSchemeFibres {X Y : Stack S} (f : StackHom X Y) : Prop :=
  ∀ (T : Over S) (y : Y.Fibre T), Nonempty (SchemeFibreModel f T y)

/-- Closedness is checked on the actual represented scheme fibres. -/
def IsClosed {X Y : Stack S} (f : StackHom X Y) : Prop :=
  ∀ (T : Over S) (y : Y.Fibre T), ∃ m : SchemeFibreModel f T y,
    IsClosedImmersion m.scheme.hom

/-- A stack base-change model may also be retained when the morphism is
not representable by schemes, as for a DM-type or vector-bundle stack. -/
structure StackFibreModel {X Y : Stack S} (f : StackHom X Y)
    (T : Over S) (y : Y.Fibre T) where
  stack : Stack T.left
  comparison : Total stack ≌ FibreCategory f T y
  overBase : comparison.functor ⋙ fibreForget f T y ⋙ T.iteratedSliceForward ≅
    Pseudofunctor.CoGrothendieck.forget stack.toPseudofunctor

def IsDMType {X Y : Stack S} (f : StackHom X Y) : Prop :=
  ∀ (T : Over S) (y : Y.Fibre T), ∃ m : StackFibreModel f T y,
    m.stack.IsDeligneMumfordStack

end AlgebraicGeometry.StackFibreModels
