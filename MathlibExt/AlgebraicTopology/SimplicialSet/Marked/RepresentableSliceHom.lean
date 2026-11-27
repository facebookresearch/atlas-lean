/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Whole marked representable maps in the original slice

The actual slice Hom records its entire marked map and original base
equation. Minimal standard-simplex maps are the original simplices;
sharp interval maps are the actual marked edges. Yoneda reads the
whole base equation in both cases, without changing the supplied
source or projection.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Slice maps are exactly the original entire marked maps with their complete original base equation. -/
def overHomSubtypeEquiv {Z : Marked.{u}} (X Y : Over Z) :
    (X ⟶ Y) ≃ {f : X.left ⟶ Y.left // f ≫ Y.hom = X.hom} where
  toFun f := ⟨f.left, Over.w f⟩
  invFun f := Over.homMk f.val f.property
  left_inv f := by apply Over.OverMorphism.ext; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- The original minimal marked standard simplex has precisely the entire native Yoneda Hom correspondence. -/
def minSimplexHomEquiv (n : ℕ) (Y : Marked.{u}) : (min (Δ[n] : SSet.{u}) ⟶ Y) ≃ Y.toSSet _⦋n⦌ :=
  (minimalHomEquiv (Δ[n] : SSet.{u}) Y).trans SSet.yonedaEquiv

/-- Every original minimal simplex map over the base is exactly a native simplex with its actual whole base equation. -/
def overMinSimplexHomEquiv {Z : Marked.{u}} (Y : Over Z) (n : ℕ)
    (p : min (Δ[n] : SSet.{u}) ⟶ Z) :
    (Over.mk p ⟶ Y) ≃
      {x : Y.left.toSSet _⦋n⦌ // Y.hom.hom.app (op ⦋n⦌) x = SSet.yonedaEquiv p.hom} :=
  (overHomSubtypeEquiv (Over.mk p) Y).trans
    (Equiv.subtypeEquiv (minSimplexHomEquiv n Y.left) (fun f =>
      ⟨fun h => by
          have hh : (f ≫ Y.hom).hom = p.hom := congrArg Hom.hom h
          exact congrArg SSet.yonedaEquiv hh,
        fun h => by
          apply Hom.ext
          apply SSet.yonedaEquiv.injective
          change Y.hom.hom.app (op ⦋n⦌) (SSet.yonedaEquiv f.hom) = SSet.yonedaEquiv p.hom
          exact h⟩))

/-- Original sharp interval maps over the base are exactly the original marked edges with their whole
  projection equation. -/
def overMaxIntervalHomEquiv {Z : Marked.{u}} (Y : Over Z) (p : max (Δ[1] : SSet.{u}) ⟶ Z) :
    (Over.mk p ⟶ Y) ≃
      {e : Y.left.marking // Y.hom.hom.app (op ⦋1⦌) e.val = SSet.yonedaEquiv p.hom} :=
  (overHomSubtypeEquiv (Over.mk p) Y).trans
    (Equiv.subtypeEquiv (maxIntervalHomEquiv Y.left) (fun f =>
      ⟨fun h => by
          have hh : (f ≫ Y.hom).hom = p.hom := congrArg Hom.hom h
          exact congrArg SSet.yonedaEquiv hh,
        fun h => by
          apply Hom.ext
          apply SSet.yonedaEquiv.injective
          change Y.hom.hom.app (op ⦋1⦌) (SSet.yonedaEquiv f.hom) = SSet.yonedaEquiv p.hom
          exact h⟩))

end SSet.Marked
