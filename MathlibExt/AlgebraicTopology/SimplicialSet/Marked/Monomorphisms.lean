/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Original monomorphisms of marked simplicial sets

Minimal standard-simplex markings test every original simplex, so a marked
map is monic exactly when its original simplicial map is monic. This is a
carrier/cofibration prerequisite; no marked model or weak class is assumed.
-/

universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- A marked monomorphism is injective on each original simplex. -/
theorem Hom.injective_app {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] (n : SimplexCategory) :
    Function.Injective (f.hom.app (op n)) := by
  intro a b hab
  let g : min (SSet.stdSimplex.obj n) ⟶ X := ofMin (SSet.yonedaEquiv.symm a)
  let h : min (SSet.stdSimplex.obj n) ⟶ X := ofMin (SSet.yonedaEquiv.symm b)
  have he : g ≫ f = h ≫ f := by
    apply Hom.ext
    apply SSet.yonedaEquiv.injective
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm a ≫ f.hom) =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm b ≫ f.hom)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hab
  have hgh : g = h := (cancel_mono f).mp he
  exact SSet.yonedaEquiv.symm.injective (congrArg Hom.hom hgh)

/-- The original underlying simplicial map of a marked monomorphism is itself monic. -/
theorem Hom.mono_underlying {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] : Mono f.hom := by
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (f.hom.app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (f.injective_app n.unop)
  exact NatTrans.mono_of_mono_app f.hom

/-- A map monic on its original simplicial carrier is monic as a marked map. -/
theorem Hom.mono_of_underlying {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f.hom] : Mono f where
  right_cancellation g h w := by
    apply Hom.ext
    apply (cancel_mono f.hom).mp
    exact congrArg Hom.hom w

/-- The actual marked and underlying monomorphism predicates coincide on the original map. -/
theorem mono_iff_underlying {X Y : Marked.{u}} (f : X ⟶ Y) : Mono f ↔ Mono f.hom := by
  constructor
  · intro h
    let _ : Mono f := h
    exact f.mono_underlying
  · intro h
    let _ : Mono f.hom := h
    exact f.mono_of_underlying

end SSet.Marked
