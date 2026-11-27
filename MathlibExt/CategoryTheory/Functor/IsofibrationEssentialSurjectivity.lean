/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Functor.Isofibration
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Essential surjectivity and strict object lifting

A genuine isofibration that is essentially surjective is surjective on
the original objects. The actual isomorphism lift supplies the strict
object equality; the object carrier is not replaced by isomorphism classes.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂
namespace CategoryTheory.Functor

/-- A genuine essentially surjective isofibration is surjective on its original objects. -/
theorem surjective_obj_of_isIsofibration {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [F.EssSurj] [F.IsIsofibration] :
    Function.Surjective F.obj := by
  intro Y
  obtain ⟨X, ⟨e⟩⟩ := EssSurj.mem_essImage F Y
  obtain ⟨Y', f, h, hf⟩ := F.exists_iso_lift e
  exact ⟨Y', h⟩

end CategoryTheory.Functor
