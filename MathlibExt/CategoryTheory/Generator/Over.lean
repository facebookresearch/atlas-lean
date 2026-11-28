/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Generator.StrongGenerator
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Strong generators with their original maps to a fixed base

A generating family lifts to the slice by retaining every actual map from
each generator to the base. Tests in this family are precisely the original
tests with their forced base triangle. A strong generator remains strong,
and local smallness makes the indexing family small in the same universe.
-/

noncomputable section
universe w v u t
open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {ι : Type t} (G : ι → C) (S : C)

/-- Retain every actual generator-to-base map as its original slice object. -/
def overGeneratorObj : (Σ i, G i ⟶ S) → Over S := fun i => Over.mk i.2

/-- The actual image family of generators with all their original base maps. -/
def overGenerator : ObjectProperty (Over S) := ObjectProperty.ofObj (overGeneratorObj G S)

/-- Small generator labels and native small Hom sets give small slice labels at the same bound. -/
theorem overGenerator_small [Small.{w} ι] [LocallySmall.{w} C] :
    ObjectProperty.Small.{w} (overGenerator G S) := by
  change ObjectProperty.Small.{w} (ObjectProperty.ofObj (overGeneratorObj G S))
  infer_instance

/-- Every original map from a generator occurs literally in the slice family. -/
theorem overGenerator_mk (i : ι) (a : G i ⟶ S) : overGenerator G S (Over.mk a) :=
  ObjectProperty.ofObj.mk (X := overGeneratorObj G S) ⟨i, a⟩

/-- Separating the underlying original maps separates their slice maps. -/
theorem overGenerator_isSeparating (hG : (ObjectProperty.ofObj G).IsSeparating) :
    (overGenerator G S).IsSeparating := by
  intro X Y f g h
  apply Over.OverMorphism.ext
  apply hG f.left g.left
  rintro T ⟨i⟩ a
  let q : Over.mk (a ≫ X.hom) ⟶ X := Over.homMk a rfl
  exact congrArg Over.Hom.left (h _ (overGenerator_mk G S i (a ≫ X.hom)) q)

/-- Strong generator lifting in the slice detects the underlying original isomorphism. -/
theorem overGenerator_isStrongGenerator (hG : (ObjectProperty.ofObj G).IsStrongGenerator) :
    (overGenerator G S).IsStrongGenerator := by
  apply ObjectProperty.isStrongGenerator_iff.mpr
  refine ⟨overGenerator_isSeparating G S hG.isSeparating, ?_⟩
  intro X Y f _ h
  let _ : Mono f.left := Over.mono_left_of_mono f
  let _ : IsIso f.left := hG.isIso_of_mono f.left (by
    rintro T ⟨i⟩ a
    let q : Over.mk (a ≫ Y.hom) ⟶ Y := Over.homMk a rfl
    obtain ⟨b, hb⟩ := h _ (overGenerator_mk G S i (a ≫ Y.hom)) q
    exact ⟨b.left, congrArg Over.Hom.left hb⟩)
  let e : X ≅ Y := Over.isoMk (asIso f.left) (Over.w f)
  have he : e.hom = f := Over.OverMorphism.ext rfl
  exact he ▸ e.isIso_hom

end CategoryTheory
