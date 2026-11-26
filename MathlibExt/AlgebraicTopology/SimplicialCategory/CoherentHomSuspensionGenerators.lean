/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeUniversalProperty
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory

/-!
# Actual two-object suspension generators of an original simplicial set

The original left and right labels are distinct. The supplied simplicial
set is the sole generating Hom from left to right; every other generating
Hom is empty. Its actual free enriched category retains these labels and
every original generating cell, without an enriched-model hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomSuspensionGenerators
open SimplicialEnrichment SimplicialQuiver

/-- The two original suspension object labels at the same original Hom universe. -/
abbrev Objects := ULift.{u} (Fin 2)

/-- The original source label of the simplicial suspension. -/
def left : Objects.{u} := ULift.up 0

/-- The original target label of the simplicial suspension. -/
def right : Objects.{u} := ULift.up 1

/-- The two supplied original suspension labels are distinct. -/
theorem left_ne_right : left.{u} ≠ right := by
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)

/-- The actual empty original generating simplicial set, with no cell in any scalar degree. -/
abbrev empty : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

/-- The original scalar-generating quiver, with the supplied simplicial set only in the
actual left-to-right Hom. -/
def quiver (K : SSet.{u}) : SimplicialQuiver.Data Objects.{u} where
  Hom a b := if a = left ∧ b = right then K else empty.{u}

/-- The supplied original simplicial set is exactly the actual forward generating Hom. -/
theorem quiver_forward (K : SSet.{u}) : (quiver K).Hom left right = K := by
  simp only [quiver, and_self, ite_true]

/-- Every other original generating Hom is genuinely empty. -/
theorem quiver_other (K : SSet.{u}) (a b : Objects.{u}) (h : ¬(a = left ∧ b = right)) :
    (quiver K).Hom a b = empty.{u} := by
  simp only [quiver, ite_eq_right h]

/-- The actual free enriched suspension carrier, preserving both original object labels and
whole original
  generating paths. -/
def carrier (K : SSet.{u}) : Carrier.{u} :=
  SimplicialQuiver.free (quiver K)

/-- Every actual generating cell retains the supplied original source and target labels. -/
theorem generator_endpoints (K : SSet.{u}) {n : SimplexCategoryᵒᵖ} {a b : Objects.{u}}
    (x : ((quiver K).Hom a b).obj n) : a = left ∧ b = right := by
  classical
  by_contra h
  have hK := quiver_other K a b h
  have hEmpty : IsEmpty (((quiver K).Hom a b).obj n) := by
    rw [hK]
    change IsEmpty PEmpty.{u + 1}
    infer_instance
  exact hEmpty.false x

/-- No supplied original generator leaves the original right label. -/
theorem no_generator_from_right (K : SSet.{u}) {n : SimplexCategoryᵒᵖ} {b : Objects.{u}}
    (x : ((quiver K).Hom right b).obj n) : False :=
  left_ne_right (generator_endpoints K x).1.symm

/-- No supplied original generator enters the original left label. -/
theorem no_generator_to_left (K : SSet.{u}) {n : SimplexCategoryᵒᵖ} {a : Objects.{u}}
    (x : ((quiver K).Hom a left).obj n) : False :=
  left_ne_right (generator_endpoints K x).2

/-- Every actual free path ending at the original left label is its original empty path,
with exact original
  starting-label equality. -/
theorem path_to_left (K : SSet.{u}) {n : SimplexCategoryᵒᵖ} {a : Objects.{u}}
    (p : SimplicialQuiver.Path (quiver K) n a left) : a = left := by
  let _ : Quiver Objects.{u} := SimplicialQuiver.quiverAt (quiver K) n
  cases p with
  | nil => rfl
  | cons p x => exact False.elim (no_generator_to_left K x)

/-- An actual free path on the left label is the original empty path. -/
theorem path_left_left (K : SSet.{u}) {n : SimplexCategoryᵒᵖ}
    (p : SimplicialQuiver.Path (quiver K) n left left) : p = @Quiver.Path.nil Objects.{u}
      (SimplicialQuiver.quiverAt (quiver K) n) left := by
  let _ : Quiver Objects.{u} := SimplicialQuiver.quiverAt (quiver K) n
  cases p with
  | nil => rfl
  | cons p x => exact False.elim (no_generator_to_left K x)

/-- Every actual forward free path is precisely one supplied original generating cell. -/
theorem path_forward (K : SSet.{u}) {n : SimplexCategoryᵒᵖ}
    (p : SimplicialQuiver.Path (quiver K) n left right) :
    ∃ x : ((quiver K).Hom left right).obj n, p = @Quiver.Hom.toPath Objects.{u}
      (SimplicialQuiver.quiverAt
      (quiver K) n) left right x := by
  let _ : Quiver Objects.{u} := SimplicialQuiver.quiverAt (quiver K) n
  cases p with
  | @cons b c p x =>
    obtain ⟨hb, hc⟩ := generator_endpoints K x
    subst b
    have hp := path_left_left K p
    exact ⟨x, by rw [hp]; rfl⟩

end CategoryTheory.CoherentRealization.HomSuspensionGenerators
