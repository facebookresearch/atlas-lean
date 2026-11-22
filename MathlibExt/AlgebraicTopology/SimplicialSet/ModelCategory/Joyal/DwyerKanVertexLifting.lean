/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Functor.IsofibrationEssentialSurjectivity
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan

/-!
# Strict original vertex lifting from genuine categorical fibrancy

Essential surjectivity of the actual ordinary homotopy-category functor,
together with the proved isofibration classifier, supplies literal
surjectivity of original vertices. Precomposition does not add an
object-class quotient or strengthen the target hypotheses.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet
variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Essential surjectivity of the same original composite implies essential surjectivity of its last map. -/
theorem dwyerKanEssentiallySurjective.of_precomp
    (h : dwyerKanEssentiallySurjective (f ≫ g)) : dwyerKanEssentiallySurjective g := by
  have hcomp : mapHomotopyCategory (f ≫ g) =
      mapHomotopyCategory f ⋙ mapHomotopyCategory g := by
    have hrw : ∀ {A B : SSet.{u}} (p : A ⟶ B),
        mapHomotopyCategory p = (hoFunctor.map p).toFunctor := fun _ => rfl
    rw [hrw, hrw, hrw, hoFunctor.map_comp]
    rfl
  change (mapHomotopyCategory (f ≫ g)).EssSurj at h
  rw [hcomp] at h
  let _ := h
  refine ⟨fun z => ?_⟩
  obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (mapHomotopyCategory f ⋙ mapHomotopyCategory g) z
  exact ⟨(mapHomotopyCategory f).obj x, ⟨e⟩⟩

/-- A genuine categorical fibration into a quasicategory which is essentially surjective lifts every
  individual original vertex strictly. -/
theorem categoricalFibrations.surjective_vertices_of_essSurj {p : X ⟶ Y}
    [Quasicategory Y] (hp : categoricalFibrations p)
    (hES : dwyerKanEssentiallySurjective p) : Function.Surjective (p.app (op ⦋0⦌)) := by
  have hLift := ((categoricalFibrations_iff_innerFibration_and_hoIsofibration p).mp hp).2
  change (mapHomotopyCategory p).IsIsofibration at hLift
  let _ := hLift
  let _ : (mapHomotopyCategory p).EssSurj := hES
  intro y
  obtain ⟨a, ha⟩ := (mapHomotopyCategory p).surjective_obj_of_isIsofibration
    (HomotopyCategory.mk y)
  cases a using HomotopyCategory.rec with
  | mk x =>
    exact ⟨x, congrArg (HomotopyCategory.objEquiv (X := Y)) ha⟩

end SSet
