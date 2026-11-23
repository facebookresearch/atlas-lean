/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.BinaryClosedGlue

@[expose] public section

/-!
# Binary closed-cover glue clients (KQ4, PR #3951)

Direct concrete clients of `TopCat.exists_continuousMap_glue_of_closed_cover`
and `TopCat.exists_lift_of_binary_closed_cover` over `TopCat.of PUnit` with
explicit closed covers (`univ`/`univ` and `univ`/`empty`). Each client builds
constant local maps and lifts, then asserts the returned restriction or triangle
equations so inference and orientation are exercised. No other gluing, model, or
realization claim.
-/

set_option autoImplicit false

open CategoryTheory TopCat

namespace MathlibExtTest.Topology.Category.TopCat.BinaryClosedGlueTests

/-- Glue over two equal `univ` pieces; asserts both restrictions. -/
theorem glue_univ_univ_restricts :
    ∃ F : ContinuousMap (TopCat.of PUnit.{1}) (TopCat.of PUnit.{1}),
      F.restrict (Set.univ : Set ↑(TopCat.of PUnit.{1})) =
        (⟨fun _ => (), continuous_const⟩ :
          ContinuousMap ↥(Set.univ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1})) ∧
      F.restrict (Set.univ : Set ↑(TopCat.of PUnit.{1})) =
        (⟨fun _ => (), continuous_const⟩ :
          ContinuousMap ↥(Set.univ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1})) := by
  exact TopCat.exists_continuousMap_glue_of_closed_cover isClosed_univ isClosed_univ
    (by simp) _ _ (fun x _ _ => Subsingleton.elim _ _)

/-- Glue over `univ`/`empty`; asserts both restrictions including the empty piece. -/
theorem glue_univ_empty_restricts :
    ∃ F : ContinuousMap (TopCat.of PUnit.{1}) (TopCat.of PUnit.{1}),
      F.restrict (Set.univ : Set ↑(TopCat.of PUnit.{1})) =
        (⟨fun _ => (), continuous_const⟩ :
          ContinuousMap ↥(Set.univ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1})) ∧
      F.restrict (∅ : Set ↑(TopCat.of PUnit.{1})) =
        (⟨fun _ => (), continuous_const⟩ :
          ContinuousMap ↥(∅ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1})) := by
  exact TopCat.exists_continuousMap_glue_of_closed_cover isClosed_univ isClosed_empty
    (by simp) _ _ (fun x _ hxt => absurd hxt (by simp))

/-- Lift over two equal `univ` pieces for the identity square; asserts both triangles. -/
theorem lift_univ_univ_triangles :
    ∃ l : (TopCat.of PUnit.{1}) ⟶ (TopCat.of PUnit.{1}),
      (𝟙 (TopCat.of PUnit.{1}) ≫ l = 𝟙 (TopCat.of PUnit.{1})) ∧
        (l ≫ 𝟙 (TopCat.of PUnit.{1}) = 𝟙 (TopCat.of PUnit.{1})) := by
  let sq : CommSq (𝟙 (TopCat.of PUnit.{1})) (𝟙 (TopCat.of PUnit.{1}))
    (𝟙 (TopCat.of PUnit.{1})) (𝟙 (TopCat.of PUnit.{1})) := ⟨by simp⟩
  let ls : ContinuousMap ↥(Set.univ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1}) :=
    ⟨fun _ => (), continuous_const⟩
  let lt : ContinuousMap ↥(Set.univ : Set ↑(TopCat.of PUnit.{1})) ↑(TopCat.of PUnit.{1}) :=
    ⟨fun _ => (), continuous_const⟩
  have hLift := TopCat.exists_lift_of_binary_closed_cover (f := 𝟙 (TopCat.of PUnit.{1}))
    (i := 𝟙 (TopCat.of PUnit.{1})) (p := 𝟙 (TopCat.of PUnit.{1})) (g := 𝟙 (TopCat.of PUnit.{1}))
    sq isClosed_univ isClosed_univ (by simp) ls lt
    (fun b _ _ => Subsingleton.elim _ _) (fun a _ => Subsingleton.elim _ _)
    (fun a _ => Subsingleton.elim _ _) (fun b _ => Subsingleton.elim _ _)
    (fun b _ => Subsingleton.elim _ _)
  rw [CommSq.HasLift.iff] at hLift
  obtain ⟨lStruct⟩ := hLift
  exact ⟨lStruct.l, lStruct.fac_left, lStruct.fac_right⟩

#print axioms glue_univ_univ_restricts
#print axioms glue_univ_empty_restricts
#print axioms lift_univ_univ_triangles

end MathlibExtTest.Topology.Category.TopCat.BinaryClosedGlueTests
