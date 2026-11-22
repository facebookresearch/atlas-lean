/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RightFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Endpoint-preserving lifting for the original interval and triangle

The interval source lifts through a left fibration, and the interval target
through a right fibration. Two such lifts fill a triangle from either of
its edges containing that endpoint. Each statement retains the supplied
whole bottom simplex and the original top edge.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet

/-- The actual interval source inclusion lifts through every left fibration. -/
theorem LeftFibration.hasLiftingProperty_source {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] : HasLiftingProperty (stdSimplex.δ.{u} (1 : Fin 2)) p := by
  refine ⟨fun {a b} sq => ?_⟩
  have hcompat : horn.IsCompatible (fun (j : Fin 2) (_ : j ≠ 0) => a) := by
    rw [horn.isCompatible_zero_iff_true]
    trivial
  have hcomm : ∀ (j : Fin 2) (hj : j ≠ 0), a ≫ p = stdSimplex.δ j ≫ b := by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact sq.w
  obtain ⟨l, hl, hp⟩ := exists_simplex_lift_horn hcompat
    (LeftFibration.hasLiftingProperty_horn (by decide : (0 : Fin 2) < Fin.last 1)) b hcomm
  exact CommSq.HasLift.mk' ⟨l, hl 1 (by decide), hp⟩

/-- The actual interval target inclusion lifts through every right fibration. -/
theorem RightFibration.hasLiftingProperty_target {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] : HasLiftingProperty (stdSimplex.δ.{u} (0 : Fin 2)) p := by
  refine ⟨fun {a b} sq => ?_⟩
  have hcompat : horn.IsCompatible (fun (j : Fin 2) (_ : j ≠ 1) => a) := by
    rw [horn.isCompatible_zero_iff_true]
    trivial
  have hcomm : ∀ (j : Fin 2) (hj : j ≠ 1), a ≫ p = stdSimplex.δ j ≫ b := by
    intro j hj
    fin_cases j
    · exact sq.w
    · exact (hj rfl).elim
  obtain ⟨l, hl, hp⟩ := exists_simplex_lift_horn hcompat
    (RightFibration.hasLiftingProperty_horn (1 : Fin 2) (by decide)) b hcomm
  exact CommSq.HasLift.mk' ⟨l, hl 0 (by decide), hp⟩

private theorem triangle_source_face_identity :
    stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
  exact (CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm

private theorem triangle_target_face_identity :
    stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
  exact CosimplicialObject.δ_comp_δ (SSet.stdSimplex.{u})
    (n := 0) (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)

private theorem LeftFibration.triangle_lift {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (a₀₁ a₀₂ : (Δ[1] : SSet.{u}) ⟶ X)
    (b : (Δ[2] : SSet.{u}) ⟶ B)
    (h : stdSimplex.δ (1 : Fin 2) ≫ a₀₁ = stdSimplex.δ (1 : Fin 2) ≫ a₀₂)
    (h₀₁ : a₀₁ ≫ p = stdSimplex.δ (2 : Fin 3) ≫ b)
    (h₀₂ : a₀₂ ≫ p = stdSimplex.δ (1 : Fin 3) ≫ b) :
    ∃ l : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ l = a₀₁ ∧
      stdSimplex.δ (1 : Fin 3) ≫ l = a₀₂ ∧ l ≫ p = b := by
  obtain ⟨a, ha₀₁, ha₀₂⟩ := horn₂₀.isPushout.exists_desc a₀₁ a₀₂ h
  have hsquare : a ≫ p = (horn 2 (0 : Fin 3)).ι ≫ b := by
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ha₀₁, ← Category.assoc,
        horn.ι_ι (0 : Fin 3) (2 : Fin 3) (by decide)]
      exact h₀₁
    · rw [← Category.assoc, ha₀₂, ← Category.assoc,
        horn.ι_ι (0 : Fin 3) (1 : Fin 3) (by decide)]
      exact h₀₂
  let _ : HasLiftingProperty (horn 2 (0 : Fin 3)).ι p :=
    LeftFibration.hasLiftingProperty_horn (by decide : (0 : Fin 3) < Fin.last 2)
  let sq : CommSq a (horn 2 (0 : Fin 3)).ι p b := ⟨hsquare⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← horn.ι_ι (0 : Fin 3) (2 : Fin 3) (by decide), Category.assoc,
      sq.fac_left]
    exact ha₀₁
  · rw [← horn.ι_ι (0 : Fin 3) (1 : Fin 3) (by decide), Category.assoc,
      sq.fac_left]
    exact ha₀₂

private theorem RightFibration.triangle_lift {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] (a₀₂ a₁₂ : (Δ[1] : SSet.{u}) ⟶ X)
    (b : (Δ[2] : SSet.{u}) ⟶ B)
    (h : stdSimplex.δ (0 : Fin 2) ≫ a₀₂ = stdSimplex.δ (0 : Fin 2) ≫ a₁₂)
    (h₀₂ : a₀₂ ≫ p = stdSimplex.δ (1 : Fin 3) ≫ b)
    (h₁₂ : a₁₂ ≫ p = stdSimplex.δ (0 : Fin 3) ≫ b) :
    ∃ l : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (1 : Fin 3) ≫ l = a₀₂ ∧
      stdSimplex.δ (0 : Fin 3) ≫ l = a₁₂ ∧ l ≫ p = b := by
  obtain ⟨a, ha₀₂, ha₁₂⟩ := horn₂₂.isPushout.exists_desc a₀₂ a₁₂ h
  have hi₀₂ : horn₂₂.ι₀₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (1 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (1 : Fin 3) (by decide)
  have hi₁₂ : horn₂₂.ι₁₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (0 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (0 : Fin 3) (by decide)
  have hsquare : a ≫ p = (horn 2 (Fin.last 2)).ι ≫ b := by
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, ha₀₂, ← Category.assoc,
        hi₀₂]
      exact h₀₂
    · rw [← Category.assoc, ha₁₂, ← Category.assoc,
        hi₁₂]
      exact h₁₂
  let _ : HasLiftingProperty (horn 2 (Fin.last 2)).ι p :=
    RightFibration.hasLiftingProperty_horn (Fin.last 2) (by decide)
  let sq : CommSq a (horn 2 (Fin.last 2)).ι p b := ⟨hsquare⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← horn.ι_ι (Fin.last 2) (1 : Fin 3) (by decide), Category.assoc,
      sq.fac_left]
    exact ha₀₂
  · rw [← horn.ι_ι (Fin.last 2) (0 : Fin 3) (by decide), Category.assoc,
      sq.fac_left]
    exact ha₁₂

/-- Either original edge containing the initial vertex extends through a left fibration. -/
theorem LeftFibration.hasLiftingProperty_triangleFace {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (i : Fin 3) (hi : i ≠ 0) :
    HasLiftingProperty (stdSimplex.δ.{u} i) p := by
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨fun {a b} sq => ?_⟩
    change CommSq a (stdSimplex.δ (1 : Fin 3)) p b at sq
    let _ : HasLiftingProperty (stdSimplex.δ.{u} (1 : Fin 2)) p :=
      LeftFibration.hasLiftingProperty_source p
    have hs : CommSq (stdSimplex.δ (1 : Fin 2) ≫ a)
        (stdSimplex.δ (1 : Fin 2)) p (stdSimplex.δ (2 : Fin 3) ≫ b) := by
      constructor
      rw [Category.assoc, sq.w, ← Category.assoc, triangle_source_face_identity,
        Category.assoc]
    obtain ⟨l, _, hl, hp⟩ := LeftFibration.triangle_lift p hs.lift a b
      hs.fac_left hs.fac_right sq.w
    exact CommSq.HasLift.mk' ⟨l, hl, hp⟩
  · refine ⟨fun {a b} sq => ?_⟩
    change CommSq a (stdSimplex.δ (2 : Fin 3)) p b at sq
    let _ : HasLiftingProperty (stdSimplex.δ.{u} (1 : Fin 2)) p :=
      LeftFibration.hasLiftingProperty_source p
    have hs : CommSq (stdSimplex.δ (1 : Fin 2) ≫ a)
        (stdSimplex.δ (1 : Fin 2)) p (stdSimplex.δ (1 : Fin 3) ≫ b) := by
      constructor
      rw [Category.assoc, sq.w, ← Category.assoc, ← triangle_source_face_identity,
        Category.assoc]
    obtain ⟨l, hl, _, hp⟩ := LeftFibration.triangle_lift p a hs.lift b
      hs.fac_left.symm sq.w hs.fac_right
    exact CommSq.HasLift.mk' ⟨l, hl, hp⟩

/-- Either original edge containing the terminal vertex extends through a right fibration. -/
theorem RightFibration.hasLiftingProperty_triangleFace {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] (i : Fin 3) (hi : i ≠ 2) :
    HasLiftingProperty (stdSimplex.δ.{u} i) p := by
  fin_cases i
  · refine ⟨fun {a b} sq => ?_⟩
    change CommSq a (stdSimplex.δ (0 : Fin 3)) p b at sq
    let _ : HasLiftingProperty (stdSimplex.δ.{u} (0 : Fin 2)) p :=
      RightFibration.hasLiftingProperty_target p
    have ht : CommSq (stdSimplex.δ (0 : Fin 2) ≫ a)
        (stdSimplex.δ (0 : Fin 2)) p (stdSimplex.δ (1 : Fin 3) ≫ b) := by
      constructor
      rw [Category.assoc, sq.w, ← Category.assoc, ← triangle_target_face_identity,
        Category.assoc]
    obtain ⟨l, _, hl, hp⟩ := RightFibration.triangle_lift p ht.lift a b
      ht.fac_left ht.fac_right sq.w
    exact CommSq.HasLift.mk' ⟨l, hl, hp⟩
  · refine ⟨fun {a b} sq => ?_⟩
    change CommSq a (stdSimplex.δ (1 : Fin 3)) p b at sq
    let _ : HasLiftingProperty (stdSimplex.δ.{u} (0 : Fin 2)) p :=
      RightFibration.hasLiftingProperty_target p
    have ht : CommSq (stdSimplex.δ (0 : Fin 2) ≫ a)
        (stdSimplex.δ (0 : Fin 2)) p (stdSimplex.δ (0 : Fin 3) ≫ b) := by
      constructor
      rw [Category.assoc, sq.w, ← Category.assoc, triangle_target_face_identity,
        Category.assoc]
    obtain ⟨l, hl, _, hp⟩ := RightFibration.triangle_lift p a ht.lift b
      ht.fac_left.symm sq.w ht.fac_right
    exact CommSq.HasLift.mk' ⟨l, hl, hp⟩
  · exact (hi rfl).elim

/-- The interval source is in the generated left horn class. -/
theorem leftHorn_llp_source : leftHornInclusions.rlp.llp
    (stdSimplex.δ.{u} (1 : Fin 2)) := by
  intro X B p hp
  let _ : LeftFibration p := ⟨hp⟩
  exact LeftFibration.hasLiftingProperty_source p

/-- Every initial-vertex-containing triangle edge is in the generated left horn class. -/
theorem leftHorn_llp_triangleFace (i : Fin 3) (hi : i ≠ 0) :
    leftHornInclusions.rlp.llp (stdSimplex.δ.{u} i) := by
  intro X B p hp
  let _ : LeftFibration p := ⟨hp⟩
  exact LeftFibration.hasLiftingProperty_triangleFace p i hi

/-- The interval target is in the generated right horn class. -/
theorem rightHorn_llp_target : rightHornInclusions.rlp.llp
    (stdSimplex.δ.{u} (0 : Fin 2)) := by
  intro X B p hp
  let _ : RightFibration p := rightFibration_of_mem_rightFibrations hp
  exact RightFibration.hasLiftingProperty_target p

/-- Every terminal-vertex-containing triangle edge is in the generated right horn class. -/
theorem rightHorn_llp_triangleFace (i : Fin 3) (hi : i ≠ 2) :
    rightHornInclusions.rlp.llp (stdSimplex.δ.{u} i) := by
  intro X B p hp
  let _ : RightFibration p := rightFibration_of_mem_rightFibrations hp
  exact RightFibration.hasLiftingProperty_triangleFace p i hi

end SSet
