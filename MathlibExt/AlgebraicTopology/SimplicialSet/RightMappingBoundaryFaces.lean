/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW

/-!
# Whole boundary faces in the original right mapping space

A compatible boundary in the genuine right mapping object becomes a
compatible boundary one degree higher in the original target, by adding
the constant source face. Every other face retains the original join
simplex and the same target vertex. This is a literal boundary statement,
with no fibrancy, mapping-weakness or extension outcome premise.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.mappingSpaceRight
variable {X : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The original target simplex represented by one supplied right-mapping boundary face. -/
def boundaryFace {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (j : Fin (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ X :=
  ((simplexEquivSucc X x y n) (yonedaEquiv (faces j))).val

/-- Each original transported face has exactly the constant supplied source boundary. -/
theorem boundaryFace_source {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (j : Fin (n + 2)) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ boundaryFace x y faces j =
      toDeltaZero (Δ[n] : SSet.{u}) ≫ x := by
  rw [← frontInclusion_eq]
  exact ((simplexEquivSucc X x y n) (yonedaEquiv (faces j))).2.1

/-- Each transported face retains that same individual original target vertex. -/
theorem boundaryFace_target {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (j : Fin (n + 2)) : rightVertex n ≫ boundaryFace x y faces j = y :=
  ((simplexEquivSucc X x y n) (yonedaEquiv (faces j))).2.2

private theorem yonedaFace {T : SSet.{u}} {n : ℕ}
    (a : Fin (n + 2)) (φ : (Δ[n + 1] : SSet.{u}) ⟶ T) :
    T.δ a (yonedaEquiv φ) = yonedaEquiv (stdSimplex.δ a ≫ φ) :=
  yonedaEquiv_naturality (SimplexCategory.δ a) φ

private theorem boundaryFace_pair {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (hf : boundary.IsCompatible faces) (j k : Fin (n + 2)) (hjk : j < k) :
    stdSimplex.δ (k.castSucc.pred (Fin.ne_zero_of_lt (Fin.castSucc_lt_castSucc_iff.mpr hjk))) ≫
        boundaryFace x y faces j =
      stdSimplex.δ (j.castSucc.castPred (Fin.ne_last_of_lt
        (Fin.castSucc_lt_castSucc_iff.mpr hjk))) ≫ boundaryFace x y faces k := by
  obtain _ | n := n
  · have hj0 : j = (0 : Fin 2) := by
      apply Fin.ext
      change j.val = 0
      omega
    have hk1 : k = (1 : Fin 2) := by
      apply Fin.ext
      change k.val = 1
      omega
    subst j
    subst k
    change stdSimplex.δ (0 : Fin 2) ≫ boundaryFace x y faces 0 =
      stdSimplex.δ (0 : Fin 2) ≫ boundaryFace x y faces 1
    rw [← rightVertex_zero, boundaryFace_target, boundaryFace_target]
  · have hidx : j.castSucc.castPred (Fin.ne_last_of_lt
        (Fin.castSucc_lt_castSucc_iff.mpr hjk)) =
        (j.castPred (Fin.ne_last_of_lt hjk)).castSucc := by
      ext
      simp only [Fin.coe_castPred, Fin.val_castSucc]
    rw [← Fin.castSucc_pred_eq_pred_castSucc (Fin.ne_zero_of_lt hjk), hidx]
    change stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)).castSucc ≫
        ((simplexEquivSucc X x y (n + 1)) (yonedaEquiv (faces j))).val =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)).castSucc ≫
        ((simplexEquivSucc X x y (n + 1)) (yonedaEquiv (faces k))).val
    rw [← simplexEquivSucc_δ x y (yonedaEquiv (faces j)),
      ← simplexEquivSucc_δ x y (yonedaEquiv (faces k)), yonedaFace, yonedaFace]
    exact congrArg (fun φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y =>
        ((simplexEquivSucc X x y n) (yonedaEquiv φ)).val)
      ((boundary.isCompatible_succ_iff faces).mp hf j k hjk)

/-- Add only the original constant source face to all the actual supplied mapping-space boundary faces. -/
def augmentedFaces {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y)) :
    Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X) :=
  fun j => if hj : j = Fin.last (n + 2) then toDeltaZero Δ[n + 1] ≫ x
    else boundaryFace x y faces (j.castPred hj)

/-- Every supplied original face is preserved at its actual shifted boundary index. -/
theorem augmentedFaces_castSucc {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (j : Fin (n + 2)) : augmentedFaces x y faces j.castSucc = boundaryFace x y faces j :=
  dite_eq_right (Fin.ne_last_of_lt (Fin.castSucc_lt_last j))

/-- The only added face is the literal constant simplex at the supplied original source vertex. -/
theorem augmentedFaces_last {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y)) :
    augmentedFaces x y faces (Fin.last (n + 2)) = toDeltaZero Δ[n + 1] ≫ x :=
  dite_eq_left rfl

/-- Compatibility of the supplied whole mapping-space boundary proves compatibility of the actual augmented
  boundary in the original target. -/
theorem augmentedFaces_isCompatible {n : ℕ}
    (faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ mappingSpaceRight X x y))
    (hf : boundary.IsCompatible faces) : boundary.IsCompatible (augmentedFaces x y faces) := by
  rw [boundary.isCompatible_succ_iff]
  intro j k hjk
  by_cases hk : k = Fin.last (n + 2)
  · subst k
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    rw [augmentedFaces_castSucc, augmentedFaces_last, Fin.pred_last,
      Fin.castPred_castSucc, boundaryFace_source]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ x) (toDeltaZero_eq
        (stdSimplex.δ j ≫ toDeltaZero (Δ[n + 1] : SSet.{u}))))).symm
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_castSucc_of_ne_last hk
    rw [augmentedFaces_castSucc, augmentedFaces_castSucc]
    exact boundaryFace_pair x y faces hf j k (Fin.castSucc_lt_castSucc_iff.mp hjk)

end SSet.mappingSpaceRight
