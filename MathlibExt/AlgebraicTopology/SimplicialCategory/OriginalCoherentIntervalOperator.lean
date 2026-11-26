/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadInterval

/-!
# Genuine restriction of every original ordinal operator to endpoint intervals

The actual original operator restricts to the SAME consecutive original
source and target intervals. Its whole square, endpoint equations and
vertex values are retained, including zero intervals and noninjective maps.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

variable {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (a b : Fin (n + 1)) (hab : a ≤ b)

/-- The SAME original operator restricted to the two full original endpoint intervals. -/
def intervalOperator : ⦋length a b⦌ ⟶ ⦋length (f.toOrderHom a) (f.toOrderHom b)⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨(f.toOrderHom (embedding a b hab i)).val - (f.toOrderHom a).val, by
        have hlo := f.toOrderHom.monotone ((embedding a b hab).monotone (Fin.zero_le i))
        have hhi := f.toOrderHom.monotone ((embedding a b hab).monotone (Fin.le_last i))
        rw [embedding_zero] at hlo
        rw [embedding_last] at hhi
        change (f.toOrderHom a).val ≤ (f.toOrderHom (embedding a b hab i)).val at hlo
        change (f.toOrderHom (embedding a b hab i)).val ≤ (f.toOrderHom b).val at hhi
        dsimp [length]
        omega⟩
      monotone' := fun i j hij => Nat.sub_le_sub_right
        (f.toOrderHom.monotone ((embedding a b hab).monotone hij)) _ }

/-- The full original interval operator has its exact first-endpoint equation. -/
theorem intervalOperator_zero : (intervalOperator f a b hab).toOrderHom 0 = 0 := by
  apply Fin.ext
  change (f.toOrderHom (embedding a b hab 0)).val - (f.toOrderHom a).val = 0
  rw [embedding_zero]
  exact Nat.sub_self _

/-- The full original interval operator has its exact last-endpoint equation. -/
theorem intervalOperator_last :
    (intervalOperator f a b hab).toOrderHom (Fin.last (length a b)) =
      Fin.last (length (f.toOrderHom a) (f.toOrderHom b)) := by
  apply Fin.ext
  change (f.toOrderHom (embedding a b hab (Fin.last (length a b)))).val - (f.toOrderHom a).val = _
  rw [embedding_last]
  rfl

/-- EVERY original interval vertex retains its exact original full-operator image. -/
theorem intervalOperator_vertex (i : Fin (length a b + 1)) :
    embedding (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)
      ((intervalOperator f a b hab).toOrderHom i) = f.toOrderHom (embedding a b hab i) := by
  apply Fin.ext
  change (f.toOrderHom a).val +
    ((f.toOrderHom (embedding a b hab i)).val - (f.toOrderHom a).val) =
      (f.toOrderHom (embedding a b hab i)).val
  have hlo := f.toOrderHom.monotone ((embedding a b hab).monotone (Fin.zero_le i))
  rw [embedding_zero] at hlo
  change (f.toOrderHom a).val ≤ (f.toOrderHom (embedding a b hab i)).val at hlo
  omega

/-- The SAME entire original interval square commutes as literal simplex-category maps. -/
theorem intervalOperator_square :
    intervalOperator f a b hab ≫ operator (f.toOrderHom a) (f.toOrderHom b)
      (f.toOrderHom.monotone hab) = operator a b hab ≫ f := by
  ext i : 3
  exact intervalOperator_vertex f a b hab i

end CategoryTheory.CoherentRealization.OriginalBeadInterval
