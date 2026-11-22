/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorFibre

/-!
# The actual original triangle of a Segal path simplex operator

The original shifted simplex contains its source object, first tail
vertex and the image of the operator's first vertex. Restriction to
that whole triangle retains the old leading edge, new leading edge
and the actual tail edge from zero to f(0), even when those vertices coincide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original tail edge from zero to the actual operator image of zero. -/
def operatorInitialEdge {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.mk 1 ⟶ SimplexCategory.mk n :=
  SimplexCategory.mkOfLe 0 (f.toOrderHom 0) (Fin.zero_le _)

/-- The original three-vertex triangle retaining the old and new leading edges of the shifted row. -/
def operatorTriangle {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.mk 2 ⟶ SimplexCategory.mk (n + 1) :=
  SimplexCategory.Hom.mk
    { toFun := Fin.cases 0 (Fin.cases 1 (fun _ => (f.toOrderHom 0).succ))
      monotone' := by
        rw [Fin.monotone_iff_le_succ]
        intro i
        fin_cases i
        · exact Fin.zero_le _
        · change (0 : ℕ) + 1 ≤ (f.toOrderHom 0).val + 1
          omega }

/-- The first original triangle edge is the same actual old leading edge. -/
theorem operatorTriangle_first {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.δ (2 : Fin 3) ≫ operatorTriangle f =
      SimplexCategory.mkOfSucc (0 : Fin (n + 1)) := by
  ext i
  fin_cases i <;> rfl

/-- The original triangle middle edge is precisely the new original leading edge after the whole operator. -/
theorem operatorTriangle_middle {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.δ (1 : Fin 3) ≫ operatorTriangle f =
      SimplexCategory.mkOfSucc (0 : Fin (m + 1)) ≫
        CategoryTheory.SimplicialObject.LeftDecalage.ordinal.map f := by
  ext i
  fin_cases i <;> rfl

/-- The original triangle last edge is the actual operator initial edge inside the same full tail. -/
theorem operatorTriangle_last {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.δ (0 : Fin 3) ≫ operatorTriangle f =
      operatorInitialEdge f ≫ SimplexCategory.δ (0 : Fin (n + 2)) := by
  ext i
  fin_cases i <;> rfl

end SimplicialSpace.LeftDecalageObject
