/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeNormalForms
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicialMaps

/-!
# Actual canonical original cells of the right-cube quotient

Each genuine quotient class has its unique whole reduced original path
chain. The actual inverse projects that same chain. Scalar restriction
and outer right-join maps are followed by the proved reduction, retaining
all original cell data without assuming unreduced strict naturality.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeCanonicalCells
open PathLastMaximum RightCubeRelations RightCubeReduction RightCubeNormalForms
variable {n m : ℕ}

/-- Whole original reduced scalar chains, at the same original structural zero and last endpoints. -/
def Cells (n : ℕ) (q : SimplexCategoryᵒᵖ) :=
  {p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q // normalize p = p}

/-- The genuine canonical representative equivalence of the actual original cube quotient. -/
def equiv (n : ℕ) (q : SimplexCategoryᵒᵖ) : (RightCubeRelations.object.{u} n).obj q ≃ Cells.{u} n q where
  toFun := _root_.Quotient.lift (fun p => ⟨normalize p, normalize_idempotent p⟩)
    (fun _ _ h => Subtype.ext (setoid_normalize h))
  invFun p := _root_.Quotient.mk (setoid.{u} n q) p.1
  left_inv a := by
    induction a using _root_.Quotient.inductionOn with
    | _ p => exact _root_.Quotient.sound (Relation.EqvGen.symm _ _ (related_normalize p))
  right_inv p := Subtype.ext p.2

/-- Canonical readback of an actual original scalar representative is exactly its proved whole reduction. -/
theorem equiv_mk (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    (equiv n q (_root_.Quotient.mk _ p)).1 = normalize p := rfl

/-- The actual inverse canonical readback projects the same original reduced whole chain. -/
theorem equiv_symm (n : ℕ) (q : SimplexCategoryᵒᵖ) (p : Cells.{u} n q) :
    (equiv n q).symm p = _root_.Quotient.mk _ p.1 := rfl

/-- Original quotient representatives have the same class exactly when their whole canonical reductions are equal. -/
theorem mk_eq_iff (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (p r : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    (_root_.Quotient.mk (setoid.{u} n q) p = _root_.Quotient.mk _ r) ↔ normalize p = normalize r := by
  constructor
  · intro h
    exact setoid_normalize (_root_.Quotient.exact h)
  · intro h
    exact _root_.Quotient.sound ((setoid_iff_normalize_eq p r).mpr h)

/-- Every scalar operator reads the same actual restricted original chain followed by its proved
  first-maximum reduction. -/
theorem scalar_read {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) (a : (RightCubeRelations.object.{u} n).obj q) :
    (equiv n r ((RightCubeRelations.object n).map θ a)).1 =
      normalize ((nerve (LastPath.{u} (0 : Fin (n + 1)))).map θ (equiv n q a).1) := by
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact setoid_normalize (setoid_operator θ (related_normalize p))

/-- Every outer right-join operator reads the same actual original path image and zero insertion followed by
  canonical reduction. -/
theorem outer_read (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) {q : SimplexCategoryᵒᵖ}
    (a : (RightCubeRelations.object.{u} n).obj q) :
    (equiv m q ((RightCubeCosimplicialMaps.map θ).app q a)).1 =
      normalize ((equiv n q a).1 ⋙ RightCubeOperator.functor θ) := by
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact setoid_normalize (RightCubeCosimplicialMaps.compatible θ (related_normalize p))

end CategoryTheory.CoherentRealization.RightCubeCanonicalCells
