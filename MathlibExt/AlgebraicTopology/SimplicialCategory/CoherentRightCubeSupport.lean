/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCanonicalCells

/-!
# Actual retained front support of original right-cube cells

The retained support is the original last path's front labels at or
above the actual first maximum. It is nonempty, unchanged by the proved
normalization, and only decreases under scalar restriction. Thus it is
well defined on the genuine original quotient classes.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeSupport
open PathLastMaximum RightCubeRelations RightCubeReduction RightCubeNormalForms
variable {n : ℕ}

/-- The actual retained original front labels, including the original first maximum and excluding merely
  adjoined structural zero. -/
def support {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : Set (Fin (n + 1)) :=
  {j | ULift.up.{u} j.castSucc ∈ (p.obj (Fin.last q.unop.len)).I ∧ initialMaximum p ≤ j}

/-- The same individual original first maximum belongs to the retained support. -/
theorem initialMaximum_support {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : initialMaximum p ∈ support p :=
  ⟨initialMaximum_mem p (Fin.last q.unop.len), le_rfl⟩

/-- The original retained support is nonempty in every resolving and scalar degree. -/
theorem support_nonempty {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : (support p).Nonempty :=
  ⟨initialMaximum p, initialMaximum_support p⟩

/-- Whole canonical reduction retains precisely the same original front support. -/
theorem normalize_support {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : support (normalize p) = support p := by
  ext j
  change (ULift.up.{u} j.castSucc ∈ ((normalize p).obj (Fin.last q.unop.len)).I ∧ initialMaximum (normalize p) ≤ j) ↔
    (ULift.up.{u} j.castSucc ∈ (p.obj (Fin.last q.unop.len)).I ∧ initialMaximum p ≤ j)
  rw [normalize_initialMaximum]
  change (((ULift.up.{u} j.castSucc = ULift.up.{u} (0 : Fin (n + 2))) ∨
    (ULift.up.{u} j.castSucc ∈ (p.obj (Fin.last q.unop.len)).I ∧ initialMaximum p ≤ j)) ∧ initialMaximum p ≤ j) ↔ _
  constructor
  · rintro ⟨h₀ | hp, hj⟩
    · have hDown : j.castSucc = (0 : Fin (n + 1)).castSucc := congrArg ULift.down h₀
      have h : j = 0 := Fin.castSucc_injective _ hDown
      subst j
      exact ⟨(p.obj (Fin.last q.unop.len)).left, hj⟩
    · exact hp
  · intro hp
    exact ⟨Or.inr hp, hp.2⟩

/-- Equality of the proved original canonical chains retains the same actual front support. -/
theorem support_of_normalize_eq {q : SimplexCategoryᵒᵖ}
    {p r : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : normalize p = normalize r) : support p = support r :=
  (normalize_support p).symm.trans ((congrArg support h).trans (normalize_support r))

/-- The actual retained original front support of a genuine cube quotient class. -/
def quotientSupport {q : SimplexCategoryᵒᵖ} (a : (RightCubeRelations.object.{u} n).obj q) : Set (Fin (n + 1)) :=
  _root_.Quotient.lift support (fun _ _ h => support_of_normalize_eq (setoid_normalize h)) a

/-- The actual quotient support reads the same whole original representative support. -/
theorem quotientSupport_mk {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) : quotientSupport (_root_.Quotient.mk _ p) = support p := rfl

/-- Every actual original quotient cell has nonempty retained front support, including resolving degree zero. -/
theorem quotientSupport_nonempty {q : SimplexCategoryᵒᵖ} (a : (RightCubeRelations.object.{u} n).obj q) :
    (quotientSupport a).Nonempty := by
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact support_nonempty p

/-- Scalar restriction retains a subset of the same original front support. -/
theorem support_scalar_subset {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    support ((nerve (LastPath.{u} (0 : Fin (n + 1)))).map θ p) ⊆ support p := by
  intro j hj
  have hi : initialMaximum p ≤ initialMaximum ((nerve (LastPath.{u} (0 : Fin (n + 1)))).map θ p) :=
    maximum_mono 0 (p.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))
  exact ⟨(p.map (homOfLE (Fin.le_last (θ.unop.toOrderHom (Fin.last r.unop.len))))).hom.down.down hj.1,
    le_trans hi hj.2⟩

/-- Every actual quotient scalar operator retains a subset of the same original front support. -/
theorem quotientSupport_scalar_subset {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (a : (RightCubeRelations.object.{u} n).obj q) : quotientSupport ((RightCubeRelations.object n).map θ a)
      ⊆ quotientSupport a := by
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact support_scalar_subset θ p

end CategoryTheory.CoherentRealization.RightCubeSupport
