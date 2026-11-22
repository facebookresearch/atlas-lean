/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupport
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicialMaps

/-!
# Actual original support images under all right-join operators

Every original quotient right-join operator sends the retained front
support to its actual direct image. A collapsed prefix label is read at
the same supplied first maximum. This holds for faces and degeneracies,
without an injected-operator or relative-frame hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeSupportOperators
open PathLastMaximum PathMaximumOperators RightCubeReduction RightCubeSupport
variable {n m : ℕ}

/-- Every original whole chain has exactly the same retained support image under the supplied right-join operator. -/
theorem support_image (θ : ⦋n⦌ ⟶ ⦋m⦌) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q) :
    support (p ⋙ RightCubeOperator.functor θ) = θ.toOrderHom '' support p := by
  have hi : initialMaximum (p ⋙ RightCubeOperator.functor θ) = θ.toOrderHom (initialMaximum p) :=
    RightCubeOperator.maximum_operator θ (p.obj 0)
  ext y
  change (ULift.up.{u} y.castSucc ∈ ((p ⋙ RightCubeOperator.functor θ).obj (Fin.last q.unop.len)).I ∧
    initialMaximum (p ⋙ RightCubeOperator.functor θ) ≤ y) ↔ ∃ j, j ∈ support p ∧ θ.toOrderHom j = y
  rw [hi]
  constructor
  · rintro ⟨hy, hcut⟩
    change ULift.up.{u} y.castSucc ∈ ({ULift.up.{u} (0 : Fin (m + 2))} ∪
      (extension θ).toOrderHom.uliftMap '' (p.obj (Fin.last q.unop.len)).I) at hy
    rcases hy with h₀ | ⟨x, hx, hy⟩
    · have hyDown : y.castSucc = (0 : Fin (m + 1)).castSucc := congrArg ULift.down h₀
      have hyZero : y = 0 := Fin.castSucc_injective _ hyDown
      exact ⟨initialMaximum p, initialMaximum_support p, le_antisymm hcut (hyZero ▸ Fin.zero_le _)⟩
    · cases x with
      | up x =>
        cases x using Fin.lastCases with
        | last =>
          have hbad : Fin.last (m + 1) = y.castSucc := (extension_last θ).symm.trans (congrArg ULift.down hy)
          exact False.elim ((ne_of_lt (Fin.castSucc_lt_last y)) hbad.symm)
        | cast j =>
          have hcast : (θ.toOrderHom j).castSucc = y.castSucc :=
            (extension_front θ j).symm.trans (congrArg ULift.down hy)
          have hjImage : θ.toOrderHom j = y := Fin.castSucc_injective _ hcast
          by_cases hj : initialMaximum p ≤ j
          · exact ⟨j, ⟨hx, hj⟩, hjImage⟩
          · have hLow : y ≤ θ.toOrderHom (initialMaximum p) :=
              hjImage ▸ θ.toOrderHom.monotone (le_of_lt (not_le.mp hj))
            exact ⟨initialMaximum p, initialMaximum_support p, le_antisymm hcut hLow⟩
  · rintro ⟨j, hj, rfl⟩
    change (ULift.up.{u} (θ.toOrderHom j).castSucc ∈
      ({ULift.up.{u} (0 : Fin (m + 2))} ∪ (extension θ).toOrderHom.uliftMap '' (p.obj (Fin.last q.unop.len)).I) ∧
        θ.toOrderHom (initialMaximum p) ≤ θ.toOrderHom j)
    exact ⟨Or.inr ⟨ULift.up.{u} j.castSucc, hj.1, lifted_front θ j⟩, θ.toOrderHom.monotone hj.2⟩

/-- The actual quotient support follows every original face and degeneracy by the same literal direct image. -/
theorem quotientSupport_image (θ : ⦋n⦌ ⟶ ⦋m⦌) {q : SimplexCategoryᵒᵖ}
    (a : (RightCubeRelations.object.{u} n).obj q) :
    quotientSupport ((RightCubeCosimplicialMaps.map θ).app q a) = θ.toOrderHom '' quotientSupport a := by
  induction a using _root_.Quotient.inductionOn with
  | _ p => exact support_image θ p

end CategoryTheory.CoherentRealization.RightCubeSupportOperators
