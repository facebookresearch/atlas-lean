/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFaces

/-!
# Degeneracy identities for coefficient bars

Inserting repeated vertices twice satisfies the degeneracy-degeneracy
simplicial identity for the coefficient category bar. The endpoint-arrow
identity passes through the coefficient functor, and the coproduct
injections determine the resulting equality of bar maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- The two composites of canonical left-endpoint arrows associated to a pair of degeneracies
agree after transport across the nerve identity. -/
theorem degeneracyLeftHom_degeneracyLeftHom {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) (F : ComposableArrows C n) :
    (degeneracyLeftHom j F ≫
        degeneracyLeftHom i.castSucc ((nerve C).σ j F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 2) ↦ K.left)
        (SSet.σ_comp_σ_apply (S := nerve C) hij F)) =
    degeneracyLeftHom i F ≫
      degeneracyLeftHom j.succ ((nerve C).σ i F) := by
  have hIndex : j.predAbove (i.castSucc.predAbove (0 : Fin (n + 3))) =
      i.predAbove (j.succ.predAbove (0 : Fin (n + 3))) := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.σ_comp_σ hij).symm (0 : Fin (n + 3))
  unfold degeneracyLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = F.map _ ≫ F.map _
  rw [← F.map_comp]
  rw [← F.map_comp]
  change F.map _ ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 2) ↦ K.left)
        (SSet.σ_comp_σ_apply (S := nerve C) hij F)) = F.map _
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map _ := congrArg F.map (Subsingleton.elim _ _)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Coefficient maps of two degeneracies satisfy the transported degeneracy identity. -/
theorem coefficientDegeneracyHom_degeneracyDegeneracy {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) (F : ComposableArrows C n) :
    (coefficientDegeneracyHom M j F ≫
        coefficientDegeneracyHom M i.castSucc ((nerve C).σ j F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 2) ↦ M.obj K.left)
        (SSet.σ_comp_σ_apply (S := nerve C) hij F)) =
    coefficientDegeneracyHom M i F ≫
      coefficientDegeneracyHom M j.succ ((nerve C).σ i F) := by
  have h := congrArg M.map (degeneracyLeftHom_degeneracyLeftHom i j hij F)
  simpa only [coefficientDegeneracyHom, Functor.map_comp, eqToHom_map,
    Category.assoc] using h

/-- Coefficient bar degeneracies satisfy the fifth simplicial identity. -/
theorem coefficientBarDegeneracy_comp_degeneracy {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    coefficientBarDegeneracy M j ≫ coefficientBarDegeneracy M i.castSucc =
      coefficientBarDegeneracy M i ≫ coefficientBarDegeneracy M j.succ := by
  apply coefficientBar_hom_ext M
  intro F
  let hChain := SSet.σ_comp_σ_apply (S := nerve C) hij F
  let Fsj := (nerve C).σ j F
  let Fsi := (nerve C).σ i F
  have hDegL₁ := coefficientBarι_degeneracy M j F
  have hDegL₂ := coefficientBarι_degeneracy M i.castSucc Fsj
  have hDegR₁ := coefficientBarι_degeneracy M i F
  have hDegR₂ := coefficientBarι_degeneracy M j.succ Fsi
  have hCoeff := coefficientDegeneracyHom_degeneracyDegeneracy M i j hij F
  have hTransport :
      eqToHom (congrArg
        (fun K : ComposableArrows C (n + 2) ↦ M.obj K.left) hChain) ≫
        coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F)) =
      coefficientBarι M ((nerve C).σ i.castSucc ((nerve C).σ j F)) := by
    exact eqToHom_comp_coefficientBarι M hChain
  calc
    coefficientBarι M F ≫
          (coefficientBarDegeneracy M j ≫
            coefficientBarDegeneracy M i.castSucc) =
        (coefficientBarι M F ≫ coefficientBarDegeneracy M j) ≫
          coefficientBarDegeneracy M i.castSucc := (Category.assoc _ _ _).symm
    _ = (coefficientDegeneracyHom M j F ≫
          coefficientBarι M ((nerve C).σ j F)) ≫
          coefficientBarDegeneracy M i.castSucc := by
      exact congrArg (fun k ↦ k ≫ coefficientBarDegeneracy M i.castSucc) hDegL₁
    _ = coefficientDegeneracyHom M j F ≫
          (coefficientBarι M ((nerve C).σ j F) ≫
            coefficientBarDegeneracy M i.castSucc) := Category.assoc _ _ _
    _ = coefficientDegeneracyHom M j F ≫
          (coefficientDegeneracyHom M i.castSucc ((nerve C).σ j F) ≫
            coefficientBarι M ((nerve C).σ i.castSucc ((nerve C).σ j F))) := by
      exact congrArg (fun k ↦ coefficientDegeneracyHom M j F ≫ k) hDegL₂
    _ = (coefficientDegeneracyHom M j F ≫
          coefficientDegeneracyHom M i.castSucc ((nerve C).σ j F)) ≫
            coefficientBarι M ((nerve C).σ i.castSucc ((nerve C).σ j F)) :=
      (Category.assoc _ _ _).symm
    _ = ((coefficientDegeneracyHom M j F ≫
            coefficientDegeneracyHom M i.castSucc ((nerve C).σ j F)) ≫
          eqToHom (congrArg
            (fun K : ComposableArrows C (n + 2) ↦ M.obj K.left) hChain)) ≫
            coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F)) := by
      calc
        _ = (coefficientDegeneracyHom M j F ≫
              coefficientDegeneracyHom M i.castSucc ((nerve C).σ j F)) ≫
              (eqToHom (congrArg
                (fun K : ComposableArrows C (n + 2) ↦ M.obj K.left) hChain) ≫
                coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F))) := by
            rw [hTransport]
        _ = _ := (Category.assoc _ _ _).symm
    _ = (coefficientDegeneracyHom M i F ≫
          coefficientDegeneracyHom M j.succ ((nerve C).σ i F)) ≫
            coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F)) := by
      exact congrArg (fun k ↦ k ≫
        coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F))) hCoeff
    _ = coefficientDegeneracyHom M i F ≫
          (coefficientDegeneracyHom M j.succ ((nerve C).σ i F) ≫
            coefficientBarι M ((nerve C).σ j.succ ((nerve C).σ i F))) :=
      Category.assoc _ _ _
    _ = coefficientDegeneracyHom M i F ≫
          (coefficientBarι M ((nerve C).σ i F) ≫
            coefficientBarDegeneracy M j.succ) := by
      exact congrArg (fun k ↦ coefficientDegeneracyHom M i F ≫ k) hDegR₂.symm
    _ = (coefficientDegeneracyHom M i F ≫
          coefficientBarι M ((nerve C).σ i F)) ≫
            coefficientBarDegeneracy M j.succ := (Category.assoc _ _ _).symm
    _ = (coefficientBarι M F ≫ coefficientBarDegeneracy M i) ≫
            coefficientBarDegeneracy M j.succ := by
      exact congrArg (fun k ↦ k ≫ coefficientBarDegeneracy M j.succ) hDegR₁.symm
    _ = coefficientBarι M F ≫
          (coefficientBarDegeneracy M i ≫ coefficientBarDegeneracy M j.succ) :=
      Category.assoc _ _ _

end CategoryTheory.CategoryHomology

end
