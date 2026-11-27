/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarConstruction

/-!
# Face identities for coefficient bars

Successive deletion of vertices satisfies the face-face simplicial identity
for the coefficient category bar. The endpoint-arrow equality passes through
the coefficient functor; equality on coproduct summands gives the equality of
bar face maps.
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
/-- The two composites of canonical left-endpoint arrows associated to a pair of faces agree after
transporting across the nerve face identity. -/
theorem faceLeftHom_faceLeftHom {n : ℕ} (i j : Fin (n + 2))
    (hij : i ≤ j) (F : ComposableArrows C (n + 2)) :
    (faceLeftHom j.succ F ≫
        faceLeftHom i ((nerve C).δ j.succ F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ K.left)
        (SSet.δ_comp_δ_apply (S := nerve C) hij F)) =
    faceLeftHom i.castSucc F ≫
      faceLeftHom j ((nerve C).δ i.castSucc F) := by
  have hIndex : j.succ.succAbove (i.succAbove (0 : Fin (n + 1))) =
      i.castSucc.succAbove (j.succAbove (0 : Fin (n + 1))) := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_δ hij) (0 : Fin (n + 1))
  unfold faceLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = F.map _ ≫ F.map _
  rw [← F.map_comp]
  rw [← F.map_comp]
  change F.map _ ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ K.left)
        (SSet.δ_comp_δ_apply (S := nerve C) hij F)) = F.map _
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map _ := congrArg F.map (Subsingleton.elim _ _)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- The coefficient morphisms of two faces agree after transport across the nerve face identity. -/
theorem coefficientFaceHom_faceFace {n : ℕ} (i j : Fin (n + 2))
    (hij : i ≤ j) (F : ComposableArrows C (n + 2)) :
    (coefficientFaceHom M j.succ F ≫
        coefficientFaceHom M i ((nerve C).δ j.succ F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ M.obj K.left)
        (SSet.δ_comp_δ_apply (S := nerve C) hij F)) =
    coefficientFaceHom M i.castSucc F ≫
      coefficientFaceHom M j ((nerve C).δ i.castSucc F) := by
  have h := congrArg M.map (faceLeftHom_faceLeftHom i j hij F)
  simpa only [coefficientFaceHom, Functor.map_comp, eqToHom_map,
    Category.assoc] using h

/-- Transporting a coefficient summand inclusion across equality of its index recovers the given
inclusion. -/
theorem eqToHom_comp_coefficientBarι {n : ℕ}
    {F G : ComposableArrows C n} (h : F = G) :
    eqToHom (congrArg (coefficientBarFamily M n) h) ≫
        coefficientBarι M G = coefficientBarι M F := by
  subst G
  exact Category.id_comp _

/-- The coefficient bar face maps satisfy the first simplicial identity. -/
theorem coefficientBarFace_comp_face {n : ℕ} (i j : Fin (n + 2))
    (hij : i ≤ j) :
    coefficientBarFace M j.succ ≫ coefficientBarFace M i =
      coefficientBarFace M i.castSucc ≫ coefficientBarFace M j := by
  apply coefficientBar_hom_ext M
  intro F
  let hChain := SSet.δ_comp_δ_apply (S := nerve C) hij F
  let Fjs := (nerve C).δ j.succ F
  let Fic := (nerve C).δ i.castSucc F
  have hFaceL₁ := coefficientBarι_face M j.succ F
  have hFaceL₂ := coefficientBarι_face M i Fjs
  have hFaceR₁ := coefficientBarι_face M i.castSucc F
  have hFaceR₂ := coefficientBarι_face M j Fic
  have hCoeff := coefficientFaceHom_faceFace M i j hij F
  have hTransport :
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ M.obj K.left)
        hChain) ≫ coefficientBarι M ((nerve C).δ j ((nerve C).δ i.castSucc F)) =
      coefficientBarι M ((nerve C).δ i ((nerve C).δ j.succ F)) := by
    exact eqToHom_comp_coefficientBarι M hChain
  calc
    coefficientBarι M F ≫
          (coefficientBarFace M j.succ ≫ coefficientBarFace M i) =
        (coefficientBarι M F ≫ coefficientBarFace M j.succ) ≫
          coefficientBarFace M i := (Category.assoc _ _ _).symm
    _ = (coefficientFaceHom M j.succ F ≫
          coefficientBarι M ((nerve C).δ j.succ F)) ≫
          coefficientBarFace M i := by
      exact congrArg (fun k ↦ k ≫ coefficientBarFace M i) hFaceL₁
    _ = coefficientFaceHom M j.succ F ≫
          (coefficientBarι M ((nerve C).δ j.succ F) ≫
            coefficientBarFace M i) := Category.assoc _ _ _
    _ = coefficientFaceHom M j.succ F ≫
          (coefficientFaceHom M i ((nerve C).δ j.succ F) ≫
            coefficientBarι M ((nerve C).δ i ((nerve C).δ j.succ F))) := by
      exact congrArg (fun k ↦ coefficientFaceHom M j.succ F ≫ k) hFaceL₂
    _ = (coefficientFaceHom M j.succ F ≫
          coefficientFaceHom M i ((nerve C).δ j.succ F)) ≫
            coefficientBarι M ((nerve C).δ i ((nerve C).δ j.succ F)) :=
      (Category.assoc _ _ _).symm
    _ = ((coefficientFaceHom M j.succ F ≫
            coefficientFaceHom M i ((nerve C).δ j.succ F)) ≫
          eqToHom (congrArg
            (fun K : ComposableArrows C n ↦ M.obj K.left) hChain)) ≫
            coefficientBarι M ((nerve C).δ j ((nerve C).δ i.castSucc F)) := by
      calc
        _ = (coefficientFaceHom M j.succ F ≫
              coefficientFaceHom M i ((nerve C).δ j.succ F)) ≫
              (eqToHom (congrArg
                (fun K : ComposableArrows C n ↦ M.obj K.left) hChain) ≫
                coefficientBarι M
                  ((nerve C).δ j ((nerve C).δ i.castSucc F))) := by
            rw [hTransport]
        _ = _ := (Category.assoc _ _ _).symm
    _ = (coefficientFaceHom M i.castSucc F ≫
          coefficientFaceHom M j ((nerve C).δ i.castSucc F)) ≫
            coefficientBarι M ((nerve C).δ j ((nerve C).δ i.castSucc F)) := by
      exact congrArg (fun k ↦ k ≫
        coefficientBarι M ((nerve C).δ j ((nerve C).δ i.castSucc F))) hCoeff
    _ = coefficientFaceHom M i.castSucc F ≫
          (coefficientFaceHom M j ((nerve C).δ i.castSucc F) ≫
            coefficientBarι M ((nerve C).δ j ((nerve C).δ i.castSucc F))) :=
      Category.assoc _ _ _
    _ = coefficientFaceHom M i.castSucc F ≫
          (coefficientBarι M ((nerve C).δ i.castSucc F) ≫
            coefficientBarFace M j) := by
      exact congrArg (fun k ↦ coefficientFaceHom M i.castSucc F ≫ k)
        hFaceR₂.symm
    _ = (coefficientFaceHom M i.castSucc F ≫
          coefficientBarι M ((nerve C).δ i.castSucc F)) ≫
            coefficientBarFace M j := (Category.assoc _ _ _).symm
    _ = (coefficientBarι M F ≫ coefficientBarFace M i.castSucc) ≫
            coefficientBarFace M j := by
      exact congrArg (fun k ↦ k ≫ coefficientBarFace M j) hFaceR₁.symm
    _ = coefficientBarι M F ≫
          (coefficientBarFace M i.castSucc ≫ coefficientBarFace M j) :=
      Category.assoc _ _ _

end CategoryTheory.CategoryHomology

end
