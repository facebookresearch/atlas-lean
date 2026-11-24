/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarCore

import MathlibExt.CategoryTheory.CategoryHomology.BarFaces

/-!
# Face identity for the nerve-pullback coefficient bar

The component face maps of the nerve-pullback coefficient bar satisfy the
face--face coherence after the naturality transports of the nerve map are
combined with the face identity of the source simplicial set. The generic
coproduct comparison from `NervePullbackBarCore` then gives the corresponding
identity of degree maps.

This file proves only the face--face identity. It makes no mixed face--
degeneracy, degeneracy--degeneracy, simplicial-object, chain-complex, homology,
local-system, or plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CategoryHomology

universe vG uG vA uA

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

@[reassoc]
private theorem eqToHom_comp_coefficientFaceHom {n : ℕ}
    (i : Fin (n + 2)) {F F' : ComposableArrows G (n + 1)}
    (h : F = F') :
    eqToHom (congrArg (fun K => M.obj K.left) h) ≫
        coefficientFaceHom M i F' =
      coefficientFaceHom M i F ≫
        eqToHom (congrArg
          (fun K => M.obj ((CategoryTheory.nerve G).δ i K).left) h) := by
  subst F'
  simp

/-- Component face maps of the nerve-pullback coefficient bar satisfy the
face--face coherence, including the final transport along the face identity
of the source simplicial set. -/
theorem nervePullbackCoefficientFaceHom_faceFace {n : ℕ}
    (i j : Fin (n + 2)) (hij : i ≤ j) (σ : X _⦋n + 2⦌) :
    (nervePullbackCoefficientFaceHom φ M j.succ σ ≫
        nervePullbackCoefficientFaceHom φ M i (X.δ j.succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_δ_apply (S := X) hij σ)) =
    nervePullbackCoefficientFaceHom φ M i.castSucc σ ≫
      nervePullbackCoefficientFaceHom φ M j
        (X.δ i.castSucc σ) := by
  let F : ComposableArrows G (n + 1 + 1) := φ.app _ σ
  let Fjs : ComposableArrows G (n + 1) :=
    φ.app _ (X.δ j.succ σ)
  let Fic : ComposableArrows G (n + 1) :=
    φ.app _ (X.δ i.castSucc σ)
  let Fij : ComposableArrows G n :=
    φ.app _ (X.δ i (X.δ j.succ σ))
  let Fji : ComposableArrows G n :=
    φ.app _ (X.δ j (X.δ i.castSucc σ))
  let hjs : (CategoryTheory.nerve G).δ j.succ F = Fjs := by
    simpa only [F, Fjs] using nervePullback_face_index φ j.succ σ
  let hic : (CategoryTheory.nerve G).δ i.castSucc F = Fic := by
    simpa only [F, Fic] using nervePullback_face_index φ i.castSucc σ
  let hi : (CategoryTheory.nerve G).δ i Fjs = Fij := by
    simpa only [Fjs, Fij] using
      nervePullback_face_index φ i (X.δ j.succ σ)
  let hj : (CategoryTheory.nerve G).δ j Fic = Fji := by
    simpa only [Fic, Fji] using
      nervePullback_face_index φ j (X.δ i.castSucc σ)
  let hX := SSet.δ_comp_δ_apply (S := X) hij σ
  let hφX : Fij = Fji := by
    exact congrArg (fun τ : X _⦋n⦌ => φ.app _ τ) hX
  let hN := SSet.δ_comp_δ_apply
    (S := CategoryTheory.nerve G) hij F
  let gjs := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hjs
  let gic := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hic
  let gL₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).δ i K).left) hjs
  let gL₂ := congrArg (fun K : ComposableArrows G n => K.left) hi
  let gL₃ := congrArg (fun K : ComposableArrows G n => K.left) hφX
  let gN := congrArg (fun K : ComposableArrows G n => K.left) hN
  let gR₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).δ j K).left) hic
  let gR₂ := congrArg (fun K : ComposableArrows G n => K.left) hj
  have gcasts : gL₁.trans (gL₂.trans gL₃) =
      gN.trans (gR₁.trans gR₂) :=
    Subsingleton.elim _ _
  let ejs := congrArg M.obj gjs
  let eic := congrArg M.obj gic
  let eL₁ := congrArg M.obj gL₁
  let eL₂ := congrArg M.obj gL₂
  let eL₃ := congrArg M.obj gL₃
  let eN := congrArg M.obj gN
  let eR₁ := congrArg M.obj gR₁
  let eR₂ := congrArg M.obj gR₂
  let cL₀ := coefficientFaceHom M j.succ F
  let tL₀ := eqToHom ejs
  let cL₁ := coefficientFaceHom M i Fjs
  let tL₁ := eqToHom eL₂
  let tX := eqToHom eL₃
  let cLN := coefficientFaceHom M i
    ((CategoryTheory.nerve G).δ j.succ F)
  let tLN := eqToHom eL₁
  let tN := eqToHom eN
  let cR₀ := coefficientFaceHom M i.castSucc F
  let tR₀ := eqToHom eic
  let cR₁ := coefficientFaceHom M j Fic
  let cRN := coefficientFaceHom M j
    ((CategoryTheory.nerve G).δ i.castSucc F)
  let tRN := eqToHom eR₁
  let tR₂ := eqToHom eR₂
  have hStepL : tL₀ ≫ cL₁ = cLN ≫ tLN :=
    eqToHom_comp_coefficientFaceHom M i hjs
  have hStepR : tR₀ ≫ cR₁ = cRN ≫ tRN :=
    eqToHom_comp_coefficientFaceHom M j hic
  have hTransport : tLN ≫ (tL₁ ≫ tX) =
      tN ≫ (tRN ≫ tR₂) := by
    have hUnderlying :
        eqToHom gL₁ ≫ (eqToHom gL₂ ≫ eqToHom gL₃) =
          eqToHom gN ≫ (eqToHom gR₁ ≫ eqToHom gR₂) := by
      have hEqToHom :
          (eqToHom (gL₁.trans (gL₂.trans gL₃)) :
            _ ⟶ Fji.left) =
          eqToHom (gN.trans (gR₁.trans gR₂)) :=
        congrArg (fun h => eqToHom h) gcasts
      simp only [eqToHom_trans] at hEqToHom ⊢
    have hMapped := congrArg M.map hUnderlying
    simpa only [tLN, tL₁, tX, tN, tRN, tR₂, eL₁, eL₂, eL₃,
      eN, eR₁, eR₂, Functor.map_comp, eqToHom_map] using hMapped
  have hStepLRest : tL₀ ≫ (cL₁ ≫ (tL₁ ≫ tX)) =
      cLN ≫ (tLN ≫ (tL₁ ≫ tX)) := by
    calc
      _ = (tL₀ ≫ cL₁) ≫ (tL₁ ≫ tX) :=
        (Category.assoc _ _ _).symm
      _ = (cLN ≫ tLN) ≫ (tL₁ ≫ tX) := by rw [hStepL]
      _ = _ := Category.assoc _ _ _
  have hStepRRest : tR₀ ≫ (cR₁ ≫ tR₂) =
      cRN ≫ (tRN ≫ tR₂) := by
    calc
      _ = (tR₀ ≫ cR₁) ≫ tR₂ := (Category.assoc _ _ _).symm
      _ = (cRN ≫ tRN) ≫ tR₂ := by rw [hStepR]
      _ = _ := Category.assoc _ _ _
  have hCoeff : (cL₀ ≫ cLN) ≫ tN = cR₀ ≫ cRN :=
    coefficientFaceHom_faceFace M i j hij F
  have hCoeffPost := congrArg
    (fun k => k ≫ (tRN ≫ tR₂)) hCoeff
  have hCoeffPost' :
      cL₀ ≫ (cLN ≫ (tN ≫ (tRN ≫ tR₂))) =
        cR₀ ≫ (cRN ≫ (tRN ≫ tR₂)) := by
    simpa only [Category.assoc] using hCoeffPost
  dsimp only [nervePullbackCoefficientFaceHom]
  change ((cL₀ ≫ tL₀) ≫ (cL₁ ≫ tL₁)) ≫ tX =
    (cR₀ ≫ tR₀) ≫ (cR₁ ≫ tR₂)
  calc
    _ = cL₀ ≫ (tL₀ ≫ (cL₁ ≫ (tL₁ ≫ tX))) := by
      simp only [Category.assoc]
    _ = cL₀ ≫ (cLN ≫ (tLN ≫ (tL₁ ≫ tX))) :=
      congrArg (fun k => cL₀ ≫ k) hStepLRest
    _ = cL₀ ≫ (cLN ≫ (tN ≫ (tRN ≫ tR₂))) :=
      congrArg (fun k => cL₀ ≫ (cLN ≫ k)) hTransport
    _ = cR₀ ≫ (cRN ≫ (tRN ≫ tR₂)) := hCoeffPost'
    _ = cR₀ ≫ (tR₀ ≫ (cR₁ ≫ tR₂)) :=
      congrArg (fun k => cR₀ ≫ k) hStepRRest.symm
    _ = _ := by simp only [Category.assoc]

variable [HasCoproducts.{max uG vG} A]

/-- Face maps of the nerve-pullback coefficient bar satisfy the first
simplicial identity. -/
theorem nervePullbackCoefficientFace_comp_face {n : ℕ}
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    nervePullbackCoefficientFace φ M j.succ ≫
        nervePullbackCoefficientFace φ M i =
      nervePullbackCoefficientFace φ M i.castSucc ≫
        nervePullbackCoefficientFace φ M j := by
  unfold nervePullbackCoefficientFace
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily φ M (n + 2))
    (X₁ := nervePullbackCoefficientFamily φ M (n + 1))
    (X₁' := nervePullbackCoefficientFamily φ M (n + 1))
    (X₂ := nervePullbackCoefficientFamily φ M n)
    (fun σ => X.δ j.succ σ)
    (fun σ => X.δ i σ)
    (nervePullbackCoefficientFaceHom φ M j.succ)
    (nervePullbackCoefficientFaceHom φ M i)
    (fun σ => X.δ i.castSucc σ)
    (fun σ => X.δ j σ)
    (nervePullbackCoefficientFaceHom φ M i.castSucc)
    (nervePullbackCoefficientFaceHom φ M j)
    (fun σ => SSet.δ_comp_δ_apply (S := X) hij σ)
    (fun σ => nervePullbackCoefficientFaceHom_faceFace φ M i j hij σ)

end CategoryTheory.CategoryHomology
