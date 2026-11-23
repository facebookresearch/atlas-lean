/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesLe

import MathlibExt.CategoryTheory.CategoryHomology.BarFaceDegeneracies

/-!
# Remaining mixed face--degeneracy identity for a pulled-back bar

This file proves the `δ_comp_σ_of_gt` component and degree-map identities for
the nerve-pullback coefficient bar. It deliberately stops before the
degeneracy--degeneracy identity, simplicial-object packaging, chain complexes,
or homology.
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

@[reassoc]
private theorem eqToHom_comp_coefficientDegeneracyHom {n : ℕ}
    (i : Fin (n + 1)) {F F' : ComposableArrows G n}
    (h : F = F') :
    eqToHom (congrArg (fun K => M.obj K.left) h) ≫
        coefficientDegeneracyHom M i F' =
      coefficientDegeneracyHom M i F ≫
        eqToHom (congrArg
          (fun K => M.obj ((CategoryTheory.nerve G).σ i K).left) h) := by
  subst F'
  simp

/-- Component form of the remaining mixed face--degeneracy identity for the
nerve-pullback coefficient bar. -/
theorem nervePullbackCoefficientHom_face_degeneracy_of_gt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (σ : X _⦋n + 1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j.castSucc σ ≫
        nervePullbackCoefficientFaceHom φ M i.succ
          (X.σ j.castSucc σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 1))
        (SSet.δ_comp_σ_of_gt_apply (S := X) hji σ)) =
    nervePullbackCoefficientFaceHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j (X.δ i σ) := by
  let F : ComposableArrows G (n + 1) := φ.app _ σ
  let Fs : ComposableArrows G (n + 1 + 1) :=
    φ.app _ (X.σ j.castSucc σ)
  let Fd : ComposableArrows G n := φ.app _ (X.δ i σ)
  let Fl : ComposableArrows G (n + 1) :=
    φ.app _ (X.δ i.succ (X.σ j.castSucc σ))
  let Fr : ComposableArrows G (n + 1) :=
    φ.app _ (X.σ j (X.δ i σ))
  let hs : (CategoryTheory.nerve G).σ j.castSucc F = Fs := by
    simpa only [F, Fs] using nervePullback_degeneracy_index φ j.castSucc σ
  let hdl : (CategoryTheory.nerve G).δ i.succ Fs = Fl := by
    simpa only [Fs, Fl] using
      nervePullback_face_index φ i.succ (X.σ j.castSucc σ)
  let hdr : (CategoryTheory.nerve G).δ i F = Fd := by
    simpa only [F, Fd] using nervePullback_face_index φ i σ
  let hsr : (CategoryTheory.nerve G).σ j Fd = Fr := by
    simpa only [Fd, Fr] using
      nervePullback_degeneracy_index φ j (X.δ i σ)
  let hX := SSet.δ_comp_σ_of_gt_apply (S := X) hji σ
  let hφX : Fl = Fr := by
    exact congrArg (fun τ : X _⦋n + 1⦌ => φ.app _ τ) hX
  let hN := SSet.δ_comp_σ_of_gt_apply
    (S := CategoryTheory.nerve G) hji F
  let gs := congrArg (fun K : ComposableArrows G (n + 1 + 1) =>
    K.left) hs
  let gd := congrArg (fun K : ComposableArrows G n => K.left) hdr
  let gL₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).δ i.succ K).left) hs
  let gL₂ := congrArg (fun K : ComposableArrows G (n + 1) =>
    K.left) hdl
  let gL₃ := congrArg (fun K : ComposableArrows G (n + 1) =>
    K.left) hφX
  let gN := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hN
  let gR₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).σ j K).left) hdr
  let gR₂ := congrArg (fun K : ComposableArrows G (n + 1) =>
    K.left) hsr
  have gcasts : gL₁.trans (gL₂.trans gL₃) =
      gN.trans (gR₁.trans gR₂) :=
    Subsingleton.elim _ _
  let es := congrArg M.obj gs
  let ed := congrArg M.obj gd
  let eL₁ := congrArg M.obj gL₁
  let eL₂ := congrArg M.obj gL₂
  let eL₃ := congrArg M.obj gL₃
  let eN := congrArg M.obj gN
  let eR₁ := congrArg M.obj gR₁
  let eR₂ := congrArg M.obj gR₂
  let cL₀ := coefficientDegeneracyHom M j.castSucc F
  let tL₀ := eqToHom es
  let cL₁ := coefficientFaceHom M i.succ Fs
  let tL₁ := eqToHom eL₂
  let tX := eqToHom eL₃
  let cLN := coefficientFaceHom M i.succ
    ((CategoryTheory.nerve G).σ j.castSucc F)
  let tLN := eqToHom eL₁
  let tN := eqToHom eN
  let cR₀ := coefficientFaceHom M i F
  let tR₀ := eqToHom ed
  let cR₁ := coefficientDegeneracyHom M j Fd
  let cRN := coefficientDegeneracyHom M j
    ((CategoryTheory.nerve G).δ i F)
  let tRN := eqToHom eR₁
  let tR₂ := eqToHom eR₂
  have hStepL : tL₀ ≫ cL₁ = cLN ≫ tLN :=
    eqToHom_comp_coefficientFaceHom M i.succ hs
  have hStepR : tR₀ ≫ cR₁ = cRN ≫ tRN :=
    eqToHom_comp_coefficientDegeneracyHom M j hdr
  have hTransport : tLN ≫ (tL₁ ≫ tX) =
      tN ≫ (tRN ≫ tR₂) := by
    have hUnderlying :
        eqToHom gL₁ ≫ (eqToHom gL₂ ≫ eqToHom gL₃) =
          eqToHom gN ≫ (eqToHom gR₁ ≫ eqToHom gR₂) := by
      have hEqToHom :
          (eqToHom (gL₁.trans (gL₂.trans gL₃)) : _ ⟶ Fr.left) =
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
    coefficientHom_face_degeneracy_of_gt M i j hji F
  have hCoeffPost := congrArg
    (fun k => k ≫ (tRN ≫ tR₂)) hCoeff
  have hCoeffPost' :
      cL₀ ≫ (cLN ≫ (tN ≫ (tRN ≫ tR₂))) =
        cR₀ ≫ (cRN ≫ (tRN ≫ tR₂)) := by
    simpa only [Category.assoc] using hCoeffPost
  dsimp only [nervePullbackCoefficientDegeneracyHom,
    nervePullbackCoefficientFaceHom]
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

/-- Remaining mixed face--degeneracy identity for degree maps of the
nerve-pullback coefficient bar. -/
theorem nervePullbackCoefficient_face_degeneracy_of_gt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    nervePullbackCoefficientDegeneracy φ M j.castSucc ≫
        nervePullbackCoefficientFace φ M i.succ =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j := by
  unfold nervePullbackCoefficientDegeneracy nervePullbackCoefficientFace
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily φ M (n + 1))
    (X₁ := nervePullbackCoefficientFamily φ M (n + 2))
    (X₁' := nervePullbackCoefficientFamily φ M n)
    (X₂ := nervePullbackCoefficientFamily φ M (n + 1))
    (fun σ => X.σ j.castSucc σ)
    (fun σ => X.δ i.succ σ)
    (nervePullbackCoefficientDegeneracyHom φ M j.castSucc)
    (nervePullbackCoefficientFaceHom φ M i.succ)
    (fun σ => X.δ i σ)
    (fun σ => X.σ j σ)
    (nervePullbackCoefficientFaceHom φ M i)
    (nervePullbackCoefficientDegeneracyHom φ M j)
    (fun σ => SSet.δ_comp_σ_of_gt_apply (S := X) hji σ)
    (fun σ =>
      nervePullbackCoefficientHom_face_degeneracy_of_gt φ M i j hji σ)

end CategoryTheory.CategoryHomology
