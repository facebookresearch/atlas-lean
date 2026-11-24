/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaces

import MathlibExt.CategoryTheory.CategoryHomology.BarFaceDegeneracies

/-!
# Ordered and cancelling face--degeneracy identities for a pulled-back bar

This file proves the ordered `δ_comp_σ_of_le` identity and the two adjacent
face--degeneracy cancellation identities for the nerve-pullback coefficient
bar. It deliberately stops before `δ_comp_σ_of_gt`, `σ_comp_σ`, simplicial-
object packaging, chain complexes, or homology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Limits.Sigma

universe w v u

variable {A : Type u} [Category.{v} A]

/-- A pair of `Sigma.map'` maps is the identity when its index composite and
its component composites are identities after the induced transport. -/
theorem map'_comp_id
    {I₀ I₁ : Type w} [HasCoproducts.{w} A]
    {X₀ : I₀ → A} {X₁ : I₁ → A}
    (p : I₀ → I₁) (q : I₁ → I₀)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a))
    (hq : ∀ b, X₁ b ⟶ X₀ (q b))
    (hidx : ∀ a, q (p a) = a)
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₀ (hidx a)) = 𝟙 (X₀ a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq = 𝟙 _ := by
  apply Sigma.hom_ext
  intro a
  have transport_ι {x y : I₀} (h : x = y) :
      eqToHom (congrArg X₀ h) ≫ Sigma.ι X₀ y = Sigma.ι X₀ x := by
    subst y
    exact Category.id_comp _
  have hι : eqToHom (congrArg X₀ (hidx a)) ≫
      Sigma.ι X₀ a = Sigma.ι X₀ (q (p a)) :=
    transport_ι (hidx a)
  have h₁ : Sigma.ι X₀ a ≫ Sigma.map' p hp =
      hp a ≫ Sigma.ι X₁ (p a) :=
    Sigma.ι_comp_map' p hp a
  have h₂ : Sigma.ι X₁ (p a) ≫ Sigma.map' q hq =
      hq (p a) ≫ Sigma.ι X₀ (q (p a)) :=
    Sigma.ι_comp_map' q hq (p a)
  calc
    Sigma.ι X₀ a ≫ (Sigma.map' p hp ≫ Sigma.map' q hq) =
        (Sigma.ι X₀ a ≫ Sigma.map' p hp) ≫ Sigma.map' q hq :=
      (Category.assoc _ _ _).symm
    _ = (hp a ≫ Sigma.ι X₁ (p a)) ≫ Sigma.map' q hq := by
      exact congrArg (fun k => k ≫ Sigma.map' q hq) h₁
    _ = hp a ≫ (Sigma.ι X₁ (p a) ≫ Sigma.map' q hq) :=
      Category.assoc _ _ _
    _ = hp a ≫ (hq (p a) ≫ Sigma.ι X₀ (q (p a))) := by
      exact congrArg (fun k => hp a ≫ k) h₂
    _ = (hp a ≫ hq (p a)) ≫ Sigma.ι X₀ (q (p a)) :=
      (Category.assoc _ _ _).symm
    _ = ((hp a ≫ hq (p a)) ≫
          eqToHom (congrArg X₀ (hidx a))) ≫ Sigma.ι X₀ a := by
      calc
        _ = (hp a ≫ hq (p a)) ≫
            (eqToHom (congrArg X₀ (hidx a)) ≫ Sigma.ι X₀ a) := by
          rw [hι]
        _ = _ := (Category.assoc _ _ _).symm
    _ = 𝟙 (X₀ a) ≫ Sigma.ι X₀ a := by
      exact congrArg (fun k => k ≫ Sigma.ι X₀ a) (hhom a)
    _ = Sigma.ι X₀ a := Category.id_comp _
    _ = Sigma.ι X₀ a ≫ 𝟙 _ := (Category.comp_id _).symm

end CategoryTheory.Limits.Sigma

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

/-- Component form of the ordered face--degeneracy identity for the
nerve-pullback coefficient bar. -/
theorem nervePullbackCoefficientHom_face_degeneracy_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (σ : X _⦋n + 1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j.succ σ ≫
        nervePullbackCoefficientFaceHom φ M i.castSucc
          (X.σ j.succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 1))
        (SSet.δ_comp_σ_of_le_apply (S := X) hij σ)) =
    nervePullbackCoefficientFaceHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j (X.δ i σ) := by
  let F : ComposableArrows G (n + 1) := φ.app _ σ
  let Fs : ComposableArrows G (n + 1 + 1) :=
    φ.app _ (X.σ j.succ σ)
  let Fd : ComposableArrows G n := φ.app _ (X.δ i σ)
  let Fl : ComposableArrows G (n + 1) :=
    φ.app _ (X.δ i.castSucc (X.σ j.succ σ))
  let Fr : ComposableArrows G (n + 1) :=
    φ.app _ (X.σ j (X.δ i σ))
  let hs : (CategoryTheory.nerve G).σ j.succ F = Fs := by
    simpa only [F, Fs] using nervePullback_degeneracy_index φ j.succ σ
  let hdl : (CategoryTheory.nerve G).δ i.castSucc Fs = Fl := by
    simpa only [Fs, Fl] using
      nervePullback_face_index φ i.castSucc (X.σ j.succ σ)
  let hdr : (CategoryTheory.nerve G).δ i F = Fd := by
    simpa only [F, Fd] using nervePullback_face_index φ i σ
  let hsr : (CategoryTheory.nerve G).σ j Fd = Fr := by
    simpa only [Fd, Fr] using
      nervePullback_degeneracy_index φ j (X.δ i σ)
  let hX := SSet.δ_comp_σ_of_le_apply (S := X) hij σ
  let hφX : Fl = Fr := by
    exact congrArg (fun τ : X _⦋n + 1⦌ => φ.app _ τ) hX
  let hN := SSet.δ_comp_σ_of_le_apply
    (S := CategoryTheory.nerve G) hij F
  let gs := congrArg (fun K : ComposableArrows G (n + 1 + 1) =>
    K.left) hs
  let gd := congrArg (fun K : ComposableArrows G n => K.left) hdr
  let gL₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).δ i.castSucc K).left) hs
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
  let cL₀ := coefficientDegeneracyHom M j.succ F
  let tL₀ := eqToHom es
  let cL₁ := coefficientFaceHom M i.castSucc Fs
  let tL₁ := eqToHom eL₂
  let tX := eqToHom eL₃
  let cLN := coefficientFaceHom M i.castSucc
    ((CategoryTheory.nerve G).σ j.succ F)
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
    eqToHom_comp_coefficientFaceHom M i.castSucc hs
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
    coefficientHom_face_degeneracy_of_le M i j hij F
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

private theorem nervePullbackCoefficientHom_face_degeneracy_cancel
    {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2))
    (σ : X _⦋n⦌)
    (hX : X.δ k (X.σ i σ) = σ)
    (hN : ∀ F : ComposableArrows G n,
      (CategoryTheory.nerve G).δ k
        ((CategoryTheory.nerve G).σ i F) = F)
    (hCoeff : ∀ F : ComposableArrows G n,
      (coefficientDegeneracyHom M i F ≫
          coefficientFaceHom M k ((CategoryTheory.nerve G).σ i F)) ≫
        eqToHom (congrArg (fun K => M.obj K.left) (hN F)) =
      𝟙 (M.obj F.left)) :
    (nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientFaceHom φ M k (X.σ i σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n) hX) =
    𝟙 (nervePullbackCoefficientFamily φ M n σ) := by
  let F : ComposableArrows G n := φ.app _ σ
  let Fs : ComposableArrows G (n + 1) := φ.app _ (X.σ i σ)
  let Fb : ComposableArrows G n := φ.app _ (X.δ k (X.σ i σ))
  let hs : (CategoryTheory.nerve G).σ i F = Fs := by
    simpa only [F, Fs] using nervePullback_degeneracy_index φ i σ
  let hd : (CategoryTheory.nerve G).δ k Fs = Fb := by
    simpa only [Fs, Fb] using nervePullback_face_index φ k (X.σ i σ)
  let hφX : Fb = F := by
    exact congrArg (fun τ : X _⦋n⦌ => φ.app _ τ) hX
  let hN' := hN F
  let gs := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hs
  let gL₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).δ k K).left) hs
  let gL₂ := congrArg (fun K : ComposableArrows G n => K.left) hd
  let gL₃ := congrArg (fun K : ComposableArrows G n => K.left) hφX
  let gN := congrArg (fun K : ComposableArrows G n => K.left) hN'
  have gcasts : gL₁.trans (gL₂.trans gL₃) = gN :=
    Subsingleton.elim _ _
  let es := congrArg M.obj gs
  let eL₁ := congrArg M.obj gL₁
  let eL₂ := congrArg M.obj gL₂
  let eL₃ := congrArg M.obj gL₃
  let eN := congrArg M.obj gN
  let cD := coefficientDegeneracyHom M i F
  let tD := eqToHom es
  let cF := coefficientFaceHom M k Fs
  let tF := eqToHom eL₂
  let tX := eqToHom eL₃
  let cFN := coefficientFaceHom M k
    ((CategoryTheory.nerve G).σ i F)
  let tFN := eqToHom eL₁
  let tN := eqToHom eN
  have hStep : tD ≫ cF = cFN ≫ tFN :=
    eqToHom_comp_coefficientFaceHom M k hs
  have hTransport : tFN ≫ (tF ≫ tX) = tN := by
    have hUnderlying :
        eqToHom gL₁ ≫ (eqToHom gL₂ ≫ eqToHom gL₃) = eqToHom gN := by
      have hEqToHom :
          (eqToHom (gL₁.trans (gL₂.trans gL₃)) : _ ⟶ F.left) =
          eqToHom gN := congrArg (fun h => eqToHom h) gcasts
      simp only [eqToHom_trans] at hEqToHom ⊢
    have hMapped := congrArg M.map hUnderlying
    simpa only [tFN, tF, tX, tN, eL₁, eL₂, eL₃, eN,
      Functor.map_comp, eqToHom_map] using hMapped
  have hStepRest : tD ≫ (cF ≫ (tF ≫ tX)) =
      cFN ≫ (tFN ≫ (tF ≫ tX)) := by
    calc
      _ = (tD ≫ cF) ≫ (tF ≫ tX) := (Category.assoc _ _ _).symm
      _ = (cFN ≫ tFN) ≫ (tF ≫ tX) := by rw [hStep]
      _ = _ := Category.assoc _ _ _
  have hCoeff' : (cD ≫ cFN) ≫ tN = 𝟙 (M.obj F.left) := hCoeff F
  dsimp only [nervePullbackCoefficientDegeneracyHom,
    nervePullbackCoefficientFaceHom]
  change ((cD ≫ tD) ≫ (cF ≫ tF)) ≫ tX = 𝟙 _
  calc
    _ = cD ≫ (tD ≫ (cF ≫ (tF ≫ tX))) := by
      simp only [Category.assoc]
    _ = cD ≫ (cFN ≫ (tFN ≫ (tF ≫ tX))) :=
      congrArg (fun q => cD ≫ q) hStepRest
    _ = cD ≫ (cFN ≫ tN) := by rw [hTransport]
    _ = (cD ≫ cFN) ≫ tN := (Category.assoc _ _ _).symm
    _ = _ := hCoeff'

/-- First component cancellation for a degeneracy followed by its matching
face. -/
theorem nervePullbackCoefficientHom_face_degeneracy_self {n : ℕ}
    (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientFaceHom φ M i.castSucc (X.σ i σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_σ_self_apply (S := X) i σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M n σ) := by
  exact nervePullbackCoefficientHom_face_degeneracy_cancel
    φ M i i.castSucc σ
    (SSet.δ_comp_σ_self_apply (S := X) i σ)
    (fun F => SSet.δ_comp_σ_self_apply
      (S := CategoryTheory.nerve G) i F)
    (fun F => coefficientHom_face_degeneracy_self M i F)

/-- Second component cancellation for a degeneracy followed by its adjacent
face. -/
theorem nervePullbackCoefficientHom_face_degeneracy_succ {n : ℕ}
    (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientFaceHom φ M i.succ (X.σ i σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_σ_succ_apply (S := X) i σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M n σ) := by
  exact nervePullbackCoefficientHom_face_degeneracy_cancel
    φ M i i.succ σ
    (SSet.δ_comp_σ_succ_apply (S := X) i σ)
    (fun F => SSet.δ_comp_σ_succ_apply
      (S := CategoryTheory.nerve G) i F)
    (fun F => coefficientHom_face_degeneracy_succ M i F)

variable [HasCoproducts.{max uG vG} A]

/-- Ordered face--degeneracy identity for the nerve-pullback coefficient
bar. -/
theorem nervePullbackCoefficient_face_degeneracy_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    nervePullbackCoefficientDegeneracy φ M j.succ ≫
        nervePullbackCoefficientFace φ M i.castSucc =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j := by
  unfold nervePullbackCoefficientDegeneracy nervePullbackCoefficientFace
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily φ M (n + 1))
    (X₁ := nervePullbackCoefficientFamily φ M (n + 2))
    (X₁' := nervePullbackCoefficientFamily φ M n)
    (X₂ := nervePullbackCoefficientFamily φ M (n + 1))
    (fun σ => X.σ j.succ σ)
    (fun σ => X.δ i.castSucc σ)
    (nervePullbackCoefficientDegeneracyHom φ M j.succ)
    (nervePullbackCoefficientFaceHom φ M i.castSucc)
    (fun σ => X.δ i σ)
    (fun σ => X.σ j σ)
    (nervePullbackCoefficientFaceHom φ M i)
    (nervePullbackCoefficientDegeneracyHom φ M j)
    (fun σ => SSet.δ_comp_σ_of_le_apply (S := X) hij σ)
    (fun σ =>
      nervePullbackCoefficientHom_face_degeneracy_of_le φ M i j hij σ)

/-- First degree-map cancellation for the nerve-pullback coefficient bar. -/
theorem nervePullbackCoefficient_face_degeneracy_self {n : ℕ}
    (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.castSucc = 𝟙 _ := by
  unfold nervePullbackCoefficientDegeneracy nervePullbackCoefficientFace
  exact Sigma.map'_comp_id
    (X₀ := nervePullbackCoefficientFamily φ M n)
    (X₁ := nervePullbackCoefficientFamily φ M (n + 1))
    (fun σ => X.σ i σ)
    (fun σ => X.δ i.castSucc σ)
    (nervePullbackCoefficientDegeneracyHom φ M i)
    (nervePullbackCoefficientFaceHom φ M i.castSucc)
    (fun σ => SSet.δ_comp_σ_self_apply (S := X) i σ)
    (fun σ =>
      nervePullbackCoefficientHom_face_degeneracy_self φ M i σ)

/-- Second degree-map cancellation for the nerve-pullback coefficient bar. -/
theorem nervePullbackCoefficient_face_degeneracy_succ {n : ℕ}
    (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.succ = 𝟙 _ := by
  unfold nervePullbackCoefficientDegeneracy nervePullbackCoefficientFace
  exact Sigma.map'_comp_id
    (X₀ := nervePullbackCoefficientFamily φ M n)
    (X₁ := nervePullbackCoefficientFamily φ M (n + 1))
    (fun σ => X.σ i σ)
    (fun σ => X.δ i.succ σ)
    (nervePullbackCoefficientDegeneracyHom φ M i)
    (nervePullbackCoefficientFaceHom φ M i.succ)
    (fun σ => SSet.δ_comp_σ_succ_apply (S := X) i σ)
    (fun σ =>
      nervePullbackCoefficientHom_face_degeneracy_succ φ M i σ)

end CategoryTheory.CategoryHomology
