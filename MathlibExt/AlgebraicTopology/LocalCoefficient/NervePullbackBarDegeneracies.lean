/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesLe

import MathlibExt.CategoryTheory.CategoryHomology.BarDegeneracies

/-!
# Degeneracy identity for the nerve-pullback coefficient bar

The component degeneracy maps of the nerve-pullback coefficient bar satisfy
the degeneracy--degeneracy coherence after the naturality transports of the
nerve map are combined with the degeneracy identity of the source simplicial
set. The generic coproduct comparison from `NervePullbackBarCore` then gives
the corresponding identity of degree maps.

This file proves only `σ_comp_σ`. It stops before simplicial-object packaging,
chain complexes, homology, local-system specialization, or plus constructions.
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

/-- Component degeneracy maps of the nerve-pullback coefficient bar satisfy
the degeneracy--degeneracy coherence, including the final transport along the
source simplicial identity. -/
theorem nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j σ ≫
        nervePullbackCoefficientDegeneracyHom φ M i.castSucc (X.σ j σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 2))
        (SSet.σ_comp_σ_apply (S := X) hij σ)) =
    nervePullbackCoefficientDegeneracyHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j.succ (X.σ i σ) := by
  let F : ComposableArrows G n := φ.app _ σ
  let Fsj : ComposableArrows G (n + 1) := φ.app _ (X.σ j σ)
  let Fsi : ComposableArrows G (n + 1) := φ.app _ (X.σ i σ)
  let Fl : ComposableArrows G (n + 2) :=
    φ.app _ (X.σ i.castSucc (X.σ j σ))
  let Fr : ComposableArrows G (n + 2) :=
    φ.app _ (X.σ j.succ (X.σ i σ))
  let hsj : (CategoryTheory.nerve G).σ j F = Fsj := by
    simpa only [F, Fsj] using nervePullback_degeneracy_index φ j σ
  let hsl : (CategoryTheory.nerve G).σ i.castSucc Fsj = Fl := by
    simpa only [Fsj, Fl] using
      nervePullback_degeneracy_index φ i.castSucc (X.σ j σ)
  let hsi : (CategoryTheory.nerve G).σ i F = Fsi := by
    simpa only [F, Fsi] using nervePullback_degeneracy_index φ i σ
  let hsr : (CategoryTheory.nerve G).σ j.succ Fsi = Fr := by
    simpa only [Fsi, Fr] using
      nervePullback_degeneracy_index φ j.succ (X.σ i σ)
  let hX := SSet.σ_comp_σ_apply (S := X) hij σ
  let hφX : Fl = Fr := by
    exact congrArg (fun τ : X _⦋n + 2⦌ => φ.app _ τ) hX
  let hN := SSet.σ_comp_σ_apply
    (S := CategoryTheory.nerve G) hij F
  let gsj := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hsj
  let gsi := congrArg (fun K : ComposableArrows G (n + 1) => K.left) hsi
  let gL₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).σ i.castSucc K).left) hsj
  let gL₂ := congrArg (fun K : ComposableArrows G (n + 2) => K.left) hsl
  let gL₃ := congrArg (fun K : ComposableArrows G (n + 2) => K.left) hφX
  let gN := congrArg (fun K : ComposableArrows G (n + 2) => K.left) hN
  let gR₁ := congrArg
    (fun K => ((CategoryTheory.nerve G).σ j.succ K).left) hsi
  let gR₂ := congrArg (fun K : ComposableArrows G (n + 2) => K.left) hsr
  have gcasts : gL₁.trans (gL₂.trans gL₃) =
      gN.trans (gR₁.trans gR₂) :=
    Subsingleton.elim _ _
  let esj := congrArg M.obj gsj
  let esi := congrArg M.obj gsi
  let eL₁ := congrArg M.obj gL₁
  let eL₂ := congrArg M.obj gL₂
  let eL₃ := congrArg M.obj gL₃
  let eN := congrArg M.obj gN
  let eR₁ := congrArg M.obj gR₁
  let eR₂ := congrArg M.obj gR₂
  let cL₀ := coefficientDegeneracyHom M j F
  let tL₀ := eqToHom esj
  let cL₁ := coefficientDegeneracyHom M i.castSucc Fsj
  let tL₁ := eqToHom eL₂
  let tX := eqToHom eL₃
  let cLN := coefficientDegeneracyHom M i.castSucc
    ((CategoryTheory.nerve G).σ j F)
  let tLN := eqToHom eL₁
  let tN := eqToHom eN
  let cR₀ := coefficientDegeneracyHom M i F
  let tR₀ := eqToHom esi
  let cR₁ := coefficientDegeneracyHom M j.succ Fsi
  let cRN := coefficientDegeneracyHom M j.succ
    ((CategoryTheory.nerve G).σ i F)
  let tRN := eqToHom eR₁
  let tR₂ := eqToHom eR₂
  have hStepL : tL₀ ≫ cL₁ = cLN ≫ tLN :=
    eqToHom_comp_coefficientDegeneracyHom M i.castSucc hsj
  have hStepR : tR₀ ≫ cR₁ = cRN ≫ tRN :=
    eqToHom_comp_coefficientDegeneracyHom M j.succ hsi
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
    coefficientDegeneracyHom_degeneracyDegeneracy M i j hij F
  have hCoeffPost := congrArg
    (fun k => k ≫ (tRN ≫ tR₂)) hCoeff
  have hCoeffPost' :
      cL₀ ≫ (cLN ≫ (tN ≫ (tRN ≫ tR₂))) =
        cR₀ ≫ (cRN ≫ (tRN ≫ tR₂)) := by
    simpa only [Category.assoc] using hCoeffPost
  dsimp only [nervePullbackCoefficientDegeneracyHom]
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

/-- Degree degeneracy maps of the nerve-pullback coefficient bar satisfy the
degeneracy--degeneracy identity. -/
theorem nervePullbackCoefficientDegeneracy_comp_degeneracy
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    nervePullbackCoefficientDegeneracy φ M j ≫
        nervePullbackCoefficientDegeneracy φ M i.castSucc =
      nervePullbackCoefficientDegeneracy φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j.succ := by
  unfold nervePullbackCoefficientDegeneracy
  exact Sigma.map'_comp_eq
    (X₀ := nervePullbackCoefficientFamily φ M n)
    (X₁ := nervePullbackCoefficientFamily φ M (n + 1))
    (X₁' := nervePullbackCoefficientFamily φ M (n + 1))
    (X₂ := nervePullbackCoefficientFamily φ M (n + 2))
    (fun σ => X.σ j σ)
    (fun σ => X.σ i.castSucc σ)
    (nervePullbackCoefficientDegeneracyHom φ M j)
    (nervePullbackCoefficientDegeneracyHom φ M i.castSucc)
    (fun σ => X.σ i σ)
    (fun σ => X.σ j.succ σ)
    (nervePullbackCoefficientDegeneracyHom φ M i)
    (nervePullbackCoefficientDegeneracyHom φ M j.succ)
    (fun σ => SSet.σ_comp_σ_apply (S := X) hij σ)
    (fun σ =>
      nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
        φ M i j hij σ)

end CategoryTheory.CategoryHomology
