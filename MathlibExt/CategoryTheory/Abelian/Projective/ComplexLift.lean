/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Lifting projective complexes to projective resolutions

An augmented nonnegative chain complex whose terms are projective admits a
comparison map to any projective resolution of its augmentation target. The
source complex need not be exact or bounded.

The construction follows the usual comparison theorem for projective
resolutions: factor the degree-zero map through the target augmentation,
then lift inductively through the exact short complexes in the target
resolution.

## Main declarations

* `CategoryTheory.ProjectiveResolution.liftFromComplex`
* `CategoryTheory.ProjectiveResolution.liftFromComplex_f_zero_comp`
* `CategoryTheory.ProjectiveResolution.liftFromComplex_commutes`
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Y Z : C}

private def liftFromComplexFZero
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    K.X 0 ⟶ Q.complex.X 0 := by
  let _ : Projective (K.X 0) := hK 0
  exact Projective.factorThru (ε.f 0 ≫ f) (Q.π.f 0)

private theorem liftFromComplexFZero_comp
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    liftFromComplexFZero f K ε Q hK ≫ Q.π.f 0 = ε.f 0 ≫ f := by
  let _ : Projective (K.X 0) := hK 0
  apply Projective.factorThru_comp

private def liftFromComplexFOne
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    K.X 1 ⟶ Q.complex.X 1 := by
  let _ : Projective (K.X 1) := hK 1
  exact Q.exact₀.liftFromProjective
    (K.d 1 0 ≫ liftFromComplexFZero f K ε Q hK) (by
      rw [Category.assoc, liftFromComplexFZero_comp]
      have hε : K.d 1 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm 1 0]
        simp
      rw [← Category.assoc, hε, zero_comp])

private theorem liftFromComplexFOne_zero_comm
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    liftFromComplexFOne f K ε Q hK ≫ Q.complex.d 1 0 =
      K.d 1 0 ≫ liftFromComplexFZero f K ε Q hK := by
  let _ : Projective (K.X 1) := hK 1
  apply Q.exact₀.liftFromProjective_comp

private def liftFromComplexFSucc
    (K : ChainComplex C ℕ) (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) (n : ℕ)
    (g : K.X n ⟶ Q.complex.X n)
    (g' : K.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = K.d (n + 1) n ≫ g) :
    Σ' g'' : K.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) =
        K.d (n + 2) (n + 1) ≫ g' := by
  let _ : Projective (K.X (n + 2)) := hK (n + 2)
  exact ⟨(Q.exact_succ n).liftFromProjective
    (K.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- A morphism from the augmentation target of a projective complex to the
object resolved by `Q` lifts to a chain map into `Q`. Source exactness and
boundedness are not required. -/
@[no_expose]
def liftFromComplex
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    K ⟶ Q.complex :=
  ChainComplex.mkHom K Q.complex
    (liftFromComplexFZero f K ε Q hK)
    (liftFromComplexFOne f K ε Q hK)
    (liftFromComplexFOne_zero_comm f K ε Q hK)
    (fun n p ↦ liftFromComplexFSucc K Q hK n p.1 p.2.1 p.2.2)

/-- The degree-zero component of `liftFromComplex` factors the source
augmentation followed by the chosen map. -/
@[reassoc (attr := simp)]
theorem liftFromComplex_f_zero_comp
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    (liftFromComplex f K ε Q hK).f 0 ≫ Q.π.f 0 = ε.f 0 ≫ f := by
  rw [liftFromComplex, ChainComplex.mkHom_f_0]
  exact liftFromComplexFZero_comp f K ε Q hK

/-- The lifted chain map commutes with the source and target augmentations. -/
@[reassoc (attr := simp)]
theorem liftFromComplex_commutes
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    liftFromComplex f K ε Q hK ≫ Q.π =
      ε ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      simpa only [HomologicalComplex.comp_f,
        ChainComplex.single₀_map_f_zero] using
          liftFromComplex_f_zero_comp f K ε Q hK
  | succ n =>
      have hε : ε.f (n + 1) = 0 :=
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 Y (n + 1) (by omega)).eq_of_tgt _ _
      simp only [HomologicalComplex.comp_f,
        ProjectiveResolution.π_f_succ, comp_zero, hε, zero_comp]

end CategoryTheory.ProjectiveResolution
