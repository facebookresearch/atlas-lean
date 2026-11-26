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
# Lifting augmented projective chain complexes

In an abelian category `C`, a natural-index chain complex `K` with
projective terms and augmentation `ε : K → Y[0]` admits a chain
map into any projective resolution of `Z`, extending any `f : Y → Z`.
No exactness of the source augmentation is required.
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

/-- In an abelian category `C`, let `K` be a chain complex on `ℕ`
with projective terms, augmented to `Y` by `ε`, and let `Q`
resolve `Z`. Every `f : Y → Z` lifts to a chain map
`K → Q.complex` commuting with these augmentations. -/
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

/-- For an augmented chain complex `K` with projective terms in an
abelian category `C`, map `f : Y → Z`, and projective resolution
`Q` of `Z`, the lifted degree-zero map satisfies
`lift₀ ≫ Q.π₀ = ε₀ ≫ f`. -/
@[reassoc (attr := simp)]
theorem liftFromComplex_f_zero_comp
    (f : Y ⟶ Z) (K : ChainComplex C ℕ)
    (ε : K ⟶ (ChainComplex.single₀ C).obj Y)
    (Q : ProjectiveResolution Z)
    (hK : ∀ n, Projective (K.X n)) :
    (liftFromComplex f K ε Q hK).f 0 ≫ Q.π.f 0 = ε.f 0 ≫ f := by
  rw [liftFromComplex, ChainComplex.mkHom_f_0]
  exact liftFromComplexFZero_comp f K ε Q hK

/-- For an abelian category `C`, augmented projective-term complex
`K → Y[0]`, projective resolution `Q` of `Z`, and map `f : Y → Z`,
the lifted chain map satisfies `lift ≫ Q.π = ε ≫ single₀(f)`. -/
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
