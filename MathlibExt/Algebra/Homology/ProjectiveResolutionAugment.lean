/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.Augment

/-!
# Augmented projective resolutions

Let P be a natural-number-indexed projective resolution of an object Z. Its augmented complex
has Z in degree zero and Pₙ in degree n+1, with the augmentation P₀ → Z as the first
differential. In an abelian category this augmented complex has zero homology in every degree.

More generally, if a nonnegative complex K has an augmentation K₀ → X whose augmented complex is
acyclic, the associated map K → X[0] is a quasi-isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- Let C have a zero object and zero morphisms, and let P be a projective resolution of Z indexed
by ℕ. Its augmented complex has Z in degree zero and Pₙ in degree n+1. The first differential is
the augmentation P₀ → Z, and the subsequent differentials are those of P. -/
noncomputable def augmented [HasZeroObject C] [HasZeroMorphisms C]
    {Z : C} (P : ProjectiveResolution Z) : ChainComplex C ℕ :=
  P.complex.augment (P.π.f 0 : P.complex.X 0 ⟶ Z)
    P.complex_d_comp_π_f_zero

@[simp]
theorem augmented_X_zero [HasZeroObject C] [HasZeroMorphisms C]
    {Z : C} (P : ProjectiveResolution Z) :
    P.augmented.X 0 = Z :=
  rfl

@[simp]
theorem augmented_X_succ [HasZeroObject C] [HasZeroMorphisms C]
    {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
    P.augmented.X (n + 1) = P.complex.X n :=
  rfl

@[simp]
theorem augmented_d_one_zero [HasZeroObject C] [HasZeroMorphisms C]
    {Z : C} (P : ProjectiveResolution Z) :
    P.augmented.d 1 0 = P.π.f 0 :=
  rfl

@[simp]
theorem augmented_d_succ_succ [HasZeroObject C] [HasZeroMorphisms C]
    {Z : C} (P : ProjectiveResolution Z) (n m : ℕ) :
    P.augmented.d (n + 1) (m + 1) = P.complex.d n m := by
  exact ChainComplex.augment_d_succ_succ _ _ _ n m

variable [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Let C be an abelian category. For a natural-number-indexed projective resolution P of Z, the
augmented complex with Z in degree zero and Pₙ in degree n+1 is acyclic: every homology object
Hₙ(P.augmented), n ∈ ℕ, is zero. -/
theorem augmented_acyclic {Z : C} (P : ProjectiveResolution Z) :
    P.augmented.Acyclic := by
  intro i
  rcases i with (_ | _ | n)
  · rw [HomologicalComplex.exactAt_iff'
      P.augmented 1 0 0 (by simp) (by simp)]
    apply (ShortComplex.exact_iff_epi _ rfl).2
    change Epi (P.π.f 0 : P.complex.X 0 ⟶ Z)
    exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  · rw [HomologicalComplex.exactAt_iff'
      P.augmented 2 1 0 (by simp) (by simp)]
    change (ShortComplex.mk (P.complex.d 1 0)
      (P.π.f 0 : P.complex.X 0 ⟶ Z) P.complex_d_comp_π_f_zero).Exact
    exact P.exact₀
  · rw [HomologicalComplex.exactAt_iff'
      P.augmented (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
    change (ShortComplex.mk
      (P.complex.d (n + 2) (n + 1))
      (P.complex.d (n + 1) n)
      (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact
    exact P.exact_succ n

end CategoryTheory.ProjectiveResolution

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Let C be an abelian category. Let K be a natural-number-indexed chain complex, X an object, and
f : K₀ → X with f ∘ d_K^{1,0}=0. If the augmented complex X ← K₀ ← K₁ ← ⋯ is acyclic, then the
associated augmentation map K → X[0] is a quasi-isomorphism. -/
theorem quasiIso_toSingle₀_of_augment_acyclic
    (K : ChainComplex C ℕ) (X : C) (f : K.X 0 ⟶ X)
    (w : K.d 1 0 ≫ f = 0) (h : (K.augment f w).Acyclic) :
    QuasiIso ((toSingle₀Equiv K X).symm ⟨f, w⟩) := by
  let π := (toSingle₀Equiv K X).symm ⟨f, w⟩
  change QuasiIso π
  have hπ : π.f 0 = f := by
    dsimp only [π]
    exact toSingle₀Equiv_symm_apply_f_zero f w
  constructor
  intro i
  cases i with
  | zero =>
      rw [quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · have h₁ := h 1
          rw [HomologicalComplex.exactAt_iff'
            (K.augment f w) 2 1 0 (by simp) (by simp)] at h₁
          change (ShortComplex.mk (K.d 1 0) f w).Exact at h₁
          change (ShortComplex.mk (K.d 1 0) (π.f 0) _).Exact
          convert h₁ using 1
          simp [hπ]
        · have h₀ := h 0
          rw [HomologicalComplex.exactAt_iff'
            (K.augment f w) 1 0 0 (by simp) (by simp)] at h₀
          let _ : Epi f :=
            ((K.augment f w).sc' 1 0 0).exact_iff_epi rfl |>.1 h₀
          change Epi (π.f 0)
          rw [hπ]
          infer_instance
      all_goals simp
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · have hn := h (n + 2)
        rw [HomologicalComplex.exactAt_iff'
          (K.augment f w) (n + 3) (n + 2) (n + 1)
            (by simp) (by simp)] at hn
        rw [HomologicalComplex.exactAt_iff'
          K (n + 2) (n + 1) n (by simp) (by simp)]
        change (ShortComplex.mk
          (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
          (K.d_comp_d (n + 2) (n + 1) n)).Exact at hn ⊢
        exact hn
      · exact exactAt_succ_single_obj X n

end ChainComplex

end
