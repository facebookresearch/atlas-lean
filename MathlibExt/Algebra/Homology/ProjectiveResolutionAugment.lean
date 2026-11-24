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

This file packages the augmented chain complex of a projective resolution,
proves it acyclic, and records the general implication from acyclicity of an
augmented complex to quasi-isomorphism of its augmentation.
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
/-- Insert the resolved object in degree zero below a projective resolution. -/
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
/-- The augmented chain complex of a projective resolution is acyclic. -/
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
/-- An augmentation is a quasi-isomorphism when its augmented complex is
acyclic. -/
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
          all_goals simp [hπ]
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
