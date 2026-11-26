/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.Algebra.Homology.ChainComplexAugmentation
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Two-term projective resolutions

A short exact presentation with projective middle and first objects gives
a two-term projective resolution. Its differential and augmentation are
the specified presentation maps.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short exact presentation has its objects in degrees zero and one. -/
def presentationX (S : ShortComplex C) : ℕ → C
  | 0 => S.X₂
  | 1 => S.X₁
  | _ + 2 => 0

/-- The only nonzero differential is the presentation map. -/
def presentationD (S : ShortComplex C) : (n : ℕ) → presentationX S (n + 1) ⟶ presentationX S n
  | 0 => S.f
  | _ + 1 => 0

/-- The chain complex of the given presentation. -/
def presentationComplex (S : ShortComplex C) : ChainComplex C ℕ :=
  ChainComplex.of (presentationX S) (presentationD S) (by
    intro n
    cases n <;> exact zero_comp)

/-- The first differential is the presentation map. -/
theorem presentationComplex_d_zero (S : ShortComplex C) :
    (presentationComplex S).d 1 0 = S.f :=
  (ChainComplex.of_d (presentationX S) (presentationD S) 0).trans rfl

/-- Every later differential of the two-term complex vanishes. -/
theorem presentationComplex_d_succ (S : ShortComplex C) (n : ℕ) :
    (presentationComplex S).d (n + 2) (n + 1) = 0 :=
  (ChainComplex.of_d (presentationX S) (presentationD S) (n + 1)).trans rfl

/-- Its augmentation uses the quotient map. -/
def presentationAugmentation (S : ShortComplex C) :
    presentationComplex S ⟶ (ChainComplex.single₀ C).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv (presentationComplex S) S.X₃).symm
    ⟨S.g, by
      rw [presentationComplex_d_zero]
      exact S.zero⟩

/-- The degree-zero augmentation is the exact quotient map. -/
theorem presentationAugmentation_f_zero (S : ShortComplex C) :
    (presentationAugmentation S).f 0 = S.g :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- A short exact presentation resolves the object. -/
theorem presentationAugmentation_quasiIso (S : ShortComplex C) (hS : S.ShortExact) :
    QuasiIso (presentationAugmentation S) := by
  apply (quasiIso_iff _).mpr
  intro n
  cases n with
  | zero =>
      apply (ChainComplex.quasiIsoAt_zero_iff_exact_and_epi_augmentation _).mpr
      constructor
      · simp only [presentationAugmentation_f_zero, presentationComplex_d_zero]
        change S.Exact
        exact hS.exact
      · simp only [presentationAugmentation_f_zero]
        change Epi S.g
        exact hS.epi_g
  | succ n =>
      apply (quasiIsoAt_iff_exactAt' _ (n + 1)
        (ChainComplex.exactAt_succ_single_obj S.X₃ n)).mpr
      cases n with
      | zero =>
          apply (HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)).mpr
          simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
            presentationComplex_d_zero, presentationComplex_d_succ]
          exact (ShortComplex.exact_iff_mono _ rfl).mpr hS.mono_f
      | succ n =>
          apply ShortComplex.exact_of_isZero_X₂
          change IsZero (0 : C)
          exact isZero_zero C

/-- The given presentation is an projective resolution. -/
def ofPresentation (S : ShortComplex C) (hS : S.ShortExact)
    [Projective S.X₁] [Projective S.X₂] : ProjectiveResolution S.X₃ where
  complex := presentationComplex S
  projective n := by
    cases n with
    | zero => change Projective S.X₂; infer_instance
    | succ n =>
      cases n with
      | zero => change Projective S.X₁; infer_instance
      | succ n => change Projective (0 : C); exact (isZero_zero C).projective
  π := presentationAugmentation S
  quasiIso := presentationAugmentation_quasiIso S hS

end CategoryTheory.ProjectiveResolution
