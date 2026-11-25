/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChainComplexKernelTail
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Projective resolution of the kernel of a degree-zero augmentation

In an abelian category, a projective resolution `P` of `X` has an epi
augmentation `π₀ : P₀ → X`. Restricting to the terms `P_(n+1)` gives
a projective resolution of `ker(π₀)`. Its augmentation is the lift
of `d_P : P₁ → P₀` through the kernel inclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]

local instance : ChainComplex.kernelTailEmbedding.IsRelIff :=
  ComplexShape.instIsRelIffEmbeddingDown'Add 1 1

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution of
`X` with degree-zero augmentation `π₀ : P₀ → X`. The restricted tail
with degree-`n` term identified with `P_(n+1)` and augmentation induced
by `d_P : P₁ → P₀` is a projective resolution of `ker(π₀)`. -/
def normalizationKernelTail {X : C} (P : ProjectiveResolution X) :
    ProjectiveResolution (kernel (P.π.f 0)) where
  complex := P.complex.restriction ChainComplex.kernelTailEmbedding
  projective n := by
    have h : (P.complex.restriction ChainComplex.kernelTailEmbedding).X n =
        P.complex.X (n + 1) := by
      change P.complex.X (ChainComplex.kernelTailEmbedding.f n) = P.complex.X (n + 1)
      rw [ChainComplex.kernelTailEmbedding_f]
    rw [h]
    infer_instance
  π := ChainComplex.kernelTailAugmentation P.π
  quasiIso := ChainComplex.quasiIso_kernelTailAugmentation P.π

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. In each degree `n`, the kernel-tail term `T_n` is canonically
isomorphic to the next original resolution term `P_(n+1)`. -/
def normalizationKernelTailXIso {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationKernelTail P).complex.X n ≅ P.complex.X (n + 1) :=
  P.complex.restrictionXIso ChainComplex.kernelTailEmbedding
    (ChainComplex.kernelTailEmbedding_f n)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The augmentation `T₀ → K` is the unique factorization of
`d_P : P₁ → P₀` through the kernel inclusion `K → P₀`, under
`T₀ ≅ P₁`. -/
theorem normalizationKernelTail_π_f_zero {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTail P).π.f 0 =
      kernel.lift (P.π.f 0) (P.complex.d 1 0) P.complex_d_comp_π_f_zero :=
  ChainComplex.kernelTailAugmentation_f_zero P.π

end CategoryTheory.ProjectiveResolution
