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
# The kernel tail of an original projective resolution
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
/-- The kernel-augmented restricted tail is a projective resolution. -/
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

/-- The original restricted-tail degree is canonically the next original degree. -/
def normalizationKernelTailXIso {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationKernelTail P).complex.X n ≅ P.complex.X (n + 1) :=
  P.complex.restrictionXIso ChainComplex.kernelTailEmbedding
    (ChainComplex.kernelTailEmbedding_f n)

/-- The augmentation of the original kernel tail retains the original kernel lift. -/
theorem normalizationKernelTail_π_f_zero {X : C} (P : ProjectiveResolution X) :
    (normalizationKernelTail P).π.f 0 =
      kernel.lift (P.π.f 0) (P.complex.d 1 0) P.complex_d_comp_π_f_zero :=
  ChainComplex.kernelTailAugmentation_f_zero P.π

end CategoryTheory.ProjectiveResolution
