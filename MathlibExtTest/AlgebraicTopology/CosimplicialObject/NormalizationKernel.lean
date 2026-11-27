/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.CosimplicialObject.NormalizationKernel

/-!
# Lifting through cosimplicial normalization

These clients use the normalization inclusion as the common codegeneracy
kernel. They check lifting, the projection formula and uniqueness through the
specified normalization maps.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A map into full degree n+1 has a unique normalized lift when the joint codegeneracy vanishes. -/
example (X : CosimplicialObject A) (n : ℕ) {T : A}
    (g : T ⟶ X.obj (SimplexCategory.mk (n + 1))) (hg : g ≫ codegeneracyProduct X n = 0) :
    ∃! u : T ⟶ ((normalizedCofaceMapComplex A).obj X).X (n + 1),
      u ≫ ((inclusionOfNormalizedCofaceMapComplex A).app X).f (n + 1) = g := by
  let K := KernelFork.ofι g hg
  let hK := normalizationKernelIsLimit X n
  refine ⟨hK.lift K, hK.fac K WalkingParallelPair.zero, ?_⟩
  intro u hu
  apply Fork.IsLimit.hom_ext hK
  exact hu.trans (hK.fac K WalkingParallelPair.zero).symm

end
