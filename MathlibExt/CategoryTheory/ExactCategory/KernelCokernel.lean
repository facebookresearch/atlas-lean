/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import MathlibExt.Algebra.Homology.ShortComplex.KernelCokernelPair

/-!
# Admissible exactness from an admissible epi and its kernel

The kernel of an admissible epimorphism belongs to its admissible exact
sequence. Its universal property identifies any given kernel with that
presentation, while retaining the given middle and quotient objects.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- An admissible epimorphism together with a kernel first map determines
an admissible exact short complex. -/
theorem isAdmissibleExact_of_isAdmissibleEpi_isLimit {S : ShortComplex C}
    (hg : IsAdmissibleEpi S.g)
    (hk : IsLimit (KernelFork.ofι S.f S.zero)) : IsAdmissibleExact S := by
  obtain ⟨K, i, w, hT⟩ := hg
  let hk' := isLimit_kernelFork_of_isAdmissibleExact hT
  let e : S.X₁ ≅ K := hk.conePointUniqueUpToIso hk'
  have he : e.hom ≫ i = S.f := by
    have h := IsLimit.conePointUniqueUpToIso_hom_comp hk hk' WalkingParallelPair.zero
    simpa [KernelFork.ofι] using h
  let eS : S ≅ ShortComplex.mk i S.g w :=
    ShortComplex.isoMk e (Iso.refl S.X₂) (Iso.refl S.X₃)
      (by simpa using he) (by simp)
  exact isAdmissibleExact_of_iso eS.symm hT

end CategoryTheory.ExactCategory
