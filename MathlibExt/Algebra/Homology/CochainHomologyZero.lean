/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Degree-zero cohomology as the first differential kernel

For a nonnegative cochain complex K in a category with zero morphisms, assume its degree-zero
homology exists. The cycles-to-homology isomorphism at zero gives an inclusion H⁰(K) → K⁰
whose composite with d⁰ is zero. This inclusion has the kernel universal property.

When a chosen kernel of d⁰ is available, the universal property gives H⁰(K) ≅ ker(d⁰),
preserving the inclusion. The cohomology inclusion is natural in cochain maps, at the stated
object and morphism universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section HomologyZero

variable (K : CochainComplex C ℕ) [K.HasHomology 0]

/-- The degree-zero cohomology inclusion.

Identify H⁰(K) with its cycles and then include those cycles into K⁰. -/
def cohomologyZeroι : K.homology 0 ⟶ K.X 0 :=
  K.isoHomologyπ₀.inv ≫ K.iCycles 0

/-- The cohomology inclusion is killed by the first differential.

The composite H⁰(K) → K⁰ → K¹ is zero. -/
@[reassoc (attr := simp)] theorem cohomologyZeroι_comp_d :
    cohomologyZeroι K ≫ K.d 0 1 = 0 := by
  rw [cohomologyZeroι, Category.assoc, K.iCycles_d 0 1, comp_zero]

/-- The kernel fork defined by degree-zero cohomology.

The cohomology inclusion H⁰(K) → K⁰ and its zero composite with d⁰ form a kernel fork. -/
def cohomologyZeroFork : KernelFork (K.d 0 1) :=
  KernelFork.ofι (cohomologyZeroι K) (cohomologyZeroι_comp_d K)

/-- The kernel universal property of degree-zero cohomology.

The fork with point H⁰(K) is limiting, obtained from the cycle kernel through the degree-zero
cycles-to-homology isomorphism. -/
def cohomologyZeroForkIsLimit : IsLimit (cohomologyZeroFork K) := by
  let c : KernelFork (K.d 0 1) := KernelFork.ofι (K.iCycles 0) (K.iCycles_d 0 1)
  have hc : IsLimit c := K.cyclesIsKernel (i := 0) (j := 1) (by simp)
  let e : c ≅ cohomologyZeroFork K :=
    Fork.ext K.isoHomologyπ₀ (by
      change K.isoHomologyπ₀.hom ≫ (K.isoHomologyπ₀.inv ≫ K.iCycles 0) = K.iCycles 0
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ K.iCycles 0) K.isoHomologyπ₀.hom_inv_id).trans
          (Category.id_comp _)))
  exact IsLimit.ofIsoLimit hc e

variable [HasKernel (K.d 0 1)]

/-- The canonical isomorphism with the first differential kernel.

With a chosen kernel of d⁰, identify H⁰(K) with ker(d⁰) through their common kernel universal
property. -/
def cohomologyZeroIsoKernel : K.homology 0 ≅ kernel (K.d 0 1) :=
  IsLimit.conePointUniqueUpToIso
    (s := cohomologyZeroFork K)
    (t := KernelFork.ofι (kernel.ι (K.d 0 1)) (kernel.condition (K.d 0 1)))
    (cohomologyZeroForkIsLimit K) (kernelIsKernel (K.d 0 1))

/-- The degree-zero kernel isomorphism preserves inclusion.

The forward comparison followed by the chosen kernel inclusion equals cohomologyZeroι K. -/
@[reassoc (attr := simp)] theorem cohomologyZeroIsoKernel_ι :
    (cohomologyZeroIsoKernel K).hom ≫ kernel.ι (K.d 0 1) = cohomologyZeroι K :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (s := cohomologyZeroFork K)
    (t := KernelFork.ofι (kernel.ι (K.d 0 1)) (kernel.condition (K.d 0 1)))
    (cohomologyZeroForkIsLimit K) (kernelIsKernel (K.d 0 1)) WalkingParallelPair.zero

end HomologyZero

variable {K L : CochainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- Naturality of the degree-zero cohomology inclusion.

For φ : K → L, H⁰(φ) followed by the inclusion for L equals the inclusion for K followed by
φ⁰. -/
@[reassoc] theorem cohomologyZeroι_naturality (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ cohomologyZeroι L =
      cohomologyZeroι K ≫ φ.f 0 := by
  unfold cohomologyZeroι
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]

end CochainComplex

end
