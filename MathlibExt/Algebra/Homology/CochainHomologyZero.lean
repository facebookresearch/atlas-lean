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
# The actual degree-zero cohomology inclusion as a kernel

Only the selected-degree homology of the actual nonnegative cochain complex
is used. The native cycles-to-homology isomorphism transports its existing
cycle kernel; no cohomology comparison is supplied as a hypothesis.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section HomologyZero

variable (K : CochainComplex C ℕ) [K.HasHomology 0]

/-- The actual degree-zero cohomology inclusion into the original term. -/
def cohomologyZeroι : K.homology 0 ⟶ K.X 0 :=
  K.isoHomologyπ₀.inv ≫ K.iCycles 0

@[reassoc (attr := simp)] theorem cohomologyZeroι_comp_d :
    cohomologyZeroι K ≫ K.d 0 1 = 0 := by
  rw [cohomologyZeroι, Category.assoc, K.iCycles_d 0 1, comp_zero]

/-- The native degree-zero cohomology inclusion as a kernel fork of the actual d₀. -/
def cohomologyZeroFork : KernelFork (K.d 0 1) :=
  KernelFork.ofι (cohomologyZeroι K) (cohomologyZeroι_comp_d K)

/-- Degree-zero cohomology earns the native cycle kernel universal property. -/
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

/-- The actual degree-zero cohomology object is the native kernel of its differential. -/
def cohomologyZeroIsoKernel : K.homology 0 ≅ kernel (K.d 0 1) :=
  IsLimit.conePointUniqueUpToIso
    (s := cohomologyZeroFork K)
    (t := KernelFork.ofι (kernel.ι (K.d 0 1)) (kernel.condition (K.d 0 1)))
    (cohomologyZeroForkIsLimit K) (kernelIsKernel (K.d 0 1))

@[reassoc (attr := simp)] theorem cohomologyZeroIsoKernel_ι :
    (cohomologyZeroIsoKernel K).hom ≫ kernel.ι (K.d 0 1) = cohomologyZeroι K :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (s := cohomologyZeroFork K)
    (t := KernelFork.ofι (kernel.ι (K.d 0 1)) (kernel.condition (K.d 0 1)))
    (cohomologyZeroForkIsLimit K) (kernelIsKernel (K.d 0 1)) WalkingParallelPair.zero

end HomologyZero

variable {K L : CochainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- Every actual cochain map preserves the native degree-zero cohomology inclusion. -/
@[reassoc] theorem cohomologyZeroι_naturality (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ cohomologyZeroι L =
      cohomologyZeroι K ≫ φ.f 0 := by
  unfold cohomologyZeroι
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]

end CochainComplex

end
