/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentation

/-!
# Public uses of augmentation exactness

The actual augmentation has the cokernel universal property, and its actual
kernel lift supports cancellation, without projectivity or positive-degree
quasi-isomorphism assumptions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplexAugmentationTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Q : ChainComplex C ℕ} {M : C}
variable (π : Q ⟶ (ChainComplex.single₀ C).obj M) [QuasiIsoAt π 0]

example (Y : C) (f : Q.X 0 ⟶ Y) (hf : Q.d 1 0 ≫ f = 0) :
    ∃! g : M ⟶ Y, π.f 0 ≫ g = f := by
  have : Epi (π.f 0) := ChainComplex.epi_augmentation_f_zero π
  let hc := (ChainComplex.exact_augmentation π).gIsCokernel
  let g := (CokernelCofork.IsColimit.desc' hc f hf).1
  have hg : π.f 0 ≫ g = f := (CokernelCofork.IsColimit.desc' hc f hf).2
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact Cofork.IsColimit.hom_ext hc (hg'.trans hg.symm)

example (Y : C) (a b : kernel (π.f 0) ⟶ Y)
    (h : kernel.lift (π.f 0) (Q.d 1 0)
        ((ChainComplex.toSingle₀Equiv Q M) π).property ≫ a =
      kernel.lift (π.f 0) (Q.d 1 0)
        ((ChainComplex.toSingle₀Equiv Q M) π).property ≫ b) : a = b := by
  have : Epi (kernel.lift (π.f 0) (Q.d 1 0)
    ((ChainComplex.toSingle₀Equiv Q M) π).property) :=
    ChainComplex.epi_kernelLift_augmentation π
  exact (cancel_epi _).mp h

end ChainComplexAugmentationTests

end
