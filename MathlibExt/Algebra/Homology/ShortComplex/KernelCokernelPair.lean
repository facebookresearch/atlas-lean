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

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exactness from a kernel-cokernel pair

A kernel-cokernel pair has zero homology even when the ambient category is
neither abelian nor balanced. The given kernel and cokernel supply both
homology data, with the chosen zero object as their homology object.
-/

public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (S : ShortComplex C)

/-- Homology data for a kernel-cokernel pair, with zero homology. -/
noncomputable def homologyDataOfKernelCokernel
    (hk : IsLimit (KernelFork.ofι S.f S.zero))
    (hc : IsColimit (CokernelCofork.ofπ S.g S.zero)) : S.HomologyData := by
  letI : Mono S.f := mono_of_isLimit_fork hk
  letI : Epi S.g := epi_of_isColimit_cofork hc
  let l : S.X₁ ⟶ S.X₁ := hk.lift (KernelFork.ofι S.f S.zero)
  let r : S.X₃ ⟶ S.X₃ := hc.desc (CokernelCofork.ofπ S.g S.zero)
  have hl : l ≫ S.f = S.f := by
    have h := hk.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero
    simpa only [Fork.app_zero_eq_ι, KernelFork.ι_ofι] using h
  have hr : S.g ≫ r = S.g := by
    have h := hc.fac (CokernelCofork.ofπ S.g S.zero) WalkingParallelPair.one
    simpa only [Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using h
  have hl_id : l = 𝟙 S.X₁ := by
    apply (cancel_mono S.f).mp
    exact hl.trans (Category.id_comp S.f).symm
  have hr_id : r = 𝟙 S.X₃ := by
    apply (cancel_epi S.g).mp
    exact hr.trans (Category.comp_id S.g).symm
  let zeroFactorLeft : S.X₁ ⟶ (0 : C) := 0
  let zeroFactorRight : (0 : C) ⟶ S.X₃ := 0
  have wl : l ≫ zeroFactorLeft = 0 := comp_zero
  have wr : zeroFactorRight ≫ r = 0 := zero_comp
  have hLeft : IsColimit (CokernelCofork.ofπ zeroFactorLeft wl) := by
    refine CokernelCofork.IsColimit.ofπ zeroFactorLeft wl (fun _ _ => 0) ?_ ?_
    · intro T u hu
      have hu₀ : u = 0 := by
        calc
          u = 𝟙 S.X₁ ≫ u := (Category.id_comp u).symm
          _ = l ≫ u := by rw [hl_id]
          _ = 0 := hu
      simpa only [comp_zero] using hu₀.symm
    · intro T u hu m hm
      exact (isZero_zero C).eq_of_src m 0
  have hRight : IsLimit (KernelFork.ofι zeroFactorRight wr) := by
    refine KernelFork.IsLimit.ofι zeroFactorRight wr (fun _ _ => 0) ?_ ?_
    · intro T u hu
      have hu₀ : u = 0 := by
        calc
          u = u ≫ 𝟙 S.X₃ := (Category.comp_id u).symm
          _ = u ≫ r := by rw [hr_id]
          _ = 0 := hu
      simpa only [zero_comp] using hu₀.symm
    · intro T u hu m hm
      exact (isZero_zero C).eq_of_tgt m 0
  exact
    { left :=
        { K := S.X₁
          H := 0
          i := S.f
          π := zeroFactorLeft
          wi := S.zero
          hi := hk
          wπ := wl
          hπ := hLeft }
      right :=
        { Q := S.X₃
          H := 0
          p := S.g
          ι := zeroFactorRight
          wp := S.zero
          hp := hc
          wι := wr
          hι := hRight }
      iso := Iso.refl _
      comm := by
        change zeroFactorLeft ≫ (Iso.refl (0 : C)).hom ≫ zeroFactorRight = S.f ≫ S.g
        calc
          zeroFactorLeft ≫ (Iso.refl (0 : C)).hom ≫ zeroFactorRight = 0 := by
            exact zero_comp
          _ = S.f ≫ S.g := S.zero.symm }

/-- A kernel-cokernel pair is short exact in a category with zero morphisms
and a zero object. -/
theorem shortExact_of_kernel_cokernel
    (hk : IsLimit (KernelFork.ofι S.f S.zero))
    (hc : IsColimit (CokernelCofork.ofπ S.g S.zero)) : S.ShortExact where
  exact := ⟨⟨homologyDataOfKernelCokernel S hk hc, isZero_zero C⟩⟩
  mono_f := mono_of_isLimit_fork hk
  epi_g := epi_of_isColimit_cofork hc

end CategoryTheory.ShortComplex
