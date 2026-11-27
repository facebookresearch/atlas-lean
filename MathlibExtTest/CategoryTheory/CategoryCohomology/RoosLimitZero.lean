/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosLimitZero

/-!
# Roos degree-zero limit-comparison clients

These clients use the kernel lift and limit projections, including arbitrary
zero-chain indices. The homology comparison requires the individual
complex's degree-zero homology. The bundled natural comparison is tested on
its coefficient-map projection square.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosLimitZeroTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Preadditive A]
  [HasProducts.{max u₁ v₁} A]

/-- A native kernel lift has the actual limit projections at every zero-word index. -/
example (M : I ⥤ A) [HasLimit M] {Z : A}
    (u : Z ⟶ (roosComplex M).X 0) (hu : u ≫ (roosComplex M).d 0 1 = 0)
    (F : ComposableArrows Iᵒᵖ 0) :
    (roosKernelForkIsLimit M).lift (KernelFork.ofι u hu) ≫
        limit.π M (F.left.unop) = u ≫ roosπ M F := by
  fail_if_success
    have : Abelian A := inferInstance
  let X₀ : A := (roosCosimplicial M).obj (SimplexCategory.mk 0)
  let v : Z ⟶ limit M := (roosKernelForkIsLimit M).lift (KernelFork.ofι u hu)
  let l : limit M ⟶ X₀ := roosLimitToZero M
  let u₀ : Z ⟶ X₀ := u
  let p : X₀ ⟶ M.obj F.left.unop := roosπ M F
  have hv : v ≫ l = u₀ :=
    (roosKernelForkIsLimit M).fac (KernelFork.ofι u hu) WalkingParallelPair.zero
  have hl : l ≫ p = limit.π M F.left.unop := roosLimitToZero_π M F
  change v ≫ limit.π M F.left.unop = u₀ ≫ p
  calc
    v ≫ limit.π M F.left.unop = v ≫ (l ≫ p) := congrArg (fun k => v ≫ k) hl.symm
    _ = (v ≫ l) ≫ p := (Category.assoc v l p).symm
    _ = u₀ ≫ p := congrArg (fun k => k ≫ p) hv

/-- The homology class retains every coefficient of an abstractly supplied zero word. -/
example (M : I ⥤ A) [HasLimit M] [(roosComplex M).HasHomology 0]
    (F : ComposableArrows Iᵒᵖ 0) :
    (roosComplex M).homologyπ 0 ≫ (roosHomologyZeroIso M).hom ≫
        limit.π M (F.left.unop) = (roosComplex M).iCycles 0 ≫ roosπ M F := by
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective F
  exact roosHomologyπ_zeroIso_hom_π M i.unop

section NativeFunctors

variable [HasLimitsOfShape I A] [CategoryWithHomology A]

/-- The actual bundled comparison commutes with coefficient maps on native projections. -/
example {M N : I ⥤ A} (α : M ⟶ N) (i : I) :
    (roosComplexFunctor (I := I) (A := A) ⋙
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map α ≫
        (roosHomologyZeroNatIso (I := I) (A := A)).hom.app N ≫ limit.π N i =
      (roosHomologyZeroNatIso (I := I) (A := A)).hom.app M ≫
        limit.π M i ≫ α.app i := by
  have h := congrArg (fun k ↦ k ≫ limit.π N i)
    ((roosHomologyZeroNatIso (I := I) (A := A)).hom.naturality α)
  simpa only [Category.assoc, limit.map_π] using h

end NativeFunctors

end RoosLimitZeroTests

end
