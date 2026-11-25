/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Componentwise kernels of abelian sheaves

Kernels are constructed componentwise without a sheafification or
abelian-sheaf hypothesis. The final equivalence assumes the balanced-category
and homology hypotheses in a common coefficient universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))

/-- The literal componentwise left exact condition constructs the actual
kernel fork, by stock evaluation and full faithful limit reflection. -/
noncomputable def sheafKernelOfComponents
    (hinj : ∀ U : C, Function.Injective (S.f.hom.app (Opposite.op U)))
    (hexact : ∀ U : C, Set.range (S.f.hom.app (Opposite.op U)) =
      {x | S.g.hom.app (Opposite.op U) x = 0}) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  let V := sheafToPresheaf J AddCommGrpCat.{w}
  let T := S.map V
  have hT : IsLimit (KernelFork.ofι T.f T.zero) := by
    apply evaluationJointlyReflectsLimits
    intro U
    let E := (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
    have hmono : Mono (T.map E).f :=
      (AddCommGrpCat.mono_iff_injective _).2 (hinj U.unop)
    letI := hmono
    have hE : (T.map E).Exact := by
      apply (T.map E).ab_exact_iff_range_eq_ker.mpr
      exact SetLike.coe_injective (hexact U.unop)
    exact (KernelFork.isLimitMapConeEquiv _ E).symm hE.fIsKernel
  exact isLimitOfReflects V
    ((KernelFork.isLimitMapConeEquiv _ V).symm hT)

/-- An actual kernel fork gives the literal injectivity and range=kernel
properties of every original component, using only preserved limits. -/
theorem sheaf_components_of_kernel
    (h : IsLimit (KernelFork.ofι S.f S.zero)) :
    (∀ U : C, Function.Injective (S.f.hom.app (Opposite.op U))) ∧
    (∀ U : C, Set.range (S.f.hom.app (Opposite.op U)) =
      {x | S.g.hom.app (Opposite.op U) x = 0}) := by
  let V := sheafToPresheaf J AddCommGrpCat.{w}
  let T := S.map V
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    KernelFork.mapIsLimit _ h V
  have hU (U : C) : (T.map ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op U))).Exact ∧
      Mono (T.map ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op U))).f := by
    apply (exact_and_mono_f_iff_f_is_kernel _).mpr
    exact ⟨KernelFork.mapIsLimit _ hT ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op U))⟩
  constructor
  · intro U
    exact (AddCommGrpCat.mono_iff_injective _).mp (hU U).2
  · intro U
    exact congrArg SetLike.coe (hU U).1.ab_range_eq_ker

/-- With the stock balanced-category and homology hypotheses, categorical
left exactness is equivalent to its literal original components. -/
theorem sheaf_exact_mono_iff_components
    [Balanced (Sheaf J AddCommGrpCat.{w})] [S.HasHomology] :
    S.Exact ∧ Mono S.f ↔
      (∀ U : C, Function.Injective (S.f.hom.app (Opposite.op U))) ∧
      (∀ U : C, Set.range (S.f.hom.app (Opposite.op U)) =
        {x | S.g.hom.app (Opposite.op U) x = 0}) := by
  constructor
  · rintro ⟨hS, hmono⟩
    let := hmono
    exact S.sheaf_components_of_kernel hS.fIsKernel
  · rintro ⟨hinj, hexact⟩
    exact S.exact_and_mono_f_iff_f_is_kernel.mpr ⟨S.sheafKernelOfComponents hinj hexact⟩

end CategoryTheory.ShortComplex
