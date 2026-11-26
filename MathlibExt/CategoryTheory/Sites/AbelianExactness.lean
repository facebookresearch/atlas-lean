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
# Componentwise kernel criteria for additive-group sheaves

Let J be a Grothendieck topology on a category C and S₁ →^f S₂ →^g S₃ a short complex of
additive-group sheaves. If every section map f_U is injective and has image equal to ker(g_U),
then f with fg=0 is a kernel of g. Conversely, a kernel fork gives these component conditions.

When the sheaf category is balanced and S has homology, categorical exactness of S together
with monicity of f is equivalent to those same componentwise conditions. No sectionwise
surjectivity of g is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : ShortComplex (Sheaf J AddCommGrpCat.{w}))

/-- Let J be a Grothendieck topology on C and S a short complex of AddCommGrpCat.{w}-valued
sheaves. Suppose each f_U : S₁(U) → S₂(U) is injective and range(f_U)={x | g_U(x)=0}. Then the
fork with inclusion S.f and zero composite S.f≫S.g is a limiting kernel fork of S.g in the
sheaf category. -/
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

/-- For a short complex S of additive-group sheaves on a site (C,J), if S.f with its zero
composite is a kernel of S.g, then f_U is injective and range(f_U)=ker(g_U) for every U ∈ C.
The conditions follow by evaluating the preserved kernel at each site object. -/
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

/-- Let S be a short complex of AddCommGrpCat.{w}-valued sheaves on (C,J). Assume the sheaf
category is balanced and S.HasHomology. Then S.Exact ∧ Mono(S.f) holds if and only if every
f_U is injective and range(f_U)=ker(g_U). This is a left-exactness criterion using the same
section morphisms. -/
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
