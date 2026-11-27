/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.FiveLemma

/-!
# Degree-one Ext under exact full faithful functors

An exact full faithful functor induces an injective map on degree-one Ext.
The proof uses an injective presentation, the connecting maps and the
four lemma. Degree-zero Ext is preserved bijectively.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e e' v v' u u' r

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{e} C] [HasExt.{e'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful]

/-- Degree-zero Ext is preserved bijectively by the exact full faithful functor. -/
theorem Functor.mapExtAddHom_zero_bijective (X Y : C) :
    Function.Bijective (F.mapExtAddHom X Y 0) := by
  simpa [Abelian.Ext.mapExactFunctor₀] using
    (show Function.Bijective (F.map : (X ⟶ Y) →
      (F.obj X ⟶ F.obj Y)) from
        ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩)

/-- The degree-one Ext map is injective for an exact full faithful
functor, without an injective-preservation premise. -/
theorem Functor.mapExtAddHom_one_injective [EnoughInjectives C] (X Y : C) :
    Function.Injective (F.mapExtAddHom X Y 1) := by
  let S := ShortComplex.mk (Injective.ι Y)
    (cokernel.π (Injective.ι Y)) (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (Injective.ι Y)) }
  let hT := hS.map_of_exact F
  exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact
    ((Abelian.Ext.mk₀ S.g).postcomp X (add_zero 0))
    (hS.extClass.postcomp X (rfl : 0 + 1 = 1))
    ((Abelian.Ext.mk₀ (F.map S.g)).postcomp (F.obj X) (add_zero 0))
    (hT.extClass.postcomp (F.obj X) (rfl : 0 + 1 = 1))
    (F.mapExtAddHom X S.X₂ 0)
    (F.mapExtAddHom X S.X₃ 0)
    (F.mapExtAddHom X S.X₁ 1)
    (by
      apply AddMonoidHom.ext
      intro z
      change (z.mapExactFunctor F).comp (Abelian.Ext.mk₀ (F.map S.g)) (add_zero 0) =
        (z.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)).mapExactFunctor F
      rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀])
    (by
      apply AddMonoidHom.ext
      intro z
      change (z.mapExactFunctor F).comp hT.extClass (rfl : 0 + 1 = 1) =
        (z.comp hS.extClass (rfl : 0 + 1 = 1)).mapExactFunctor F
      rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass])
    ((ShortComplex.ab_exact_iff_function_exact _).1
      (Abelian.Ext.covariant_sequence_exact₃' X hS 0 1 rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).1
      (Abelian.Ext.covariant_sequence_exact₃' (F.obj X) hT 0 1 rfl))
    (F.mapExtAddHom_zero_bijective X S.X₂).surjective
    (F.mapExtAddHom_zero_bijective X S.X₃).injective
    (fun z ↦ Abelian.Ext.covariant_sequence_exact₁ X hS z
      (Abelian.Ext.eq_zero_of_injective _) rfl)

/-- The same injection for the linear Ext map.
The scalar ring and both category/Ext universes remain independent. -/
theorem Functor.mapExtLinearMap_one_injective [EnoughInjectives C]
    (R : Type r) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    [CategoryTheory.Functor.Linear R F] (X Y : C) :
    Function.Injective (F.mapExtLinearMap R X Y 1) :=
  F.mapExtAddHom_one_injective X Y

end CategoryTheory
