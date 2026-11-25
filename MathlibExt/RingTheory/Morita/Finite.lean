/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import MathlibExt.Algebra.Category.ModuleCat.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

instance isFG_isClosedUnderIsomorphisms {R : Type u} [Ring R] :
    (isFG.{v} (R := R)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : Module.Finite R X := hX
    exact Module.Finite.equiv e.toLinearEquiv

instance isFGProjective_isClosedUnderIsomorphisms {R : Type u} [Ring R] :
    (isFGProjective.{v} (R := R)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hFin, hProj⟩ := hX
    constructor
    · have : Module.Finite R X := hFin
      exact Module.Finite.equiv e.toLinearEquiv
    · have : Module.Projective R X := hProj
      exact Module.Projective.of_equiv' e.toLinearEquiv

end ModuleCat

universe u₀ u₁ u₂

variable {R₀ : Type u₀} [CommSemiring R₀] {A : Type u₁} [Ring A] [Algebra R₀ A]
  {B : Type u₂} [Ring B] [Algebra R₀ B]

namespace MoritaEquivalence

private theorem projective_iff (e : MoritaEquivalence R₀ A B)
    (X : ModuleCat.{max u₁ u₂} A) :
    Module.Projective A X ↔ Module.Projective B (e.eqv.functor.obj X) := by
  simpa [IsProjective.iff_projective] using (e.eqv.map_projective_iff X).symm

/-- Morita equivalence restricts to finitely generated modules, with no Noetherian hypotheses
on the restricted equivalence itself. -/
noncomputable def fgModuleCatEquivalence (e : MoritaEquivalence R₀ A B) :
    FGModuleCat.{max u₁ u₂} A ≌ FGModuleCat.{max u₁ u₂} B :=
  e.eqv.congrFullSubcategory (by
    ext X
    exact (ModuleCat.finite_iff e.eqv X).symm)

/-- Morita equivalence restricts to finitely generated projective modules, with no Noetherian
hypotheses. -/
noncomputable def fgProjectiveCatEquivalence (e : MoritaEquivalence R₀ A B) :
    FGProjectiveCat.{max u₁ u₂} A ≌ FGProjectiveCat.{max u₁ u₂} B :=
  e.eqv.congrFullSubcategory (by
    ext X
    constructor
    · rintro ⟨hFinB, hProjB⟩
      exact ⟨(ModuleCat.finite_iff e.eqv X).mpr hFinB, (projective_iff e X).mpr hProjB⟩
    · rintro ⟨hFinA, hProjA⟩
      exact ⟨(ModuleCat.finite_iff e.eqv X).mp hFinA, (projective_iff e X).mp hProjA⟩)

instance fgModuleCatEquivalence_additive (e : MoritaEquivalence R₀ A B) :
    e.fgModuleCatEquivalence.functor.Additive := by
  dsimp only [fgModuleCatEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

instance fgModuleCatEquivalence_inverse_additive (e : MoritaEquivalence R₀ A B) :
    e.fgModuleCatEquivalence.inverse.Additive := by
  infer_instance

instance fgProjectiveCatEquivalence_additive (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.functor.Additive := by
  dsimp only [fgProjectiveCatEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

instance fgProjectiveCatEquivalence_inverse_additive (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.inverse.Additive := by
  infer_instance

instance fgProjectiveCatEquivalence_isExact (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.functor.IsExact :=
  ExactCategory.isExact_splitSource _

instance fgProjectiveCatEquivalence_inverse_isExact (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.inverse.IsExact :=
  ExactCategory.isExact_splitSource _

instance fgModuleCatEquivalence_isExact (e : MoritaEquivalence R₀ A B)
    [IsNoetherianRing A] [IsNoetherianRing B] :
    e.fgModuleCatEquivalence.functor.IsExact := by
  rw [Functor.isExact_iff_preservesFiniteLimits_and_colimits]
  exact ⟨inferInstance, inferInstance⟩

instance fgModuleCatEquivalence_inverse_isExact (e : MoritaEquivalence R₀ A B)
    [IsNoetherianRing A] [IsNoetherianRing B] :
    e.fgModuleCatEquivalence.inverse.IsExact := by
  rw [Functor.isExact_iff_preservesFiniteLimits_and_colimits]
  exact ⟨inferInstance, inferInstance⟩

end MoritaEquivalence
