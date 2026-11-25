/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Quillen equivalences (Hovey criterion)

A Quillen adjunction `L ⊣ R` is a Quillen equivalence when, for every
cofibrant `X : C` and fibrant `Y : D`, a map `f : L.obj X ⟶ Y` is a weak
equivalence iff its adjunct `adj.homEquiv X Y f : X ⟶ R.obj Y` is.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [ModelCategory C] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C}

/--
A Quillen equivalence is a Quillen adjunction satisfying Hovey's
cofibrant-source / fibrant-target criterion: for cofibrant `X` and
fibrant `Y`, `f : L.obj X ⟶ Y` is a weak equivalence iff
`adj.homEquiv X Y f` is.
-/
class IsQuillenEquivalence (adj : L ⊣ R) : Prop extends IsQuillenAdjunction adj where
  homEquiv_weakEquivalence_iff {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y]
    (f : L.obj X ⟶ Y) : weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f)

namespace IsQuillenEquivalence

variable {adj : L ⊣ R}

/-- Translation of the Hovey criterion to `WeakEquivalence` typeclasses. -/
theorem weakEquivalence_homEquiv_iff [h : IsQuillenEquivalence adj]
    {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y] (f : L.obj X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv X Y f) := by
  simp only [weakEquivalence_iff]
  exact h.homEquiv_weakEquivalence_iff f

/-- The unit of a Quillen equivalence is a weak equivalence at a cofibrant
object whose image under the left adjoint is fibrant. -/
theorem weakEquivalence_unit [IsQuillenEquivalence adj]
    (X : C) [IsCofibrant X] [IsFibrant (L.obj X)] :
    WeakEquivalence (adj.unit.app X) := by
  have hId : WeakEquivalence (𝟙 (L.obj X)) := inferInstance
  have hAdj :=
    (weakEquivalence_homEquiv_iff (adj := adj) (𝟙 (L.obj X))).mp hId
  simpa [Adjunction.homEquiv_unit] using hAdj

/-- The counit of a Quillen equivalence is a weak equivalence at a fibrant
object whose image under the right adjoint is cofibrant. -/
theorem weakEquivalence_counit [IsQuillenEquivalence adj]
    (Y : D) [IsCofibrant (R.obj Y)] [IsFibrant Y] :
    WeakEquivalence (adj.counit.app Y) := by
  have hAdj : adj.homEquiv (R.obj Y) Y (adj.counit.app Y) = 𝟙 (R.obj Y) := by
    apply (adj.homEquiv (R.obj Y) Y).symm.injective
    simp [Adjunction.homEquiv_counit]
  apply (weakEquivalence_homEquiv_iff (adj := adj) (X := R.obj Y) (Y := Y)
    (adj.counit.app Y)).mpr
  rw [hAdj]
  infer_instance

/-- The identity adjunction is a Quillen equivalence. -/
instance id (C : Type u₁) [Category.{v₁} C] [ModelCategory C] :
    IsQuillenEquivalence (Adjunction.id (C := C)) where
  homEquiv_weakEquivalence_iff {X} {Y} _ _ f := by
    have h_eq : (Adjunction.id (C := C)).homEquiv X Y f = f := by
      simp [Adjunction.homEquiv]
    rw [h_eq]

/-- Composition of Quillen equivalences is a Quillen equivalence. -/
instance comp {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L' : D ⥤ E} {R' : E ⥤ D} (adj' : L' ⊣ R')
    [h : IsQuillenEquivalence adj] [h' : IsQuillenEquivalence adj'] :
    IsQuillenEquivalence (adj.comp adj') where
  homEquiv_weakEquivalence_iff {X Z} [IsCofibrant X] [IsFibrant Z]
      (f : L'.obj (L.obj X) ⟶ Z) := by
    have : IsCofibrant (L.obj X) :=
      (IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant inferInstance
    have : IsFibrant (R'.obj Z) :=
      (IsQuillenAdjunction.preservesFibrantObjects (adj := adj')).isFibrant inferInstance
    calc weakEquivalences E f
        ↔ weakEquivalences D (adj'.homEquiv (L.obj X) Z f) :=
          IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := adj') f
      _ ↔ weakEquivalences C (adj.homEquiv X (R'.obj Z) (adj'.homEquiv (L.obj X) Z f)) :=
          IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := adj) _
      _ ↔ weakEquivalences C ((adj.comp adj').homEquiv X Z f) := by
          simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]

end IsQuillenEquivalence

end CategoryTheory.Adjunction
