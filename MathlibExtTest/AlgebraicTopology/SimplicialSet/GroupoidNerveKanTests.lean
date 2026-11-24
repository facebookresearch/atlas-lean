/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

open CategoryTheory Limits

open scoped Simplicial SSet.modelCategoryQuillen

universe u v

example (G : Type u) [Groupoid.{v} G] :
    SSet.KanComplex (CategoryTheory.nerve G) := by
  fail_if_success infer_instance
  exact SSet.kanComplex_nerve_of_groupoid G

example (G : Type u) [Groupoid.{v} G] {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn (n + 1) i).ι
      (terminal.from (CategoryTheory.nerve G)) := by
  let _ : SSet.KanComplex (CategoryTheory.nerve G) :=
    SSet.kanComplex_nerve_of_groupoid G
  infer_instance

private theorem hasGroupoidNerveFiller (G : Type u) [Groupoid.{v} G]
    {n : ℕ} {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[n + 1] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ phi = f j hj := by
  let _ : SSet.KanComplex (CategoryTheory.nerve G) :=
    SSet.kanComplex_nerve_of_groupoid G
  exact hf.exists_lift_of_kanComplex

section LowDimensionalHornMatrix

variable (G : Type u) [Groupoid.{v} G]

example
    (f : ∀ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), Δ[0] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[1] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 2) (hj : j ≠ (0 : Fin 2)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 2) (_ : j ≠ (1 : Fin 2)), Δ[0] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[1] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 2) (hj : j ≠ (1 : Fin 2)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 3) (_ : j ≠ (1 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (1 : Fin 3)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 3) (_ : j ≠ (2 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (2 : Fin 3)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 4) (_ : j ≠ (0 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (0 : Fin 4)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 4) (_ : j ≠ (1 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (1 : Fin 4)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 4) (_ : j ≠ (2 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (2 : Fin 4)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

example
    (f : ∀ (j : Fin 4) (_ : j ≠ (3 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : SSet.horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (3 : Fin 4)), SSet.stdSimplex.δ j ≫ phi = f j hj :=
  hasGroupoidNerveFiller G f hf

end LowDimensionalHornMatrix

example : SSet.KanComplex
    (CategoryTheory.nerve
      (CategoryTheory.SingleObj (Multiplicative (ZMod 2)))) :=
  SSet.kanComplex_nerve_of_groupoid _

example : ∃ f : CategoryTheory.End
    (CategoryTheory.SingleObj.star (Multiplicative (ZMod 2))), f ≠ 1 := by
  refine ⟨End.of (Multiplicative.ofAdd (1 : ZMod 2)), ?_⟩
  intro h
  have h' := congrArg End.asHom h
  change Multiplicative.ofAdd (1 : ZMod 2) = Multiplicative.ofAdd 0 at h'
  exact one_ne_zero (congrArg Multiplicative.toAdd h')

noncomputable local instance discreteBoolGroupoid : Groupoid (Discrete Bool) :=
  Groupoid.ofIsGroupoid

example : SSet.KanComplex (CategoryTheory.nerve (Discrete Bool)) :=
  SSet.kanComplex_nerve_of_groupoid _

example (f : (Discrete.mk false : Discrete Bool) ⟶ Discrete.mk true) : False := by
  exact Bool.false_ne_true f.eq

noncomputable local instance discreteEmptyGroupoid : Groupoid (Discrete Empty) :=
  Groupoid.ofIsGroupoid

example : SSet.KanComplex (CategoryTheory.nerve (Discrete Empty)) :=
  SSet.kanComplex_nerve_of_groupoid _

noncomputable local instance discreteULiftBoolGroupoid :
    Groupoid.{1} (Discrete (ULift.{1} Bool)) :=
  Groupoid.ofIsGroupoid

example : SSet.KanComplex
    (CategoryTheory.nerve (Discrete (ULift.{1} Bool))) :=
  SSet.kanComplex_nerve_of_groupoid _
