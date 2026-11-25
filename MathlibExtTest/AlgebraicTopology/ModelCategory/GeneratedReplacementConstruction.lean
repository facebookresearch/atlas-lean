/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
import Batteries.Tactic.Lint

/-! # Generic replacements retain the actual original factor factories and every map -/

public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open GeneratedFunctorialReplacements

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

example : (replacementsOfFactors Fc Ff).cofibrantFactor = Fc ∧
    (replacementsOfFactors Fc Ff).fibrantFactor = Ff := replacementsOfFactors_factors Fc Ff

example {X Y : C} (f : X ⟶ Y) :
    (replacementsOfFactors Fc Ff).Q.map f =
      Fc.Z.map (Arrow.homMk (𝟙 (⊥_ C)) f (by simp [initialMap])) :=
  replacementsOfFactors_Q_map Fc Ff f

example {X Y : C} (f : X ⟶ Y) :
    (replacementsOfFactors Fc Ff).R.map f =
      Ff.Z.map (Arrow.homMk f (𝟙 (⊤_ C)) (by simp [terminalMap])) :=
  replacementsOfFactors_R_map Fc Ff f

example (X : C) : IsCofibrant ((replacementsOfFactors Fc Ff).Q.obj X) :=
  (replacementsOfFactors Fc Ff).q_cofibrant X
example (X : C) : IsFibrant ((replacementsOfFactors Fc Ff).R.obj X) :=
  (replacementsOfFactors Fc Ff).r_fibrant X

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((replacementsOfFactors Fc Ff).Q.map f) :=
  (replacementsOfFactors Fc Ff).q_map_weak f hf
example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((replacementsOfFactors Fc Ff).R.map f) :=
  (replacementsOfFactors Fc Ff).r_map_weak f hf

#print axioms replacementsOfFactors
#print axioms replacementsOfFactors_factors
#print axioms replacementsOfFactors_Q_map
#print axioms replacementsOfFactors_R_map
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
