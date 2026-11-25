/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original provider credits: @toskua, Avocado.
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal

/-!
# Restriction of internal Homs along cofibrations

In a cartesian closed monoidal model category, precomposition along a
cofibration is a fibration when the original target is fibrant.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [CartesianMonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

/-- In the existing cartesian closed model structure, restriction of
internal Homs along a cofibration is a fibration against a fibrant target.
The map is the ORIGINAL precomposition map, through the existing terminal
pullback-Hom Iso, not a replaced path-space comparison. -/
public theorem fibration_pre_app_of_cofibration
    {A B Z : C} (i : A ⟶ B) [Cofibration i] [IsFibrant Z] :
    Fibration ((MonoidalClosed.pre i).app Z) := by
  have hi : cofibrations C i := (cofibration_iff i).mp inferInstance
  have hz : fibrations C (terminal.from Z) := (fibration_iff _).mp inferInstance
  have h := IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.2
    i (terminal.from Z) hi hz
  let e := MonoidalCategory.Arrow.PullbackHom.isTerminalIso
    (Arrow.mk i) terminalIsTerminal (W := Z)
  exact (fibration_iff _).mpr (((fibrations C).arrow_mk_iso_iff e).mp h)

end HomotopicalAlgebra
