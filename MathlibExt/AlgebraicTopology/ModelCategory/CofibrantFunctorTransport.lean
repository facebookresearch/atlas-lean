/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Exact cofibration-class functor transport

A fixed full functor preserving initial objects carries cofibrant objects
under an exact inverse-image cofibration-class equality. The source and
target category, initial and cofibration dictionaries remain explicit.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
namespace HomotopicalAlgebra.NativeCofiberTransport
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [CategoryWithCofibrations C] [HasInitial C]
 {D : Type uD} [Category.{vD} D] [CategoryWithCofibrations D] [HasInitial D]
 [(cofibrations D).RespectsIso]
/-- A supplied exact inverse-image cofibration class preserves source cofibrancy under the full functor. -/
theorem map_isCofibrant (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F]
 (hCof : cofibrations C = (cofibrations D).inverseImage F) (X : C) (hX : IsCofibrant X) :
 IsCofibrant (F.obj X) := by
 let _ : IsCofibrant X := hX
 have h : cofibrations C (initial.to X) := mem_cofibrations _
 rw [hCof] at h
 let _ : Cofibration (F.map (initial.to X)) := (cofibration_iff _).mpr h
 exact (isCofibrant_iff_of_isInitial (F.map (initial.to X))
  (initialIsInitial.isInitialObj F _)).mpr inferInstance
end HomotopicalAlgebra.NativeCofiberTransport
