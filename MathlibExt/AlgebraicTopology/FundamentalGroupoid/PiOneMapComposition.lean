/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Composition and identity laws for `FundamentalGroup.mapOfEq`

Mathlib defines the homomorphism between fundamental groups induced by a
continuous map at specified basepoints (`FundamentalGroup.mapOfEq`), together
with its pointwise description (`FundamentalGroup.mapOfEq_apply`), but proves
no composition or identity laws for it. This module fills exactly that gap:
both laws follow from the corresponding laws for
`Path.Homotopic.Quotient.map` (`map_comp`, `map_cast`) and
`Path.Homotopic.Quotient.cast` (`cast_cast`, `cast_rfl_rfl`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The identity map induces the identity homomorphism on fundamental groups. -/
@[simp]
theorem mapOfEq_id (x : X) (h : (ContinuousMap.id X) x = x) :
    mapOfEq (ContinuousMap.id X) h = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro p
  apply End.ext
  change (mapOfEq (ContinuousMap.id X) h p).asHom = p.asHom
  rw [mapOfEq_apply]
  obtain ⟨P, hP⟩ := Path.Homotopic.Quotient.mk_surjective p.asHom
  rw [← hP]
  rfl

/-- Homomorphisms induced on fundamental groups compose functorially. -/
theorem mapOfEq_comp {x : X} {y : Y} {z : Z} (f : C(X, Y)) (g : C(Y, Z))
    (h1 : f x = y) (h2 : g y = z) (h : (g.comp f) x = z) :
    mapOfEq (g.comp f) h = (mapOfEq g h2).comp (mapOfEq f h1) := by
  apply MonoidHom.ext
  intro p
  apply End.ext
  simp only [MonoidHom.comp_apply, mapOfEq_apply,
    Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_cast,
    Path.Homotopic.Quotient.cast_cast]

end FundamentalGroup

end
