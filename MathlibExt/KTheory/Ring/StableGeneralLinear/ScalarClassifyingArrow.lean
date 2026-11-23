/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarClassifyingSource

/-!
# The normalized stable arrow under the actual coefficient functor

The original edge label op(g⁻¹) maps to op((scalarMap f g)⁻¹).
Both original source endpoints are explicit. The two coefficient and
morphism universes remain independent; no realization or comparison map
is used to define the coefficient functor.
-/

open CategoryTheory

namespace AlgebraicKTheory.StableGL

universe uR uS

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

/-- The original normalized arrow maps to the inverse of the actual scalar image. -/
public theorem classifyingCategoryScalarMap_map_normalized
    (f : R →+* S) (g : StableGL R) :
    (classifyingCategoryScalarMap f).map
        (X := SingleObj.star (StableGL R)ᵐᵒᵖ)
        (Y := SingleObj.star (StableGL R)ᵐᵒᵖ)
        (MulOpposite.op (g⁻¹)) =
      MulOpposite.op ((scalarMap f g)⁻¹) := by
  rw [classifyingCategoryScalarMap_map]
  simp only [MulOpposite.unop_op, map_inv]

end AlgebraicKTheory.StableGL
