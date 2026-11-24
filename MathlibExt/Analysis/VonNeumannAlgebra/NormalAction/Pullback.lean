/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Pullback of actual normal actions

A continuous group homomorphism pulls back the same original normal star
automorphisms and inverse predual orbits. Their norm continuity is composed
with the actual source homomorphism. No normal map or equivalence is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uD uH

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {D : Type uD} [Group D] [TopologicalSpace D]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Pull back the same actual normal action along a continuous group homomorphism. -/
def comp (β : NormalAction D M) (f : G →ₜ* D) : NormalAction G M where
  toMonoidHom := β.toMonoidHom.comp f.toMonoidHom
  continuous_predual_orbit φ := (β.continuous_predual_orbit φ).comp f.continuous

/-- Pullback keeps the exact original normal automorphism at every source group element. -/
@[simp]
theorem comp_apply (β : NormalAction D M) (f : G →ₜ* D) (g : G) :
    comp β f g = β (f g) :=
  rfl

end

end VonNeumannAlgebra.NormalAction
