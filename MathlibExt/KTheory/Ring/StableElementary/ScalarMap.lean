/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarMap

/-!
# Stable elementary subgroup preservation by coefficient maps

The actual cross-universe stable matrix map sends each finite elementary
representative to the same elementary matrix with its coefficient mapped.
The original generator closure therefore maps into the original target
stable elementary subgroup, without any comparison or preservation witness.
-/

namespace AlgebraicKTheory.StableGL

universe uR uS

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual stable coefficient map preserves the original elementary subgroup. -/
public theorem scalarMap_mem_stableElementarySubgroup (f : R →+* S)
    {x : StableGL R} (hx : x ∈ stableElementarySubgroup R) :
    scalarMap f x ∈ stableElementarySubgroup S := by
  have hclosure : stableElementarySubgroup R ≤
      (stableElementarySubgroup S).comap (scalarMap f) := by
    change Subgroup.closure (stableElementarySet R) ≤ _
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨n, i, j, hij, a, rfl⟩ := hy
    change scalarMap f (StableGL.of
      (Matrix.GeneralLinearGroup.elementary i j hij a)) ∈ stableElementarySubgroup S
    rw [scalarMap_of, Matrix.GeneralLinearGroup.mapRingHom_elementary]
    exact stableElementary_mem (hij := hij)
  exact (Subgroup.mem_comap).mp (hclosure hx)

end AlgebraicKTheory.StableGL
