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

public import MathlibExt.KTheory.Milnor.SteinbergIdealProj
public import MathlibExt.KTheory.Milnor.ClassicalDegree

/-!
# Degreewise Steinberg ideal and insertion span

The degree-`n` part of the Steinberg ideal coincides with the `ℤ`-span of
pure degree-`n` tensors containing a Steinberg adjacent pair.

## Main results
* `mem_steinbergDegreeSpan_of_mem_steinbergIdeal_of_mem_degree`
* `steinbergDegreeSubmodule_le_steinbergDegreeSpanInDegree`
* `steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree`
* `steinbergDegreeSpanInDegree_eq_ker`
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

namespace TensorRing

/-- An element in `steinbergIdeal F` and `TensorRing.degree F n` lies in
`steinbergDegreeSpan F n`. -/
theorem mem_steinbergDegreeSpan_of_mem_steinbergIdeal_of_mem_degree
    {n : ℕ} {x : TensorRing F}
    (hxI : x ∈ steinbergIdeal F)
    (hxD : x ∈ TensorRing.degree F n) :
    x ∈ steinbergDegreeSpan F n := by
  have h_mem : proj F n x ∈ steinbergDegreeSpan F n :=
    proj_mem_steinbergDegreeSpan_of_mem_steinbergIdeal (F := F) hxI n
  have h_eq : proj F n x = x :=
    GradedAlgebra.proj_eq_self (𝒜 := degree F) hxD
  rwa [h_eq] at h_mem

end TensorRing

open TensorRing

/-- The explicit Steinberg submodule of `TensorRing.degree F n` defined by
ideal membership is contained in the explicit insertion span viewed in degree. -/
theorem steinbergDegreeSubmodule_le_steinbergDegreeSpanInDegree (n : ℕ) :
    steinbergDegreeSubmodule F n ≤ steinbergDegreeSpanInDegree F n := by
  intro x hx
  have hxI : (x : TensorRing F) ∈ steinbergIdeal F :=
    (mem_steinbergDegreeSubmodule_iff (F := F) (n := n) (x := x)).mp hx
  have hxD : (x : TensorRing F) ∈ TensorRing.degree F n := x.2
  dsimp [steinbergDegreeSpanInDegree]
  rw [Submodule.mem_comap]
  exact mem_steinbergDegreeSpan_of_mem_steinbergIdeal_of_mem_degree F hxI hxD

/-- Equality of the degreewise ideal intersection with the explicit insertion span. -/
theorem steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree (n : ℕ) :
    steinbergDegreeSubmodule F n = steinbergDegreeSpanInDegree F n := by
  apply le_antisymm
  · exact steinbergDegreeSubmodule_le_steinbergDegreeSpanInDegree F n
  · have h_le_ker : steinbergDegreeSpanInDegree F n ≤
        LinearMap.ker (MilnorKRing.degreeLinear F n) :=
      steinbergDegreeSpanInDegree_le_ker F n
    have h_ker_eq : LinearMap.ker (MilnorKRing.degreeLinear F n) =
        steinbergDegreeSubmodule F n :=
      (steinbergDegreeSubmodule_eq_ker F n).symm
    exact le_trans h_le_ker (le_of_eq h_ker_eq)

/-- The explicit insertion span equals the kernel of the degreewise projection. -/
theorem steinbergDegreeSpanInDegree_eq_ker (n : ℕ) :
    steinbergDegreeSpanInDegree F n =
      LinearMap.ker (MilnorKRing.degreeLinear F n) := by
  calc steinbergDegreeSpanInDegree F n
      = steinbergDegreeSubmodule F n :=
        (steinbergDegreeSubmodule_eq_steinbergDegreeSpanInDegree F n).symm
    _ = LinearMap.ker (MilnorK.mk F n) :=
        steinbergDegreeSubmodule_eq_ker F n
    _ = LinearMap.ker (MilnorKRing.degreeLinear F n) := rfl

end MilnorK
