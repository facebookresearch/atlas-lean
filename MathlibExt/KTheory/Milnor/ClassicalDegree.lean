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

public import MathlibExt.KTheory.Milnor.DegreeSymbols

/-!
# Classical Milnor degree as canonical graded component

`MilnorK F n` is canonically `MilnorKRing.degree F n`, the degree-`n` homogeneous
component of the Milnor K-ring. The projection `MilnorK.mk` is
`MilnorKRing.degreeLinear`, the generic `TwoSidedIdeal.quotientGradeComponent`
specialization. The degreewise Steinberg submodule is defined canonically as the
comap of the restricted Steinberg ideal along `TensorRing.degree F n`, and its
membership and kernel characterizations follow from the generic homogeneous
quotient API `TwoSidedIdeal.quotientGradeComponent_ker` via
`MilnorKRing.degreeLinear_ker`.

`MilnorKPresentation` and the explicit Steinberg insertion-span presentation are
not introduced here; they belong in `ClassicalDegreePresentation` after the
Steinberg-span equality `steinbergDegreeSubmodule = steinbergDegreeSpanInDegree`.

## Main definitions
* `MilnorK.steinbergDegreeSubmodule` – canonical comap description
* `MilnorK F n` – canonical degree-`n` component (`MilnorKRing.degree`)
* `MilnorK.mk` – canonical projection `TensorRing.degree F n →ₗ[ℤ] MilnorK F n`

## Main results
* `MilnorK.mem_steinbergDegreeSubmodule_iff`
* `MilnorK.steinbergDegreeSubmodule_eq_ker`
* `MilnorK.mk_surjective`
* `MilnorK.mk_coe` – component computation via `mkLinear`
-/

@[expose] public section

open TensorAlgebra

namespace MilnorK

variable (F : Type*) [Field F]

/-- Canonical Steinberg submodule as comap of the restricted Steinberg ideal. -/
def steinbergDegreeSubmodule (n : ℕ) : Submodule ℤ (TensorRing.degree F n) :=
  Submodule.comap (TensorRing.degree F n).subtype
    ((steinbergIdeal F).asIdeal.restrictScalars ℤ)

/-- Membership iff underlying tensor lies in the Steinberg ideal. -/
@[simp]
lemma mem_steinbergDegreeSubmodule_iff {n : ℕ} {x : TensorRing.degree F n} :
    x ∈ steinbergDegreeSubmodule F n ↔ (x.1 : TensorRing F) ∈ steinbergIdeal F := by
  simp [steinbergDegreeSubmodule, Submodule.mem_comap, Submodule.restrictScalars_mem,
    TwoSidedIdeal.mem_asIdeal]

/-- Canonical Milnor K-group in degree `n` as homogeneous component. -/
abbrev _root_.MilnorK (n : ℕ) : Type _ :=
  MilnorKRing.degree F n

/-- Canonical projection onto degree `n`, specialization of
`TwoSidedIdeal.quotientGradeComponent`. -/
def mk (n : ℕ) : TensorRing.degree F n →ₗ[ℤ] MilnorK F n :=
  MilnorKRing.degreeLinear F n

/-- Most useful component computation: underlying Milnor ring element is `mkLinear`. -/
@[simp]
lemma mk_coe (n : ℕ) (x : TensorRing.degree F n) :
    (mk F n x : MilnorKRing F) = MilnorKRing.mkLinear F x.1 := rfl

/-- Kernel equals Steinberg submodule, via generic `degreeLinear_ker` API. -/
theorem steinbergDegreeSubmodule_eq_ker (n : ℕ) :
    steinbergDegreeSubmodule F n = LinearMap.ker (mk F n) := by
  unfold steinbergDegreeSubmodule mk
  exact (MilnorKRing.degreeLinear_ker F n).symm

/-- `mk` is surjective onto `MilnorK F n`. -/
lemma mk_surjective (n : ℕ) : Function.Surjective (mk F n) :=
  MilnorKRing.degreeLinear_surjective F n

end MilnorK
