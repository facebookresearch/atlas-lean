/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Linear isometry norm and inner-product preservation checks

Concrete consumers of the canonical Mathlib API
`LinearIsometry.norm_map` / `LinearIsometry.inner_map_map` and
`LinearIsometryEquiv.norm_map` / `LinearIsometryEquiv.inner_map_map`:
a linear isometry on a real Euclidean space preserves norm and inner
product. No new theorem is introduced here: M02's minimum milestone
is verbatim those Mathlib lemmas, so this test-only file is the
deliverable.

## i. Overview

The generic example covers every linear isometry `R`; the identity
(`LinearIsometryEquiv.refl`) and point reflection
(`LinearIsometryEquiv.neg`) examples exercise it on concrete
isometries, with the zero vector distinguished from a unit vector
on `ℝ` and a numeric norm/inner-product check on `ℝ`. A singular
matrix is excluded by construction: an isometry is by definition
injective, so no inverse claim is made.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Generic isometry
- B. Identity and reflection
- C. Zero versus unit, and a numeric check on `ℝ`

## iv. References

- `LinearIsometry.norm_map`, `LinearIsometry.inner_map_map`,
  `LinearIsometryEquiv.norm_map`, `LinearIsometryEquiv.inner_map_map`
  (Mathlib).
-/

/-- Every linear isometry preserves norm and inner product. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →ₗᵢ[ℝ] E) (u v : E) :
    ‖R u‖ = ‖u‖ ∧ @inner ℝ E _ (R u) (R v) = @inner ℝ E _ u v :=
  ⟨R.norm_map u, R.inner_map_map u v⟩

/-- Every linear isometry equivalence preserves norm and inner product. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E ≃ₗᵢ[ℝ] E) (u v : E) :
    ‖R u‖ = ‖u‖ ∧ @inner ℝ E _ (R u) (R v) = @inner ℝ E _ u v :=
  ⟨R.norm_map u, R.inner_map_map u v⟩

/-- Identity isometry on `ℝ`: norm `3`, inner product `2 * 3 = 6`. -/
example : ‖(LinearIsometryEquiv.refl ℝ ℝ) (3 : ℝ)‖ = 3 ∧
    @inner ℝ ℝ _ ((LinearIsometryEquiv.refl ℝ ℝ) 2)
      ((LinearIsometryEquiv.refl ℝ ℝ) 3) = 6 := by
  refine ⟨?_, ?_⟩
  · rw [(LinearIsometryEquiv.refl ℝ ℝ).norm_map]
    simp
  · rw [(LinearIsometryEquiv.refl ℝ ℝ).inner_map_map]
    simp only [RCLike.inner_apply]
    norm_num

/-- Point reflection `neg` preserves norm and inner product, and sends
`u` to `-u`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    ‖(LinearIsometryEquiv.neg ℝ (E := E)) u‖ = ‖u‖ ∧
    @inner ℝ E _ ((LinearIsometryEquiv.neg ℝ (E := E)) u)
      ((LinearIsometryEquiv.neg ℝ (E := E)) v) = @inner ℝ E _ u v ∧
    (LinearIsometryEquiv.neg ℝ (E := E)) u = -u :=
  ⟨(LinearIsometryEquiv.neg ℝ).norm_map u,
   (LinearIsometryEquiv.neg ℝ).inner_map_map u v, rfl⟩

/-- Zero vector versus unit vector under the identity on `ℝ`. -/
example : ‖(LinearIsometryEquiv.refl ℝ ℝ) (0 : ℝ)‖ = 0 ∧
    ‖(LinearIsometryEquiv.refl ℝ ℝ) (1 : ℝ)‖ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [(LinearIsometryEquiv.refl ℝ ℝ).norm_map]
    simp
  · rw [(LinearIsometryEquiv.refl ℝ ℝ).norm_map]
    simp
