/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_finrankAlong_x1LevelInclBar_eq_
  finrankAlong_x1LevelSubstBar.lean`
and
`P2M/Sol/S_ModularCurve_finrankAlong_x1LevelInclBar_eq_
  finrankAlong_x1LevelSubstBar.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

namespace AlgebraicCurve

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

/-- The degree of a field homomorphism, viewed along the homomorphism:
the dimension of the target field over the source field, where the
source acts through the homomorphism. As with `Module.finrank`, it is `0`
when the target is infinite-dimensional over the source; `finrankAlong_pos_iff`
and `finrankAlong_ne_zero_iff` characterize the finite case. -/
noncomputable def finrankAlong (φ : F →ₐ[K] F') : ℕ :=
  letI := φ.toRingHom.toAlgebra
  Module.finrank F F'

/-- The degree along a homomorphism is positive exactly when the target is
finite over the source acting through the homomorphism. -/
theorem finrankAlong_pos_iff (φ : F →ₐ[K] F') : 0 < finrankAlong φ ↔ φ.Finite := by
  let := φ.toRingHom.toAlgebra
  rw [finrankAlong, AlgHom.Finite, RingHom.Finite]
  exact ⟨fun h ↦ Module.finite_of_finrank_pos h, fun _ ↦ Module.finrank_pos⟩

/-- The degree along a homomorphism is nonzero exactly when the target is
finite over the source acting through the homomorphism; an infinite
extension has degree `0`. -/
theorem finrankAlong_ne_zero_iff (φ : F →ₐ[K] F') : finrankAlong φ ≠ 0 ↔ φ.Finite := by
  rw [← finrankAlong_pos_iff, Nat.pos_iff_ne_zero]

/-- The degree along a composite is the product of the degrees. -/
theorem finrankAlong_comp (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') :
    finrankAlong (χ.comp φ) = finrankAlong φ * finrankAlong χ := by
  let := φ.toRingHom.toAlgebra
  let := χ.toRingHom.toAlgebra
  let := (χ.comp φ).toRingHom.toAlgebra
  have h : IsScalarTower F F' F'' :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change χ (φ x) = χ (φ x)
      rfl
  exact (Module.finrank_mul_finrank F F' F'').symm

/-- Two homomorphisms that factor through a common homomorphism, with
first factors of equal degree along them, have equal degree. -/
theorem finrankAlong_eq_of_comp_eq_of_finrankAlong_eq
    {M : Type*} [Field M] [Algebra K M]
    (γ : M →ₐ[K] F') (α β : F →ₐ[K] M)
    (h : finrankAlong α = finrankAlong β) :
    finrankAlong (γ.comp α) = finrankAlong (γ.comp β) := by
  rw [finrankAlong_comp, finrankAlong_comp, h]

end AlgebraicCurve
