/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean`
and
`P2M/Sol/S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.AlgebraicGeometry.Curve.AdelicIndex
public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
import MathlibExt.AlgebraicGeometry.Curve.RatFuncGenusExists
import MathlibExt.AlgebraicGeometry.Curve.SeparatingTranscendental

/-!
# Existence of the genus of a curve function field

Let `F` be the function field of a curve over a perfect field `K` (`IsCurveOver K F`) whose
field of constants is `K`. This file proves that `F` has a genus in the sense of Stichtenoth:
there is a place, the Riemann-Roch space `L(0)` is finite-dimensional, and the quantity
`deg D - ℓ(D)` is bounded above and attains its maximum `γ - 1` at some divisor `D₀`.

The proof picks a separating transcendental element `x`, identifies `K(x) ⊆ F` with the
rational function field `RatFunc K`, and applies the corresponding result for finite separable
extensions of `RatFunc K`.

## Main statement

* `AlgebraicCurve.stichtenothGenusExists_of_isCurveOver`
-/

namespace AlgebraicCurve

open IntermediateField

/-- The function field of a curve over a perfect field, with field of constants `K`, has a
genus: `deg D - ℓ(D)` is bounded above and attains its maximum. -/
public theorem stichtenothGenusExists_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F]
    [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (hC : ConstantsAreBase K F) : StichtenothGenusExists K F := by
  classical
  obtain ⟨x, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr with he
  let : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact RationalFunctionField.stichtenothGenusExists K F hC

end AlgebraicCurve
