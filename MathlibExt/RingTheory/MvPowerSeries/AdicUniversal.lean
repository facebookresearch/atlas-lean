/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_algHom_apply_X_eq.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_algHom_apply_X_eq.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import MathlibExt.RingTheory.MvPowerSeries.SpecialFibreCoordinates

/-!
# Algebra maps from multivariate power series into adically complete rings

Let `σ` be a finite index type, `𝒪` a commutative ring, and `A` a commutative `𝒪`-algebra that
is adically complete for an ideal `I` of `A`. For any elements `a i ∈ I` there exists an
`𝒪`-algebra map `MvPowerSeries σ 𝒪 →ₐ[𝒪] A` sending each variable `X i` to `a i`
(`MvPowerSeries.exists_algHom_apply_X_eq`). Only existence is stated: no uniqueness or
extensionality result for such maps is proved here. The proof takes the `I`-adic evaluation
`MvPowerSeries.adicEvalAlgHom`, which is Mathlib's `MvPowerSeries.aeval` for the `I`-adic
topology; callers that need a specific map can use it directly.
-/

universe u v w

namespace MvPowerSeries

/-- **Existence of algebra maps from multivariate power series into adically complete rings.**
Let `σ` be finite, `𝒪` a commutative ring, and `A` a commutative `𝒪`-algebra that is adically
complete for an ideal `I` of `A`. Then for any elements `a i ∈ I` there exists an `𝒪`-algebra
map `MvPowerSeries σ 𝒪 →ₐ[𝒪] A` sending each variable `X i` to `a i`. This states existence
only, not uniqueness; one such map is `MvPowerSeries.adicEvalAlgHom`. -/
public theorem exists_algHom_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w}
    [Finite σ] [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A]
    (a : σ → A) (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  ⟨adicEvalAlgHom I fun i => Ideal.le_radical (ha i), fun i => by
    rw [coe_adicEvalAlgHom, adicEval_X]⟩

end MvPowerSeries
