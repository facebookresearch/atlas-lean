/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.CurveModelExists
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! # Tests for the existence of curve models -/

@[expose] public section

open AlgebraicCurve

universe u v

-- `exactSource` consumer with the original binders.
example (K : Type u) (L : Type v) [Field K] [PerfectField K] [Infinite K] [Field L] [Algebra K L]
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L) :
    Nonempty (CurveModel K L) :=
  CurveModel.nonempty_of_perfectField K L hfg

-- The rational function field over an infinite perfect field has a curve model.
example (K : Type u) [Field K] [PerfectField K] [Infinite K] :
    Nonempty (CurveModel K (RatFunc K)) :=
  CurveModel.nonempty_of_perfectField K (RatFunc K)
    ⟨RatFunc.X, RatFunc.transcendental_X, by
      rw [RatFunc.adjoin_X]; exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top⟩

-- The finiteness hypothesis cannot hold for `L = K`: no element of `K` is transcendental.
example (K : Type u) [Field K] :
    ¬ ∃ x : K, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set K)) K :=
  fun ⟨x, hx, _⟩ => hx (isAlgebraic_algebraMap (R := K) (A := K) x)

-- A curve model transports along `K`-isomorphisms of fields.
example (K : Type u) [Field K] {L : Type v} {L' : Type*} [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (e : L' ≃ₐ[K] L) (M : CurveModel K L') :
    (CurveModel.congr e M).C = M.C :=
  rfl

-- The chart ring of `S` is Mathlib's integral closure of `K[S]` in `L`, up to reducible unfolding.
example (K L : Type u) [Field K] [Field L] [Algebra K L] (S : Set L) :
    CurveModel.chartRing K S = (integralClosure (Algebra.adjoin K S) L).restrictScalars K := by
  with_reducible rfl
