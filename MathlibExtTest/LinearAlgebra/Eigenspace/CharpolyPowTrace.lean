/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.LinearAlgebra.Eigenspace.CharpolyPowTrace
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

private theorem exactSource {L : Type*} [Field L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E]
    [IsAlgClosed E] (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n)) :=
  LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow E T n

-- Higher-universe consumer: the algebraically closed field lives in `Type 1`.
example (E : Type 1) [Field E] [Algebra ℂ E] [IsAlgClosed E]
    (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) (n : ℕ) :
    (((T.charpoly).map (algebraMap ℂ E)).roots.map (fun z => z ^ n)).sum =
      algebraMap ℂ E (LinearMap.trace ℂ (Fin 2 → ℂ) (T ^ n)) :=
  LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow E T n

-- The case `n = 1` over `ℂ` itself: the sum of the roots of the
-- characteristic polynomial is the trace.
example (T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) :
    ((T.charpoly).roots.map (fun z => z)).sum = LinearMap.trace ℂ (Fin 2 → ℂ) T := by
  have h := LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow ℂ T 1
  simpa using h
