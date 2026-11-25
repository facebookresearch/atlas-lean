/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_ModularCurve_UVCrossingModel_U_ne_V.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.UVCrossingModel

@[expose] public section

open ModularCurve ModularCurve.UVCrossingModel in
private theorem exactSource {W : Type*} [CommRing W] (π : W)
    [Nontrivial (W ⧸ Ideal.span {π})] : U π ≠ V π :=
  ModularCurve.UVCrossingModel.U_ne_V π

-- A concrete coefficient ring: modulo the prime `3` in `ℤ`.
example : ModularCurve.UVCrossingModel.U (3 : ℤ) ≠
    ModularCurve.UVCrossingModel.V (3 : ℤ) := by
  haveI : Nontrivial (ℤ ⧸ Ideal.span {(3 : ℤ)}) := by
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    have h1 : (1 : ℤ) ∈ Ideal.span {(3 : ℤ)} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h.symm)
    rw [Ideal.mem_span_singleton] at h1
    norm_num at h1
  exact ModularCurve.UVCrossingModel.U_ne_V (3 : ℤ)

-- The constant map agrees with the constant coordinate.
example {W : Type*} [CommRing W] (π w : W) :
    ModularCurve.UVCrossingModel.constHom π w =
      ModularCurve.UVCrossingModel.const π w :=
  ModularCurve.UVCrossingModel.constHom_apply π w

-- Boundary: when `π = 1` the coefficient quotient collapses, so the
-- nontriviality hypothesis excludes this degenerate case.
example : (1 : ℤ ⧸ Ideal.span {(1 : ℤ)}) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
