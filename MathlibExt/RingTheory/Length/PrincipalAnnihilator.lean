/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Length.AnnihilatorQuotient
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Finite length from a regular principal annihilator

A finite module over a Noetherian ring of dimension at most one has finite
length when a non-zero-divisor of the ring annihilates the module.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
universe uR uM
namespace Module

/-- Let `R` be a Noetherian commutative ring of Krull dimension at most one,
and `M` a finitely generated `R`-module in an independent universe. If a
non-zero-divisor `a ∈ R` annihilates every element of `M`, then `M` has finite
composition length over `R`. -/
theorem length_ne_top_of_isTorsionBy_nonZeroDivisor
    (R : Type uR) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (M : Type uM) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : R) (ha : a ∈ R⁰) (h : Module.IsTorsionBy R M a) :
    Module.length R M ≠ ⊤ := by
  apply length_ne_top_of_finite_of_ideal_le_annihilator R M (Ideal.span {a})
  · exact (Ideal.span_singleton_le_iff_mem (Module.annihilator R M)).mpr
      ((Module.isTorsionBy_iff_mem_annihilator R M).mp h)
  · exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R ha)

end Module
