/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.ComplexIntegers
import Mathlib.RingTheory.Perfectoid.BDeRham

/-! Tests for the `p`-adic completeness of `𝓞_ℂ_[p]`: the instances that Mathlib's tilt, Fontaine's
map `θ` and `BDeRhamPlus` need are found, and the norm description of `(p) ^ n` behaves as
expected at the boundary cases. -/

open Ideal

variable (p : ℕ) [Fact p.Prime]

example : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := inferInstance

example : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := inferInstance

example : IsHausdorff (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := inferInstance

-- The instances make Mathlib's period ring for `𝓞_ℂ_[p]` available.
noncomputable example : CommRing (BDeRhamPlus 𝓞_ℂ_[p] p) := inferInstance

example : (p : ℂ_[p]) ∈ 𝓞_ℂ_[p] :=
  (PadicComplexInt.mem_iff_norm_le_one p _).mpr (PadicComplex.norm_p_lt_one p).le

-- `p ^ n` lies in `(p) ^ n`, on the boundary of the norm criterion.
example (n : ℕ) : (p : 𝓞_ℂ_[p]) ^ n ∈ span {(p : 𝓞_ℂ_[p])} ^ n :=
  (PadicComplexInt.mem_span_pow_iff p _ n).mpr (by
    push_cast
    rw [norm_pow])

-- `1` does not lie in `(p)`: its norm exceeds `‖p‖`.
example : (1 : 𝓞_ℂ_[p]) ∉ span {(p : 𝓞_ℂ_[p])} ^ 1 := by
  rw [PadicComplexInt.mem_span_pow_iff, pow_one]
  push_cast
  rw [norm_one, not_le]
  exact PadicComplex.norm_p_lt_one p

example : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := PadicComplex.norm_p p
