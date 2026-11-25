/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
import Mathlib.Tactic.NormNum

/-! On the actual integer delta ring, phi is the identity. The first
Nygaard ideal for (2) contains2 and excludes1; the zeroth is the whole
ring. No universal-prism/completion provider is assumed in these tests.
-/

open MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
open MathlibExt.RingTheory

example : (2 : ℤ) ∈ absoluteNygaard 2 ℤ (Ideal.span {(2 : ℤ)}) 1 := by
  change DeltaRing.frobenius 2 ℤ 2 ∈ Ideal.span {(2 : ℤ)} ^ 1
  rw [DeltaRing.frobenius_int, RingHom.id_apply, pow_one]
  exact Ideal.subset_span (by simp)

example : (1 : ℤ) ∉ absoluteNygaard 2 ℤ (Ideal.span {(2 : ℤ)}) 1 := by
  change ¬ DeltaRing.frobenius 2 ℤ 1 ∈ Ideal.span {(2 : ℤ)} ^ 1
  rw [map_one, pow_one, Ideal.mem_span_singleton]
  norm_num

example : absoluteNygaard 2 ℤ (Ideal.span {(2 : ℤ)}) 0 = ⊤ := by
  simp [absoluteNygaard]
