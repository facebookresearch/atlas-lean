/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Enveloping evaluation and reduction modulo two

The integer Lie generator is evaluated at two over the integers and at zero
modulo two. Induction on the enveloping algebra proves coefficient coherence.
Integer evaluation also detects that the generator is nonzero, without PBW.
-/

noncomputable section
namespace EnvelopingInductionTests

attribute [local instance] LieRing.ofAssociativeRing

private def twice : ℤ →ₗ⁅ℤ⁆ ℤ :=
  { ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) with
    map_lie' := by
      intro x y
      simp [LieRing.of_associative_ring_bracket, mul_comm] }

private theorem twice_apply (n : ℤ) : twice n = 2 * n := by
  change ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) n = 2 * n
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
private def evalTwice : UniversalEnvelopingAlgebra ℤ ℤ →ₐ[ℤ] ℤ :=
  UniversalEnvelopingAlgebra.lift ℤ twice
private def evalZero : UniversalEnvelopingAlgebra ℤ ℤ →ₐ[ℤ] ZMod 2 :=
  UniversalEnvelopingAlgebra.lift ℤ (0 : ℤ →ₗ⁅ℤ⁆ ZMod 2)

example (x : UniversalEnvelopingAlgebra ℤ ℤ) :
    evalZero x = (Algebra.ofId ℤ (ZMod 2)) (evalTwice x) := by
  induction x using UniversalEnvelopingAlgebra.induction ℤ ℤ with
  | algebraMap r => simp [evalZero, evalTwice, AlgHom.commutes]
  | ι n =>
    norm_num [evalZero, evalTwice, UniversalEnvelopingAlgebra.lift_ι_apply,
      twice_apply, map_mul]
    exact Or.inl (by decide)
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

example : UniversalEnvelopingAlgebra.ι ℤ (1 : ℤ) ≠ 0 := by
  intro h
  have he := congrArg evalTwice h
  norm_num [evalTwice, UniversalEnvelopingAlgebra.lift_ι_apply,
    twice_apply] at he
end EnvelopingInductionTests
