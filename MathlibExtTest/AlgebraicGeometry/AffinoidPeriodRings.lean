/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffinoidPeriodRings

/-! Actual completed theta retains the geometric sharp of a Witt
Teichmuller class. Its integral filtration is fixed by the theta kernel.
These tests use the actual coefficient ring, never a free period vector space.
-/

open MathlibExt.AlgebraicGeometry.AffinoidPeriodRings
open MathlibExt.RingTheory.CompleteHuberPairModels

variable (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)
  [D : IntegralPeriodInput p P]

private def compatibleElement (roots : ℕ → P.plus)
    (h : ∀ n, roots (n + 1) ^ p = roots n) : PreTilt P.plus p :=
  ⟨fun n ↦ Ideal.Quotient.mk (Ideal.span {(p : P.plus)}) (roots n),
    fun n ↦ by rw [← map_pow, h]⟩

example (roots : ℕ → P.plus) (h : ∀ n, roots (n + 1) ^ p = roots n) :
    thetaPlusToRing p P (AinfToDeRham p P
      (WittVector.teichmuller p (compatibleElement p P roots h))) =
        (roots 0 : P.ring) := by
  rw [thetaPlus_teichmuller]
  have hp : ∀ n, roots n ^ p ^ n = roots 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn => rw [Nat.pow_succ', pow_mul, h, hn]
  have hs := Perfection.teichmuller_spec (p := p)
    (I := Ideal.span {(p : P.plus)})
    (x := compatibleElement p P roots h) (y := roots 0)
    (fun n ↦ ⟨roots n, rfl, by rw [hp]; rfl⟩)
  exact congrArg (fun a : P.plus ↦ (a : P.ring)) hs

example (a : PreDeRham p P) (h : thetaInvertP p P a = 0) :
    completionUnit p P a ∈ filtration p P 1 := by
  apply completionUnit_mem_filtration
  simpa only [pow_one, RingHom.mem_ker] using h
