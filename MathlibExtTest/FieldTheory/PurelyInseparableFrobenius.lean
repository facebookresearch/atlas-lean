/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.PurelyInseparableFrobenius
import MathlibExt.FieldTheory.FrobeniusSubfieldDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic

@[expose] public section

/-- Consumer with the original binders. -/
private theorem exactSource {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] [IsPurelyInseparable M E] (p : ℕ)
    [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange =
        (iterateFrobenius E p r).fieldRange :=
  Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    p hp

/-- Both conclusions share the exponent: for every `n` with `[E : M] = p ^ n` (Mathlib's
`IsPurelyInseparable.finrank_eq_pow` gives one), the image of `M` is `E^(p^n)`. -/
example {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] [IsPurelyInseparable M E] (p : ℕ)
    [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) {n : ℕ}
    (hn : Module.finrank M E = p ^ n) :
    (algebraMap M E).fieldRange = (iterateFrobenius E p n).fieldRange := by
  obtain ⟨r, hr, hR⟩ :=
    Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
      (M := M) p hp
  obtain rfl : r = n :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (hr.symm.trans hn)
  exact hR

/-- The rational function field `𝔽_p(X)` has degree `p` over its Frobenius image. -/
private theorem finrank_frobenius_ratFunc (p : ℕ) [Fact p.Prime] :
    Module.finrank (frobenius (RatFunc (ZMod p)) p).fieldRange (RatFunc (ZMod p)) = p := by
  have : FiniteDimensional
      (IntermediateField.adjoin (ZMod p) {(RatFunc.X : RatFunc (ZMod p))}) (RatFunc (ZMod p)) := by
    rw [RatFunc.adjoin_X]
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  exact finrank_frobeniusSubfield_eq_of_transcendental (K := ZMod p) p RatFunc.X
    RatFunc.transcendental_X

/-- A concrete field meeting the degree hypothesis: every finite purely inseparable extension
`𝔽_p(X) / M` has degree `p ^ r`, with `M` mapping onto `𝔽_p(X)^(p^r)`. -/
example (p : ℕ) [Fact p.Prime] {M : Type*} [Field M] [Algebra M (RatFunc (ZMod p))]
    [FiniteDimensional M (RatFunc (ZMod p))] [IsPurelyInseparable M (RatFunc (ZMod p))] :
    ∃ r : ℕ, Module.finrank M (RatFunc (ZMod p)) = p ^ r ∧
      (algebraMap M (RatFunc (ZMod p))).fieldRange =
        (iterateFrobenius (RatFunc (ZMod p)) p r).fieldRange :=
  Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    p (finrank_frobenius_ratFunc p)
