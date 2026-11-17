/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import MathlibExt.Combinatorics.Additive.Convolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Causal finite convolution

For sequences `f g : ℕ → R`, the causal convolution `causalConv`
is the control-theory name for the canonical sum convolution
`AdditiveCombinatorics.sumConv`, defined by unfolding to it; the
explicit finite formula is
`(causalConv f g) n = ∑ k ∈ range (n + 1), f k * g (n - k)`
(`causalConv_apply`): the output at time `n` depends only on input
values at times `≤ n`, and every value is a finite sum, so no
topology or summability side condition is needed. It agrees with
Mathlib's generic discrete convolution
`DiscreteConvolution.addRingConvolution` specialized to `ℕ` (the
`tsum` there is finite on `ℕ`), has the unit sample
`Pi.single 0 1` as a two-sided identity, and is commutative and
associative under the usual hypotheses on the values.
-/

@[expose] public section

namespace ControlTheory

/-- Causal finite convolution of natural-time sequences: the
control-theory name for the canonical sum convolution
`AdditiveCombinatorics.sumConv`, defined by unfolding to it
(a plain definition, not an abbreviation, so that the `@[simp]`
range formula below cannot fire on bare `sumConv` goals). The
output at time `n` depends only on input values at times `≤ n`,
and every value is a finite sum, so no topology or summability
side condition is needed. -/
def causalConv {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) :
    ℕ → R :=
  AdditiveCombinatorics.sumConv f g

@[simp]
theorem causalConv_apply {R : Type*} [NonUnitalNonAssocSemiring R]
    (f g : ℕ → R) (n : ℕ) :
    causalConv f g n = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
  exact AdditiveCombinatorics.sumConv_apply f g n

/-- Agreement with Mathlib's generic discrete convolution
(`DiscreteConvolution.addRingConvolution`, the additive-index
ring convolution, specialized to `ℕ`): on `ℕ` the generic
`tsum`-based convolution is the finite causal sum. -/
theorem causalConv_eq_addRingConvolution {R : Type*}
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (f g : ℕ → R) :
    causalConv f g = DiscreteConvolution.addRingConvolution f g := by
  ext n
  simp only [causalConv_apply,
    DiscreteConvolution.addRingConvolution_eq_sum_antidiagonal]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => f k * g l) n).symm

@[simp]
theorem zero_causalConv {R : Type*} [NonUnitalNonAssocSemiring R]
    (g : ℕ → R) : causalConv 0 g = 0 := by
  exact AdditiveCombinatorics.zero_sumConv g

@[simp]
theorem causalConv_zero {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : ℕ → R) : causalConv f 0 = 0 := by
  exact AdditiveCombinatorics.sumConv_zero f

/-- Unit-sample identity, left: convolution with the unit sample
`Pi.single 0 1` (the sequence that is `1` at time `0` and `0`
elsewhere) is the identity. -/
theorem single_zero_causalConv {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : causalConv (Pi.single 0 1) f = f := by
  exact AdditiveCombinatorics.single_zero_sumConv f

/-- Unit-sample identity, right. -/
theorem causalConv_single_zero {R : Type*} [NonAssocSemiring R]
    (f : ℕ → R) : causalConv f (Pi.single 0 1) = f := by
  exact AdditiveCombinatorics.sumConv_single_zero f

/-- Causal convolution is commutative when the value multiplication
is. -/
theorem causalConv_comm {R : Type*} [NonUnitalNonAssocCommSemiring R]
    (f g : ℕ → R) : causalConv f g = causalConv g f := by
  exact AdditiveCombinatorics.sumConv_comm f g

/-- Causal convolution is associative over any (not necessarily
unital) semiring: the proof uses only distributivity, additive
commutativity, and associativity of the value multiplication. -/
theorem causalConv_assoc {R : Type*} [NonUnitalSemiring R] (f g h : ℕ → R) :
    causalConv (causalConv f g) h = causalConv f (causalConv g h) := by
  exact AdditiveCombinatorics.sumConv_assoc f g h

end ControlTheory
