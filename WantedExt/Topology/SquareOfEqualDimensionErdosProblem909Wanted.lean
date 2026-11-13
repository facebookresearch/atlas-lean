/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A separable metric space whose square has the same dimension (Erdős Problem 909)

Erdős Problem 909: let `n ≥ 2`. Is there a space `S` of dimension `n` such that `S²` also has
dimension `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.InductiveDimension.Functions
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

namespace MathlibExt.Topology.SquareOfEqualDimensionErdosProblem909Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #909, https://www.erdosproblems.com/909 (status
PROVED). UnsolvedMath record UM-30007083 (`EP-909`), dataset ulamai/UnsolvedMath v1.8.0.

Space means separable metric space, the setting of classical dimension theory in which the question
was asked (the page's example for `n = 1`, the rational points of Hilbert space, is one), and
dimension is Mathlib's small inductive dimension `smallInductiveDimension`; for separable metric
spaces the small and large inductive dimensions and the covering dimension coincide, so the
statement does not depend on that choice. formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 909: for every `n ≥ 2` there is a separable metric space `S` of dimension `n`
whose square `S × S` also has dimension `n`. Dimension is Mathlib's small inductive dimension
(`smallInductiveDimension`), which for separable metric spaces agrees with the large inductive and
the covering dimension. -/
def squareOfEqualDimension : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (S : Type) (_ : MetricSpace S), TopologicalSpace.SeparableSpace S ∧
    smallInductiveDimension S = n ∧ smallInductiveDimension (S × S) = n

/--
Resolved true: Anderson and Keisler constructed, for every `n`, a separable metric space `S` with
`dim S = dim (S × S) = n` (Erdős space, the rational points of Hilbert space, is the case `n = 1`);
erdosproblems.com/909 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#909, https://www.erdosproblems.com/909 (status PROVED); resolution: R. D. Anderson and J. E.
Keisler, An example in dimension theory, Proc. Amer. Math. Soc. 18 (1967), 709-713,
erdosproblems.com/909: the space of rational points in Hilbert space has the property for n = 1, and
'this was proved for general n by Anderson and Keisler', https://www.erdosproblems.com/909.
-/
public theorem_wanted squareOfEqualDimension_holds : squareOfEqualDimension

end MathlibExt.Topology.SquareOfEqualDimensionErdosProblem909Wanted
